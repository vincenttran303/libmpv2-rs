macro_rules! mpv_cstr_to_str {
    ($cstr: expr) => {
        std::ffi::CStr::from_ptr($cstr)
            .to_str()
            .map_err(Error::from)
    };
}

mod errors;

/// Event handling
pub mod events;
/// Custom protocols (`protocol://$url`) for playback
#[cfg(feature = "protocols")]
pub mod protocol;
/// Custom rendering
#[cfg(feature = "render")]
pub mod render;

pub use self::errors::*;
use self::events::EventContext;
use super::*;

use std::{
    ffi::CString,
    mem::MaybeUninit,
    ops::Deref,
    os::raw as ctype,
    ptr::{self, NonNull},
    rc::Rc,
    sync::atomic::AtomicBool,
};

fn mpv_err<T>(ret: T, err: ctype::c_int) -> Result<T> {
    if err == 0 {
        Ok(ret)
    } else {
        Err(Error::Raw(err))
    }
}

/// This trait describes which types are allowed to be passed to getter mpv APIs.
pub unsafe trait GetData: Sized {
    #[doc(hidden)]
    fn get_from_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(mut fun: F) -> Result<Self> {
        let mut val = MaybeUninit::uninit();
        let _ = fun(val.as_mut_ptr() as *mut _)?;
        Ok(unsafe { val.assume_init() })
    }
    fn get_format() -> Format;
}

/// This trait describes which types are allowed to be passed to setter mpv APIs.
pub unsafe trait SetData: Sized {
    #[doc(hidden)]
    fn call_as_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(
        mut self,
        mut fun: F,
    ) -> Result<T> {
        fun(&mut self as *mut Self as _)
    }
    fn get_format() -> Format;
}

unsafe impl GetData for f64 {
    fn get_format() -> Format {
        Format::Double
    }
}

unsafe impl SetData for f64 {
    fn get_format() -> Format {
        Format::Double
    }
}

unsafe impl GetData for i64 {
    fn get_format() -> Format {
        Format::Int64
    }
}

#[derive(Debug, Clone)]
pub enum MpvNode {
    String(String),
    Flag(bool),
    Int64(i64),
    Double(f64),
    ArrayIter(MpvNodeArrayIter),
    MapIter(MpvNodeMapIter),
    None,
}

impl MpvNode {
    pub fn bool(&self) -> Option<bool> {
        if let MpvNode::Flag(value) = *self {
            Some(value)
        } else {
            None
        }
    }
    pub fn i64(&self) -> Option<i64> {
        if let MpvNode::Int64(value) = *self {
            Some(value)
        } else {
            None
        }
    }
    pub fn f64(&self) -> Option<f64> {
        if let MpvNode::Double(value) = *self {
            Some(value)
        } else {
            None
        }
    }

    pub fn str(&self) -> Option<&str> {
        if let MpvNode::String(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn array(self) -> Option<MpvNodeArrayIter> {
        if let MpvNode::ArrayIter(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn map(self) -> Option<MpvNodeMapIter> {
        if let MpvNode::MapIter(value) = self {
            Some(value)
        } else {
            None
        }
    }
}

impl PartialEq for MpvNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::Flag(l0), Self::Flag(r0)) => l0 == r0,
            (Self::Int64(l0), Self::Int64(r0)) => l0 == r0,
            (Self::Double(l0), Self::Double(r0)) => l0 == r0,
            (Self::ArrayIter(l0), Self::ArrayIter(r0)) => l0.clone().eq(r0.clone()),
            (Self::MapIter(l0), Self::MapIter(r0)) => l0.clone().eq(r0.clone()),
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MpvNodeArrayIter {
    // Reference counted pointer to a parent node so it stays alive long enough.
    //
    // MPV has one big cleanup function that takes a node so store the parent node
    // and force it to stay alive until the reference count hits 0.
    node: Rc<DropWrapper>,
    start: *const libmpv2_sys::mpv_node,
    end: *const libmpv2_sys::mpv_node,
}

impl Iterator for MpvNodeArrayIter {
    type Item = MpvNode;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                let result = ptr::read(self.start);
                let node = SysMpvNode {
                    parent: Rc::clone(&self.node),
                    node: result,
                };
                self.start = self.start.offset(1);
                node.value().ok()
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct MpvNodeMapIter {
    // Reference counted pointer to a parent node so it stays alive long enough.
    //
    // MPV has one big cleanup function that takes a node so store the parent node
    // and force it to stay alive until the reference count hits 0.
    node: Rc<DropWrapper>,
    list: libmpv2_sys::mpv_node_list,
    curr: usize,
}

impl Iterator for MpvNodeMapIter {
    type Item = (String, MpvNode);

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr >= self.list.num.try_into().unwrap() {
            None
        } else {
            let offset = self.curr.try_into().unwrap();
            let (key, value) = unsafe {
                (
                    mpv_cstr_to_str!(*self.list.keys.offset(offset)),
                    *self.list.values.offset(offset),
                )
            };
            self.curr += 1;
            let node = SysMpvNode {
                parent: Rc::clone(&self.node),
                node: value,
            };
            Some((key.unwrap().to_string(), node.value().unwrap()))
        }
    }
}

// Rust doesn't allow implementing external traits directly on external structs so wrapper is required
#[derive(Debug)]
struct DropWrapper(libmpv2_sys::mpv_node);

impl Drop for DropWrapper {
    fn drop(&mut self) {
        unsafe { libmpv2_sys::mpv_free_node_contents(&mut self.0 as *mut libmpv2_sys::mpv_node) };
    }
}

#[derive(Debug)]
struct SysMpvNode {
    // Reference counted pointer to a parent node so it stays alive long enough.
    //
    // MPV has one big cleanup function that takes a node so store the parent node
    // and force it to stay alive until the reference count hits 0.
    parent: Rc<DropWrapper>,
    node: libmpv2_sys::mpv_node,
}

impl SysMpvNode {
    pub fn value(&self) -> Result<MpvNode> {
        let node = self.node;
        Ok(match node.format {
            mpv_format::Flag => MpvNode::Flag(unsafe { node.u.flag } == 1),
            mpv_format::Int64 => MpvNode::Int64(unsafe { node.u.int64 }),
            mpv_format::Double => MpvNode::Double(unsafe { node.u.double_ }),
            mpv_format::String => {
                let text = unsafe { mpv_cstr_to_str!(node.u.string) }?.to_owned();
                MpvNode::String(text)
            }
            mpv_format::Array => {
                let list = unsafe { *node.u.list };
                let iter = MpvNodeArrayIter {
                    node: Rc::clone(&self.parent),
                    start: unsafe { *node.u.list }.values,
                    end: unsafe { list.values.offset(list.num.try_into().unwrap()) },
                };
                return Ok(MpvNode::ArrayIter(iter));
            }

            mpv_format::Map => MpvNode::MapIter(MpvNodeMapIter {
                list: unsafe { *node.u.list },
                curr: 0,
                node: Rc::clone(&self.parent),
            }),
            mpv_format::None => MpvNode::None,
            _ => return Err(Error::Raw(mpv_error::PropertyError)),
        })
    }
}

unsafe impl SetData for i64 {
    fn get_format() -> Format {
        Format::Int64
    }
}

unsafe impl GetData for bool {
    fn get_format() -> Format {
        Format::Flag
    }
}

unsafe impl SetData for bool {
    fn call_as_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(self, mut fun: F) -> Result<T> {
        let mut cpy: i64 = if self { 1 } else { 0 };
        fun(&mut cpy as *mut i64 as *mut _)
    }

    fn get_format() -> Format {
        Format::Flag
    }
}

unsafe impl GetData for MpvNode {
    fn get_from_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(mut fun: F) -> Result<Self> {
        let mut val = MaybeUninit::uninit();
        fun(val.as_mut_ptr() as *mut _)?;
        let sys_node = unsafe { val.assume_init() };
        let node = SysMpvNode {
            parent: Rc::new(DropWrapper(sys_node)),
            node: sys_node,
        };
        node.value()
    }

    fn get_format() -> Format {
        Format::Node
    }
}

unsafe impl GetData for String {
    fn get_from_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(mut fun: F) -> Result<String> {
        let ptr = &mut ptr::null();
        fun(ptr as *mut *const ctype::c_char as _)?;

        let ret = unsafe { mpv_cstr_to_str!(*ptr) }?.to_owned();
        unsafe { libmpv2_sys::mpv_free(*ptr as *mut _) };
        Ok(ret)
    }

    fn get_format() -> Format {
        Format::String
    }
}

unsafe impl SetData for String {
    fn call_as_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(self, mut fun: F) -> Result<T> {
        let string = CString::new(self)?;
        fun((&mut string.as_ptr()) as *mut *const ctype::c_char as *mut _)
    }

    fn get_format() -> Format {
        Format::String
    }
}

/// Wrapper around an `&str` returned by mpv, that properly deallocates it with mpv's allocator.
#[derive(Debug, Hash, Eq, PartialEq)]
pub struct MpvStr<'a>(&'a str);
impl<'a> Deref for MpvStr<'a> {
    type Target = str;

    fn deref(&self) -> &str {
        self.0
    }
}
impl<'a> Drop for MpvStr<'a> {
    fn drop(&mut self) {
        unsafe { libmpv2_sys::mpv_free(self.0.as_ptr() as *mut u8 as _) };
    }
}

unsafe impl<'a> GetData for MpvStr<'a> {
    fn get_from_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(
        mut fun: F,
    ) -> Result<MpvStr<'a>> {
        let ptr = &mut ptr::null();
        let _ = fun(ptr as *mut *const ctype::c_char as _)?;

        Ok(MpvStr(unsafe { mpv_cstr_to_str!(*ptr) }?))
    }

    fn get_format() -> Format {
        Format::String
    }
}

unsafe impl<'a> SetData for &'a str {
    fn call_as_c_void<T, F: FnMut(*mut ctype::c_void) -> Result<T>>(self, mut fun: F) -> Result<T> {
        let string = CString::new(self)?;
        fun((&mut string.as_ptr()) as *mut *const ctype::c_char as *mut _)
    }

    fn get_format() -> Format {
        Format::String
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
/// Subset of `mpv_format` used by the public API.
pub enum Format {
    String,
    Flag,
    Int64,
    Double,
    Node,
}

impl Format {
    fn as_mpv_format(&self) -> MpvFormat {
        match *self {
            Format::String => mpv_format::String,
            Format::Flag => mpv_format::Flag,
            Format::Int64 => mpv_format::Int64,
            Format::Double => mpv_format::Double,
            Format::Node => mpv_format::Node,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
/// How a `File` is inserted into the playlist.
/// See [flags](https://mpv.io/manual/stable/#command-interface-[%3Coptions%3E]]])
pub enum FileState {
    #[default]
    Replace,
    Append,
    AppendPlay,
    InsertNext,
    InsertNextPlay,
    InsertAt,
    InsertAtPlay,
}

impl FileState {
    fn val(&self) -> &str {
        match *self {
            FileState::Replace => "replace",
            FileState::Append => "append",
            FileState::AppendPlay => "append-play",
            FileState::InsertNext => "insert-next",
            FileState::InsertNextPlay => "insert-next-play",
            FileState::InsertAt => "insert-at",
            FileState::InsertAtPlay => "insert-at-play",
        }
    }
}

/// Context passed to the `initializer` of `Mpv::with_initialzer`.
pub struct MpvInitializer {
    ctx: *mut libmpv2_sys::mpv_handle,
}

impl MpvInitializer {
    /// Set the value of a property.
    pub fn set_property<T: SetData>(&self, name: &str, data: T) -> Result<()> {
        let name = CString::new(name)?;
        let format = T::get_format().as_mpv_format() as _;
        data.call_as_c_void(|ptr| {
            mpv_err((), unsafe {
                libmpv2_sys::mpv_set_property(self.ctx, name.as_ptr(), format, ptr)
            })
        })
    }

    /// Set the value of an option
    pub fn set_option<T: SetData>(&self, name: &str, data: T) -> Result<()> {
        let name = CString::new(name)?;
        let format = T::get_format().as_mpv_format() as _;
        data.call_as_c_void(|ptr| {
            mpv_err((), unsafe {
                libmpv2_sys::mpv_set_option(self.ctx, name.as_ptr(), format, ptr)
            })
        })
    }
}

/// The central mpv context.
pub struct Mpv {
    /// The handle to the mpv core
    pub ctx: NonNull<libmpv2_sys::mpv_handle>,
    event_context: EventContext,
    #[cfg(feature = "protocols")]
    protocols_guard: AtomicBool,
}

unsafe impl Send for Mpv {}
unsafe impl Sync for Mpv {}

impl Drop for Mpv {
    fn drop(&mut self) {
        unsafe {
            libmpv2_sys::mpv_terminate_destroy(self.ctx.as_ptr());
        }
    }
}

impl Mpv {
    /// Create a new `Mpv`.
    /// The default settings can be probed by running: `$ mpv --show-profile=libmpv`.
    pub fn new() -> Result<Mpv> {
        Mpv::with_initializer(|_| Ok(()))
    }

    /// Create a new `Mpv`.
    /// The same as `Mpv::new`, but you can set properties before `Mpv` is initialized.
    pub fn with_initializer<F: FnOnce(MpvInitializer) -> Result<()>>(
        initializer: F,
    ) -> Result<Mpv> {
        let api_version = unsafe { libmpv2_sys::mpv_client_api_version() };
        if crate::MPV_CLIENT_API_MAJOR != api_version >> 16 {
            return Err(Error::VersionMismatch {
                linked: crate::MPV_CLIENT_API_VERSION,
                loaded: api_version,
            });
        }

        let ctx = unsafe { libmpv2_sys::mpv_create() };
        if ctx.is_null() {
            return Err(Error::Null);
        }

        initializer(MpvInitializer { ctx })?;
        mpv_err((), unsafe { libmpv2_sys::mpv_initialize(ctx) }).map_err(|err| {
            unsafe { libmpv2_sys::mpv_terminate_destroy(ctx) };
            err
        })?;

        let ctx = unsafe { NonNull::new_unchecked(ctx) };

        Ok(Mpv {
            ctx,
            event_context: EventContext::new(ctx),
            #[cfg(feature = "protocols")]
            protocols_guard: AtomicBool::new(false),
        })
    }

    /// Load a configuration file. The path has to be absolute, and a file.
    pub fn load_config(&self, path: &str) -> Result<()> {
        let file = CString::new(path)?.into_raw();
        let ret = mpv_err((), unsafe {
            libmpv2_sys::mpv_load_config_file(self.ctx.as_ptr(), file)
        });
        unsafe {
            drop(CString::from_raw(file));
        };
        ret
    }

    pub fn event_context(&self) -> &EventContext {
        &self.event_context
    }

    pub fn event_context_mut(&mut self) -> &mut EventContext {
        &mut self.event_context
    }

    /// Send a command to the `Mpv` instance. This uses `mpv_command_string` internally,
    /// so that the syntax is the same as described in the [manual for the input.conf](https://mpv.io/manual/master/#list-of-input-commands).
    ///
    /// Note that you may have to escape strings with `""` when they contain spaces.
    pub fn command(&self, name: &str, args: &[&str]) -> Result<()> {
        let mut cmd = name.to_owned();

        for elem in args {
            cmd.push(' ');
            cmd.push_str(elem);
        }

        let raw = CString::new(cmd)?;
        mpv_err((), unsafe {
            libmpv2_sys::mpv_command_string(self.ctx.as_ptr(), raw.as_ptr())
        })
    }

    /// Set the value of a property.
    pub fn set_property<T: SetData>(&self, name: &str, data: T) -> Result<()> {
        let name = CString::new(name)?;
        let format = T::get_format().as_mpv_format() as _;
        data.call_as_c_void(|ptr| {
            mpv_err((), unsafe {
                libmpv2_sys::mpv_set_property(self.ctx.as_ptr(), name.as_ptr(), format, ptr)
            })
        })
    }

    /// Get the value of a property.
    pub fn get_property<T: GetData>(&self, name: &str) -> Result<T> {
        let name = CString::new(name)?;

        let format = T::get_format().as_mpv_format() as _;
        T::get_from_c_void(|ptr| {
            mpv_err((), unsafe {
                libmpv2_sys::mpv_get_property(self.ctx.as_ptr(), name.as_ptr(), format, ptr)
            })
        })
    }

    /// Internal time in microseconds, this has an arbitrary offset, and will never go backwards.
    ///
    /// This can be called at any time, even if it was stated that no API function should be called.
    pub fn get_internal_time(&self) -> i64 {
        unsafe { libmpv2_sys::mpv_get_time_us(self.ctx.as_ptr()) }
    }

    // --- Convenience property functions ---
    //

    /// Add -or subtract- any value from a property. Over/underflow clamps to max/min.
    pub fn add_property(&self, property: &str, value: isize) -> Result<()> {
        self.command("add", &[property, &format!("{}", value)])
    }

    /// Cycle through a given property. `up` specifies direction. On
    /// overflow, set the property back to the minimum, on underflow set it to the maximum.
    pub fn cycle_property(&self, property: &str, up: bool) -> Result<()> {
        self.command("cycle", &[property, if up { "up" } else { "down" }])
    }

    /// Multiply any property with any positive factor.
    pub fn multiply_property(&self, property: &str, factor: usize) -> Result<()> {
        self.command("multiply", &[property, &format!("{}", factor)])
    }

    /// Pause playback at runtime.
    pub fn pause(&self) -> Result<()> {
        self.set_property("pause", true)
    }

    /// Unpause playback at runtime.
    pub fn unpause(&self) -> Result<()> {
        self.set_property("pause", false)
    }

    // --- Seek functions ---
    //

    /// Seek forward relatively from current position in seconds.
    /// This is less exact than `seek_absolute`, see [mpv manual](https://mpv.io/manual/master/#command-interface-[relative|absolute|absolute-percent|relative-percent|exact|keyframes]).
    pub fn seek_forward(&self, secs: ctype::c_double) -> Result<()> {
        self.command("seek", &[&format!("{}", secs), "relative"])
    }

    /// See `seek_forward`.
    pub fn seek_backward(&self, secs: ctype::c_double) -> Result<()> {
        self.command("seek", &[&format!("-{}", secs), "relative"])
    }

    /// Seek to a given absolute secs.
    pub fn seek_absolute(&self, secs: ctype::c_double) -> Result<()> {
        self.command("seek", &[&format!("{}", secs), "absolute"])
    }

    /// Seek to a given relative percent position (may be negative).
    /// If `percent` of the playtime is bigger than the remaining playtime, the next file is played.
    /// out of bounds values are clamped to either 0 or 100.
    pub fn seek_percent(&self, percent: isize) -> Result<()> {
        self.command("seek", &[&format!("{}", percent), "relative-percent"])
    }

    /// Seek to the given percentage of the playtime.
    pub fn seek_percent_absolute(&self, percent: usize) -> Result<()> {
        self.command("seek", &[&format!("{}", percent), "relative-percent"])
    }

    /// Revert the previous `seek_` call, can also revert itself.
    pub fn seek_revert(&self) -> Result<()> {
        self.command("revert-seek", &[])
    }

    /// Mark the current position as the position that will be seeked to by `seek_revert`.
    pub fn seek_revert_mark(&self) -> Result<()> {
        self.command("revert-seek", &["mark"])
    }

    /// Seek exactly one frame, and pause.
    /// Noop on audio only streams.
    pub fn seek_frame(&self) -> Result<()> {
        self.command("frame-step", &[])
    }

    /// See `seek_frame`.
    /// [Note performance considerations.](https://mpv.io/manual/master/#command-interface-frame-back-step)
    pub fn seek_frame_backward(&self) -> Result<()> {
        self.command("frame-back-step", &[])
    }

    // --- Screenshot functions ---
    //

    /// "Save the video image, in its original resolution, and with subtitles.
    /// Some video outputs may still include the OSD in the output under certain circumstances.".
    ///
    /// "\[O\]ptionally save it to a given file. The format of the file will be
    /// guessed by the extension (and --screenshot-format is ignored - the behaviour when the
    /// extension is missing or unknown is arbitrary). If the file already exists, it's overwritten.
    /// Like all input command parameters, the filename is subject to property expansion as
    /// described in [Property Expansion](https://mpv.io/manual/master/#property-expansion)."
    pub fn screenshot_subtitles(&self, path: Option<&str>) -> Result<()> {
        if let Some(path) = path {
            self.command("screenshot", &[&format!("\"{}\"", path), "subtitles"])
        } else {
            self.command("screenshot", &["subtitles"])
        }
    }

    /// "Like subtitles, but typically without OSD or subtitles. The exact behavior
    /// depends on the selected video output."
    pub fn screenshot_video(&self, path: Option<&str>) -> Result<()> {
        if let Some(path) = path {
            self.command("screenshot", &[&format!("\"{}\"", path), "video"])
        } else {
            self.command("screenshot", &["video"])
        }
    }

    /// "Save the contents of the mpv window. Typically scaled, with OSD and subtitles. The exact
    /// behaviour depends on the selected video output, and if no support is available,
    /// this will act like video.".
    pub fn screenshot_window(&self, path: Option<&str>) -> Result<()> {
        if let Some(path) = path {
            self.command("screenshot", &[&format!("\"{}\"", path), "window"])
        } else {
            self.command("screenshot", &["window"])
        }
    }

    // --- Playlist functions ---
    //

    /// Play the next item of the current playlist.
    /// Does nothing if the current item is the last item.
    pub fn playlist_next_weak(&self) -> Result<()> {
        self.command("playlist-next", &["weak"])
    }

    /// Play the next item of the current playlist.
    /// Terminates playback if the current item is the last item.
    pub fn playlist_next_force(&self) -> Result<()> {
        self.command("playlist-next", &["force"])
    }

    /// See `playlist_next_weak`.
    pub fn playlist_previous_weak(&self) -> Result<()> {
        self.command("playlist-prev", &["weak"])
    }

    /// See `playlist_next_force`.
    pub fn playlist_previous_force(&self) -> Result<()> {
        self.command("playlist-prev", &["force"])
    }

    /// Stop playback of the current file, and play the new file immediately.
    /// [More information.](https://mpv.io/manual/stable/#command-interface-[%3Coptions%3E]]])
    ///
    /// # Peculiarities
    /// `loadfile` is kind of asynchronous, any additional option is set during loading,
    /// [specifics](https://github.com/mpv-player/mpv/issues/4089).
    pub fn loadfile_replace(&self, url: &str, options: Option<&str>) -> Result<()> {
        let args = options.unwrap_or_default();

        let ret = self.command(
            "loadfile",
            &[&format!("\"{}\"", url), FileState::Replace.val(), "0", args],
        );

        if let Err(err) = ret {
            return Err(Error::Loadfile {
                error: ::std::rc::Rc::new(err),
            });
        }
        Ok(())
    }

    /// Append the file to the playlist. Optionally play the file immediately if nothing else is playing.
    /// [More information.](https://mpv.io/manual/stable/#command-interface-[%3Coptions%3E]]])
    ///
    /// # Peculiarities
    /// `loadfile` is kind of asynchronous, any additional option is set during loading,
    /// [specifics](https://github.com/mpv-player/mpv/issues/4089).
    pub fn loadfile_append(&self, url: &str, play: bool, options: Option<&str>) -> Result<()> {
        let args = options.unwrap_or_default();

        let ret = self.command(
            "loadfile",
            &[
                &format!("\"{}\"", url),
                if play {
                    FileState::AppendPlay.val()
                } else {
                    FileState::Append.val()
                },
                "0",
                args,
            ],
        );

        if let Err(err) = ret {
            return Err(Error::Loadfile {
                error: ::std::rc::Rc::new(err),
            });
        }
        Ok(())
    }

    /// Insert the file into the playlist, directly after the current entry. Optionally play the file immediately if nothing else is playing.
    /// [More information.](https://mpv.io/manual/stable/#command-interface-[%3Coptions%3E]]])
    ///
    /// # Peculiarities
    /// `loadfile` is kind of asynchronous, any additional option is set during loading,
    /// [specifics](https://github.com/mpv-player/mpv/issues/4089).
    pub fn loadfile_insert_next(&self, url: &str, play: bool, options: Option<&str>) -> Result<()> {
        let args = options.unwrap_or_default();

        let ret = self.command(
            "loadfile",
            &[
                &format!("\"{}\"", url),
                if play {
                    FileState::InsertNextPlay.val()
                } else {
                    FileState::InsertNext.val()
                },
                "0",
                args,
            ],
        );

        if let Err(err) = ret {
            return Err(Error::Loadfile {
                error: ::std::rc::Rc::new(err),
            });
        }
        Ok(())
    }

    /// Insert the file into the playlist, at the index given. Optionally play the file immediately if nothing else is playing.
    /// [More information.](https://mpv.io/manual/stable/#command-interface-[%3Coptions%3E]]])
    ///
    /// # Peculiarities
    /// `loadfile` is kind of asynchronous, any additional option is set during loading,
    /// [specifics](https://github.com/mpv-player/mpv/issues/4089).    
    pub fn loadfile_insert_at(
        &self,
        url: &str,
        play: bool,
        index: i32,
        options: Option<&str>,
    ) -> Result<()> {
        let args = options.unwrap_or_default();

        let ret = self.command(
            "loadfile",
            &[
                &format!("\"{}\"", url),
                if play {
                    FileState::InsertAtPlay.val()
                } else {
                    FileState::InsertAt.val()
                },
                &index.to_string(),
                args,
            ],
        );

        if let Err(err) = ret {
            return Err(Error::Loadfile {
                error: ::std::rc::Rc::new(err),
            });
        }
        Ok(())
    }

    /// Load the given playlist file, that either replaces the current playlist, or appends to it.
    pub fn playlist_load_list(&self, path: &str, replace: bool) -> Result<()> {
        if replace {
            self.command("loadlist", &[&format!("\"{}\"", path), "replace"])
        } else {
            self.command("loadlist", &[&format!("\"{}\"", path), "append"])
        }
    }

    /// Remove every, except the current, item from the playlist.
    pub fn playlist_clear(&self) -> Result<()> {
        self.command("playlist-clear", &[])
    }

    /// Remove the currently selected item from the playlist.
    pub fn playlist_remove_current(&self) -> Result<()> {
        self.command("playlist-remove", &["current"])
    }

    /// Remove item at `position` from the playlist.
    pub fn playlist_remove_index(&self, position: usize) -> Result<()> {
        self.command("playlist-remove", &[&format!("{}", position)])
    }

    /// Move item `old` to the position of item `new`.
    pub fn playlist_move(&self, old: usize, new: usize) -> Result<()> {
        self.command("playlist-move", &[&format!("{}", new), &format!("{}", old)])
    }

    /// Shuffle the playlist.
    pub fn playlist_shuffle(&self) -> Result<()> {
        self.command("playlist-shuffle", &[])
    }

    // --- Subtitle functions ---
    //

    /// Add and select the subtitle immediately.
    /// Specifying a language requires specifying a title.
    ///
    /// # Panics
    /// If a language but not title was specified.
    pub fn subtitle_add_select(
        &self,
        path: &str,
        title: Option<&str>,
        lang: Option<&str>,
    ) -> Result<()> {
        match (title, lang) {
            (None, None) => self.command("sub-add", &[&format!("\"{}\"", path), "select"]),
            (Some(t), None) => self.command("sub-add", &[&format!("\"{}\"", path), "select", t]),
            (None, Some(_)) => panic!("Given subtitle language, but missing title"),
            (Some(t), Some(l)) => {
                self.command("sub-add", &[&format!("\"{}\"", path), "select", t, l])
            }
        }
    }

    /// See `AddSelect`. "Don't select the subtitle.
    /// (Or in some special situations, let the default stream selection mechanism decide.)".
    ///
    /// Returns an `Error::InvalidArgument` if a language, but not a title, was provided.
    ///
    /// # Panics
    /// If a language but not title was specified.
    pub fn subtitle_add_auto(
        &self,
        path: &str,
        title: Option<&str>,
        lang: Option<&str>,
    ) -> Result<()> {
        match (title, lang) {
            (None, None) => self.command("sub-add", &[&format!("\"{}\"", path), "auto"]),
            (Some(t), None) => self.command("sub-add", &[&format!("\"{}\"", path), "auto", t]),
            (Some(t), Some(l)) => {
                self.command("sub-add", &[&format!("\"{}\"", path), "auto", t, l])
            }
            (None, Some(_)) => panic!("Given subtitle language, but missing title"),
        }
    }

    /// See `AddSelect`. "Select the subtitle. If a subtitle with the same file name was
    /// already added, that one is selected, instead of loading a duplicate entry.
    /// (In this case, title/language are ignored, and if the \[sub\] was changed since it was loaded,
    /// these changes won't be reflected.)".
    pub fn subtitle_add_cached(&self, path: &str) -> Result<()> {
        self.command("sub-add", &[&format!("\"{}\"", path), "cached"])
    }

    /// "Remove the given subtitle track. If the id argument is missing, remove the current
    /// track. (Works on external subtitle files only.)"
    pub fn subtitle_remove(&self, index: Option<usize>) -> Result<()> {
        if let Some(idx) = index {
            self.command("sub-remove", &[&format!("{}", idx)])
        } else {
            self.command("sub-remove", &[])
        }
    }

    /// "Reload the given subtitle track. If the id argument is missing, reload the current
    /// track. (Works on external subtitle files only.)"
    pub fn subtitle_reload(&self, index: Option<usize>) -> Result<()> {
        if let Some(idx) = index {
            self.command("sub-reload", &[&format!("{}", idx)])
        } else {
            self.command("sub-reload", &[])
        }
    }

    /// "Change subtitle timing such, that the subtitle event after the next `isize` subtitle
    /// events is displayed. `isize` can be negative to step backwards."
    pub fn subtitle_step(&self, skip: isize) -> Result<()> {
        self.command("sub-step", &[&format!("{}", skip)])
    }

    /// "Seek to the next subtitle. This is similar to sub-step, except that it seeks video and
    /// audio instead of adjusting the subtitle delay.
    /// For embedded subtitles (like with matroska), this works only with subtitle events that
    /// have already been displayed, or are within a short prefetch range."
    pub fn subtitle_seek_forward(&self) -> Result<()> {
        self.command("sub-seek", &["1"])
    }

    /// See `SeekForward`.
    pub fn subtitle_seek_backward(&self) -> Result<()> {
        self.command("sub-seek", &["-1"])
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn playlist_one() -> Result<()> {
        let mpv = Mpv::new().unwrap();
        mpv.set_property("vo", "null").unwrap();
        mpv.set_property("ao", "null").unwrap();

        mpv.loadfile_replace("test-data/jellyfish.mp4", None)
            .unwrap();

        let expected_file = HashMap::from([
            (String::from("id"), MpvNode::Int64(1)),
            (
                String::from("filename"),
                MpvNode::String(String::from("test-data/jellyfish.mp4")),
            ),
            (String::from("current"), MpvNode::Flag(true)),
        ]);

        let mut playlist = mpv
            .get_property::<MpvNode>("playlist")
            .unwrap()
            .array()
            .unwrap()
            .collect::<Vec<_>>();

        let file = playlist
            .pop()
            .unwrap()
            .map()
            .unwrap()
            .collect::<HashMap<_, _>>();
        assert_eq!(file, expected_file);

        Ok(())
    }

    #[test]
    fn playlist_multi() -> Result<()> {
        let mpv = Mpv::new().unwrap();
        mpv.set_property("vo", "null").unwrap();
        mpv.set_property("ao", "null").unwrap();

        mpv.loadfile_replace("test-data/jellyfish.mp4", None)?;
        mpv.loadfile_append("test-data/speech_12kbps_mb.wav", false, None)?;
        mpv.loadfile_insert_at("test-data/jellyfish.mp4", false, 1, None)?;

        let expected_0 = HashMap::from([
            (String::from("id"), MpvNode::Int64(1)),
            (
                String::from("filename"),
                MpvNode::String(String::from("test-data/jellyfish.mp4")),
            ),
            (String::from("current"), MpvNode::Flag(true)),
        ]);

        let expected_1 = HashMap::from([
            (String::from("id"), MpvNode::Int64(3)),
            (
                String::from("filename"),
                MpvNode::String(String::from("test-data/jellyfish.mp4")),
            ),
        ]);

        let expected_2 = HashMap::from([
            (String::from("id"), MpvNode::Int64(2)),
            (
                String::from("filename"),
                MpvNode::String(String::from("test-data/speech_12kbps_mb.wav")),
            ),
        ]);

        let playlist = mpv
            .get_property::<MpvNode>("playlist")
            .unwrap()
            .array()
            .unwrap()
            .collect::<Vec<_>>();

        let file_1 = playlist[0]
            .clone()
            .map()
            .unwrap()
            .collect::<HashMap<_, _>>();
        assert_eq!(file_1, expected_0);

        let file_2 = playlist[1]
            .clone()
            .map()
            .unwrap()
            .collect::<HashMap<_, _>>();
        assert_eq!(file_2, expected_1);

        let file_3 = playlist[2]
            .clone()
            .map()
            .unwrap()
            .collect::<HashMap<_, _>>();
        assert_eq!(file_3, expected_2);
        Ok(())
    }
}
