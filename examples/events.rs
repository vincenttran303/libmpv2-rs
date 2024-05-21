use libmpv2::{events::*, mpv_node::MpvNode, *};

use std::{collections::HashMap, env, thread, time::Duration};

const VIDEO_URL: &str = "https://www.youtube.com/watch?v=VLnWf1sQkjY";

fn main() -> Result<()> {
    let path = env::args()
        .nth(1)
        .unwrap_or_else(|| String::from(VIDEO_URL));

    // Create an `Mpv` and set some properties.
    let mpv = Mpv::with_initializer(|init| {
        init.set_property("vo", "null")?;
        Ok(())
    })
    .unwrap();
    mpv.set_property("volume", 15)?;

    let mut ev_ctx = EventContext::new(mpv.ctx);
    ev_ctx.disable_deprecated_events()?;
    ev_ctx.observe_property("volume", Format::Int64, 0)?;
    ev_ctx.observe_property("demuxer-cache-state", Format::Node, 0)?;

    crossbeam::scope(|scope| {
        scope.spawn(|_| {
            mpv.command("loadfile", &[&path, "append-play"]).unwrap();

            thread::sleep(Duration::from_secs(3));

            mpv.set_property("volume", 25).unwrap();

            thread::sleep(Duration::from_secs(5));

            // Trigger `Event::EndFile`.
            mpv.command("playlist-next", &["force"]).unwrap();
        });
        scope.spawn(move |_| loop {
            let ev = ev_ctx.wait_event(600.).unwrap_or(Err(Error::Null));

            match ev {
                Ok(Event::EndFile(r)) => {
                    println!("Exiting! Reason: {:?}", r);
                    break;
                }

                Ok(Event::PropertyChange {
                    name: "demuxer-cache-state",
                    change: PropertyData::Node(mpv_node),
                    ..
                }) => {
                    let ranges = seekable_ranges(mpv_node);
                    println!("Seekable ranges updated: {:?}", ranges);
                }
                Ok(e) => println!("Event triggered: {:?}", e),
                Err(e) => println!("Event errored: {:?}", e),
            }
        });
    })
    .unwrap();
    Ok(())
}

fn seekable_ranges(demuxer_cache_state: MpvNode) -> Vec<(f64, f64)> {
    let mut res = Vec::new();
    let props = demuxer_cache_state
        .map()
        .unwrap()
        .collect::<HashMap<_, _>>();
    let ranges = props
        .get("seekable-ranges")
        .unwrap()
        .clone()
        .array()
        .unwrap();
    for node in ranges {
        let range = node.map().unwrap().collect::<HashMap<_, _>>();
        let start = range.get("start").unwrap().f64().unwrap();
        let end = range.get("end").unwrap().f64().unwrap();
        res.push((start, end));
    }
    res
}
