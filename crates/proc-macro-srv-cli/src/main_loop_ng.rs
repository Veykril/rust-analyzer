//! The main loop of the proc-macro server.

#![allow(clippy::disallowed_types)]

use std::{
    collections::{hash_map::Entry, HashMap},
    io,
    thread::{self, Scope, ScopedJoinHandle},
};

use crossbeam_channel::{select, Sender};
use proc_macro_api::ng_protocol::msg::{
    self, deserialize_span_data_index_map, serialize_span_data_index_map, C2SResponse, ChannelId,
    ExpnGlobals, SpanMode, CURRENT_API_VERSION,
};
use proc_macro_srv::EnvSnapshot;

pub(crate) fn run(span_mode: SpanMode) -> io::Result<()> {
    let mut buf = String::new();
    let mut read_packet = || -> io::Result<Option<msg::C2SPacket>> { todo!() };
    let write_packet = |msg: msg::S2CPacket| -> io::Result<()> { todo!() };

    let (reader_sender, reader_receiver) = crossbeam_channel::unbounded();
    let _reader_thread = thread::spawn(move || {
        while let Some(packet) = read_packet().unwrap() {
            reader_sender.send(packet).unwrap();
        }
    });

    let env = EnvSnapshot::default();
    let srv = &proc_macro_srv::ProcMacroSrv::new(&env);

    let (loop_sender, loop_receiver) = crossbeam_channel::unbounded();
    thread::scope(|scope| -> io::Result<()> {
        let mut open_channels: HashMap<
            ChannelId,
            (ScopedJoinHandle<'_, _>, Option<Sender<msg::C2SResponse>>),
        > = HashMap::default();
        loop {
            select! {
                recv(reader_receiver) -> msg => {
                    f(&mut open_channels, msg.unwrap(), write_packet, &loop_sender, scope, srv, span_mode)?
                },
                recv(loop_receiver) -> msg => {
                    handle_loopcmd(&mut open_channels, msg.unwrap(), write_packet)?
                },
            };
        }
    })?;
    _reader_thread.join().unwrap();
    Ok(())
}

enum LoopCmd {
    CloseChannel(ChannelId, msg::S2CResponse),
    Request(ChannelId, msg::S2CRequest, Sender<msg::C2SResponse>),
}

fn handle_loopcmd(
    open_channels: &mut HashMap<ChannelId, (ScopedJoinHandle<'_, ()>, Option<Sender<C2SResponse>>)>,
    cmd: LoopCmd,
    write_packet: impl FnOnce(msg::S2CPacket) -> io::Result<()>,
) -> io::Result<()> {
    match cmd {
        LoopCmd::CloseChannel(channel, resp) => {
            write_packet(msg::S2CPacket { data: msg::S2CData::Response(resp), channel })?;
            let (thread, cb) = open_channels.remove(&channel).unwrap();
            assert!(cb.is_none());
            thread.join().unwrap();
        }
        LoopCmd::Request(channel, req, callback) => {
            write_packet(msg::S2CPacket { data: msg::S2CData::Request(req), channel })?;
            assert!(open_channels.get_mut(&channel).unwrap().1.replace(callback).is_none());
        }
    }
    Ok(())
}

fn f<'scope>(
    open_channels: &mut HashMap<
        ChannelId,
        (ScopedJoinHandle<'scope, ()>, Option<Sender<C2SResponse>>),
    >,
    packet: msg::C2SPacket,
    write_packet: impl FnOnce(msg::S2CPacket) -> io::Result<()>,
    loop_sender: &Sender<LoopCmd>,
    scope: &'scope Scope<'scope, '_>,
    srv: &'scope proc_macro_srv::ProcMacroSrv<'_>,
    span_mode: SpanMode,
) -> io::Result<()> {
    fn macro_kind_to_api(kind: proc_macro_srv::ProcMacroKind) -> proc_macro_api::ProcMacroKind {
        match kind {
            proc_macro_srv::ProcMacroKind::CustomDerive => {
                proc_macro_api::ProcMacroKind::CustomDerive
            }
            proc_macro_srv::ProcMacroKind::Bang => proc_macro_api::ProcMacroKind::Bang,
            proc_macro_srv::ProcMacroKind::Attr => proc_macro_api::ProcMacroKind::Attr,
        }
    }

    match packet.data {
        msg::C2SData::Response(data) => match open_channels.entry(packet.channel) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.get_mut().1.take().unwrap().send(data).unwrap()
            }
            Entry::Vacant(_) => write_packet(msg::S2CPacket {
                channel: packet.channel,
                data: msg::S2CData::Response(msg::S2CResponse::Error("".to_owned())),
            })?,
        },
        msg::C2SData::Request(data) => match open_channels.entry(packet.channel) {
            Entry::Occupied(_) => write_packet(msg::S2CPacket {
                channel: packet.channel,
                data: msg::S2CData::Response(msg::S2CResponse::Error("".to_owned())),
            })?,
            Entry::Vacant(vacant_entry) => {
                let loop_sender = loop_sender.clone();
                _ = vacant_entry.insert((
                    scope.spawn(move || {
                        let res = match data {
                            msg::C2SRequest::ListMacros { dylib_path } => {
                                msg::S2CResponse::ListMacros(srv.list_macros(&dylib_path).map(
                                    |macros| {
                                        macros
                                            .into_iter()
                                            .map(|(name, kind)| (name, macro_kind_to_api(kind)))
                                            .collect()
                                    },
                                ))
                            }
                            msg::C2SRequest::ExpandMacro { task } => match span_mode {
                                SpanMode::Id => unimplemented!(),
                                SpanMode::RustAnalyzer => {
                                    let msg::ExpandMacro {
                                        lib,
                                        env,
                                        current_dir,
                                        macro_body,
                                        macro_name,
                                        attribute,
                                        has_global_spans:
                                            ExpnGlobals { def_site, call_site, mixed_site },
                                        span_data_table,
                                    } = *task;
                                    msg::S2CResponse::ExpandMacro({
                                        let mut span_data_table =
                                            deserialize_span_data_index_map(&span_data_table);

                                        let def_site = span_data_table[def_site];
                                        let call_site = span_data_table[call_site];
                                        let mixed_site = span_data_table[mixed_site];

                                        let macro_body = macro_body.to_subtree_resolved(
                                            CURRENT_API_VERSION,
                                            &span_data_table,
                                        );
                                        let attribute = attribute.map(|it| {
                                            it.to_subtree_resolved(
                                                CURRENT_API_VERSION,
                                                &span_data_table,
                                            )
                                        });
                                        srv.expand(
                                            lib,
                                            env,
                                            current_dir,
                                            macro_name,
                                            macro_body,
                                            attribute,
                                            def_site,
                                            call_site,
                                            mixed_site,
                                            |req| {
                                                let req = match req {};
                                                let (tx, rx) = crossbeam_channel::bounded(1);
                                                loop_sender
                                                    .send(LoopCmd::Request(packet.channel, req, tx))
                                                    .unwrap();
                                                match rx.recv().unwrap() {}
                                            },
                                        )
                                        .map(|it| {
                                            (
                                                msg::FlatTree::new(
                                                    tt::SubtreeView::new(&it),
                                                    CURRENT_API_VERSION,
                                                    &mut span_data_table,
                                                ),
                                                serialize_span_data_index_map(&span_data_table),
                                            )
                                        })
                                        .map(|(tree, span_data_table)| msg::ExpandMacroExtended {
                                            tree,
                                            span_data_table,
                                        })
                                        .map_err(msg::PanicMessage)
                                    })
                                }
                            },
                            msg::C2SRequest::ApiVersionCheck {} => {
                                msg::S2CResponse::ApiVersionCheck(CURRENT_API_VERSION)
                            }
                        };
                        loop_sender.send(LoopCmd::CloseChannel(packet.channel, res)).unwrap();
                    }),
                    None,
                ))
            }
        },
    }
    Ok(())
}
