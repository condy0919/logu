#[macro_use]
pub mod logger;
mod udp_writer;

pub use logger::{Level, LevelParseError};
use std::io;
use std::net;

pub struct LogU {
    pub hostname: String,
    pub progname: String,
    pub udp_logger: logger::Logger,
}

impl LogU {
    pub fn new(
        host: String,
        prog: String,
        bind_ip: net::SocketAddr,
        remote: net::SocketAddr,
    ) -> io::Result<Self> {
        let w = udp_writer::UdpWriter::new(bind_ip, remote)?;
        Ok(LogU {
            hostname: host,
            progname: prog,
            udp_logger: logger::Logger::new(Level::Info, Box::new(w)),
        })
    }
}
