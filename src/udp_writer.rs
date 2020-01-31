use std::io;
use std::net;

pub struct UdpWriter {
    sk: net::UdpSocket,
    remote: net::SocketAddr,
}

impl UdpWriter {
    pub fn new(bind_ip: net::SocketAddr, remote: net::SocketAddr) -> io::Result<UdpWriter> {
        Ok(UdpWriter {
            sk: net::UdpSocket::bind(bind_ip)?,
            remote: remote,
        })
    }
}

impl io::Write for UdpWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.sk.send_to(buf, self.remote)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn udp_writer_create() {
        let remote =
            net::UdpSocket::bind("127.0.0.1:9902".parse::<net::SocketAddr>().unwrap()).unwrap();
        let mut w = UdpWriter::new(
            "127.0.0.1:9901".parse().unwrap(),
            "127.0.0.1:9902".parse().unwrap(),
        )
        .unwrap();

        w.write(b"foo").unwrap();

        let mut buf = [0u8; 10];
        assert_eq!(remote.recv(&mut buf).unwrap(), 3);
        assert_eq!(&buf[..3], b"foo");
    }
}
