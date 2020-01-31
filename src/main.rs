#[macro_use]
extern crate logu;

use logu::LogU;

fn main() {
    let mut logger = LogU::new(
        String::from("Youmu"),
        String::from("a.out"),
        "127.0.0.1:9901".parse().unwrap(),
        "127.0.0.1:9999".parse().unwrap(),
    )
    .expect("create LogU failed");

    println!("host = {}, prog = {}", logger.hostname, logger.progname,);

    info!(logger.udp_logger, "test 10101011010");
}
