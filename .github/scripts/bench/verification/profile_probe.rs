//! Standalone calibration control: measured worker work versus excluded work.

#[path = "../../../../benches/ci/profile.rs"]
mod profile;

fn work(n: u64) -> u64 {
    let mut result = 7u64;
    for i in 0..n {
        result = std::hint::black_box(result.wrapping_mul(3).wrapping_add(i));
    }
    result
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).map(|v| v.parse::<u64>().unwrap()).collect();
    let (send, receive) = std::sync::mpsc::channel();
    let (done, result) = std::sync::mpsc::channel();
    let worker = std::thread::spawn(move || {
        let n = receive.recv().unwrap();
        done.send(work(n)).unwrap();
    });
    std::hint::black_box(work(args[1]));
    profile::measure("prove", || {
        send.send(args[0]).unwrap();
        std::hint::black_box(result.recv().unwrap());
    });
    worker.join().unwrap();
}
