use bench::Timing;
use leanvm_core::cpu::Stats;
use primitives::{pretty_f64, pretty_integer};
use std::io::{self, Read};

pub fn read_bounded(reader: impl Read, limit: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader.take(limit as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > limit {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "input exceeds the batch size limit",
        ));
    }
    Ok(bytes)
}

pub fn report(name: &str, count: usize, stats: &Stats, bytes: usize, proving: &Timing, verifying: &Timing) {
    println!("{name}, {} signatures", pretty_integer(count));
    println!(
        "  cycles (VM steps)           : {} = {}",
        pretty_integer(stats.cycles),
        crate::report::pow(stats.cycles)
    );
    println!("    details                   : {}", stats.details());
    crate::report::print_proof_size(bytes);
    println!(
        "  proving time                : {} s{}      peak memory {} GiB",
        pretty_f64(proving.mean()),
        proving.spread(),
        crate::report::peak_gib()
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verifying.mean() * 1000.0)
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn input_bound() {
        assert_eq!(read_bounded(&b"abc"[..], 3).unwrap(), b"abc");
        assert_eq!(
            read_bounded(&b"abcd"[..], 3).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
    }
}
