// One-off search: find an `ikm` for DHKEM(P-256, HKDF-SHA256) whose
// DeriveKeyPair rejects the counter=0 candidate (candidate >= group order),
// so the key pair is produced at counter=1.  This exercises the rejection
// sampling loop, which every other published vector skips.
//
// Run with: cargo run --release --bin search-p256
//
// The result `ikm` is then hard-coded into the edge-vectors generator.

use hpke_ref::*;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

// suite_id for DHKEM(P-256, HKDF-SHA256): "KEM" || I2OSP(0x0010, 2)
const KEM_SUITE_ID: &[u8] = &[0x4b, 0x45, 0x4d, 0x00, 0x10];

// 24-byte ASCII prefix; the trailing 8 bytes are a big-endian counter -> 32-byte ikm.
fn ikm_for(n: u64) -> Vec<u8> {
    let mut v = b"hpke-edge-p256-rejection".to_vec();
    v.extend_from_slice(&n.to_be_bytes());
    v
}

fn main() {
    let order = hex::decode(
        "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    )
    .unwrap();

    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    eprintln!("searching with {} threads...", nthreads);

    let found = Arc::new(AtomicBool::new(false));
    let result = Arc::new(AtomicU64::new(0));
    let counter = Arc::new(AtomicU64::new(0));

    let mut handles = Vec::new();
    for tid in 0..nthreads {
        let found = found.clone();
        let result = result.clone();
        let counter = counter.clone();
        let order = order.clone();
        handles.push(std::thread::spawn(move || {
            let mut n = tid as u64;
            let step = nthreads as u64;
            let mut local: u64 = 0;
            while !found.load(Ordering::Relaxed) {
                let ikm = ikm_for(n);
                // For P-256 the bitmask is 0xff, so the candidate is used unmasked.
                let cand = HkdfSha256::derive_candidate(KEM_SUITE_ID, &ikm, 0, 32);
                if cand.as_slice() >= order.as_slice() {
                    if !found.swap(true, Ordering::Relaxed) {
                        result.store(n, Ordering::Relaxed);
                        println!(
                            "FOUND n={} ikm={} candidate0={}",
                            n,
                            hex::encode(&ikm),
                            hex::encode(&cand)
                        );
                    }
                    return;
                }
                n += step;
                local += 1;
                if local % (1 << 24) == 0 {
                    let total = counter.fetch_add(1 << 24, Ordering::Relaxed) + (1 << 24);
                    eprintln!("progress: ~{} candidates tried", total);
                }
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    let n = result.load(Ordering::Relaxed);
    println!("done; n={} ikm={}", n, hex::encode(ikm_for(n)));
}
