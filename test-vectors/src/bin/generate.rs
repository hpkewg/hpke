use std::process;

use hpke_ref::test_vectors::{TestVector, TestVectors};
use hpke_ref::*;

fn generate_test_vectors() -> TestVectors {
    let mut vectors = TestVectors::new();

    vectors.push(TestVector::new::<DhkemX25519HkdfSha256, HkdfSha256, Aes128Gcm>());
    vectors.push(TestVector::new::<DhkemX25519HkdfSha256, HkdfSha256, ChaChaPoly>());
    vectors.push(TestVector::new::<DhkemX25519HkdfSha256, HkdfSha256, ExportOnly>());
    vectors.push(TestVector::new::<DhkemP256HkdfSha256, HkdfSha256, Aes128Gcm>());
    vectors.push(TestVector::new::<DhkemP256HkdfSha256, HkdfSha512, Aes128Gcm>());
    vectors.push(TestVector::new::<DhkemP256HkdfSha256, HkdfSha256, ChaChaPoly>());
    vectors.push(TestVector::new::<DhkemP521HkdfSha512, HkdfSha512, Aes256Gcm>());
    vectors.push(TestVector::new::<DhkemP384HkdfSha384, HkdfSha384, Aes256Gcm>());
    vectors.push(TestVector::new::<DhkemX448HkdfSha512, HkdfSha512, Aes256Gcm>());

    vectors
}

fn main() {
    let vectors = generate_test_vectors();

    let json = match serde_json::to_string_pretty(&vectors) {
        Ok(j) => j,
        Err(e) => {
            eprintln!("Error serializing test vectors: {}", e);
            process::exit(1);
        }
    };

    println!("{}", json);
}
