// Generate the "Edge-Case Test Vectors" appendix for draft-ietf-hpke-hpke.
//
// These vectors exercise behavior defined by HPKE itself (its labeled key
// schedule, DeriveKeyPair rejection sampling, and forwarding of empty/zero-byte
// inputs), as opposed to the underlying AEAD/KDF/curve primitives, which have
// their own test vectors.
//
// All vectors except the KEM rejection-sampling case (C.1) use the single suite
// DHKEM(X25519, HKDF-SHA256) / HKDF-SHA256 / AES-128-GCM, because the behavior
// exercised is independent of the choice of KEM, KDF, and AEAD.
//
// Run with: cargo run --bin edge-vectors

use hpke_ref::*;

// ----- canonical key material reused from the main (RFC 9180) vectors -----
// Base context (X25519/HKDF-SHA256/AES-128-GCM):
const X_IKM_E: &str = "7268600d403fce431561aef583ee1613527cff655c1343f29812e66706df3234";
const X_IKM_R: &str = "6db9df30aa07dd42ee5e8181afdb977e538f5e1fec8a06223f33f7013e525037";
const INFO: &str = "4f6465206f6e2061204772656369616e2055726e"; // "Ode on a Grecian Urn"
// PSK context:
const X_PSK_IKM_E: &str = "78628c354e46f3e169bd231be7b2ff1c77aa302460a26dbfa15515684c00130b";
const X_PSK_IKM_R: &str = "d4a09d09f575fef425905d2ab396c1449141463f698f8efdb7accfaff8995098";

// P-256 ephemeral ikm (reused from the main P-256 vectors); the recipient ikm
// below is the special one that triggers rejection sampling.
const P_IKM_E: &str = "4270e54ffd08d79d5928020af4686d8f6b7d35dbe470265f1f5aa22816ce860e";
// suite_id for DHKEM(P-256, HKDF-SHA256), used to recompute the rejected candidate.
const KEM_P256_SUITE_ID: &[u8] = &[0x4b, 0x45, 0x4d, 0x00, 0x10];

// Found by search-p256: DeriveKeyPair rejects the counter=0 candidate (its first
// four bytes are 0xffffffff, making it >= the P-256 group order) and uses counter=1.
const P256_REJECT_IKM: &str = "68706b652d656467652d703235362d72656a656374696f6e00000001c6be4ce7";

// Canonical plaintext/aad/exporter_context, plus zero-byte edge values.
const PT: &str = "4265617574792069732074727574682c20747275746820626561757479";
const AAD: &str = "436f756e742d30"; // "Count-0"
const EXP_CTX: &str = "54657374436f6e74657874"; // "TestContext"

fn h(s: &str) -> Vec<u8> {
    hex::decode(s).unwrap()
}

// --- hex formatting, matching the existing test-vector appendix ---
const MAX_LINE_LENGTH: usize = 70;

fn format_hex(data: &[u8], label: &str) -> String {
    let hex_string = hex::encode(data);
    if label.len() + hex_string.len() <= MAX_LINE_LENGTH {
        return hex_string;
    }
    let mut result = String::from("\n");
    for chunk in hex_string
        .chars()
        .collect::<Vec<_>>()
        .chunks(MAX_LINE_LENGTH)
    {
        result.push_str(&chunk.iter().collect::<String>());
        result.push('\n');
    }
    result.pop();
    result
}

fn field(label: &str, data: &[u8]) -> String {
    // Strip any trailing whitespace left when the value is empty or wraps to a
    // new line (e.g. "shared_secret: \n..."), so the output is lint-clean.
    let line = format!("{}{}", label, format_hex(data, label));
    let cleaned = line
        .split('\n')
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    format!("{}\n", cleaned)
}

#[allow(clippy::too_many_arguments)]
fn render_context<K, H, A>(
    title: &str,
    intro: &str,
    mode: Mode,
    info: &[u8],
    psk: &[u8],
    psk_id: &[u8],
    ikm_r: &[u8],
    ikm_e: &[u8],
    extra_setup: &[String],
    encryptions: &[(&[u8], &[u8])], // (pt, aad) in sequence
    exports: &[(&[u8], u32)],       // (exporter_context, L)
) -> String
where
    K: Kem,
    H: Kdf,
    A: Aead,
{
    let (sk_r, pk_r) = K::derive_key_pair(ikm_r);
    let (shared_secret, enc) = K::encap_derand(&pk_r, ikm_e);
    let suite_id = Instance::<K, H, A>::suite_id();
    let (key, base_nonce, exporter_secret) = H::combine_secrets(
        &suite_id,
        mode,
        &shared_secret,
        info,
        psk,
        psk_id,
        A::N_K,
        A::N_N,
    );

    let is_psk = matches!(mode, Mode::Psk);
    let mut o = String::new();
    o.push_str(&format!("## {}\n\n", title));
    if !intro.is_empty() {
        o.push_str(intro);
        o.push_str("\n\n");
    }

    let setup = if is_psk {
        "PSK Setup Information"
    } else {
        "Base Setup Information"
    };
    o.push_str(&format!("### {}\n~~~\n", setup));
    o.push_str(&format!("mode: {}\n", u8::from(mode)));
    o.push_str(&format!("kem_id: {}\n", u16::from_be_bytes(K::ID)));
    o.push_str(&format!("kdf_id: {}\n", u16::from_be_bytes(H::ID)));
    o.push_str(&format!("aead_id: {}\n", u16::from_be_bytes(A::ID)));
    o.push_str(&field("info: ", info));
    o.push_str(&field("ikmE: ", ikm_e));
    o.push_str(&field("ikmR: ", ikm_r));
    for line in extra_setup {
        o.push_str(line);
    }
    o.push_str(&field("skRm: ", &K::serialize_private_key(&sk_r)));
    o.push_str(&field("pkRm: ", &K::serialize_public_key(&pk_r)));
    o.push_str(&field("enc: ", &enc));
    o.push_str(&field("shared_secret: ", &shared_secret));
    o.push_str(&field("key: ", &key));
    o.push_str(&field("base_nonce: ", &base_nonce));
    o.push_str(&field("exporter_secret: ", &exporter_secret));
    if is_psk {
        o.push_str(&field("psk: ", psk));
        o.push_str(&field("psk_id: ", psk_id));
    }
    o.push_str("~~~\n\n");

    if A::ID != [0xff, 0xff] && !encryptions.is_empty() {
        o.push_str("#### Encryptions\n~~~\n");
        let mut ctx =
            Context::<A, Sender>::new(key.clone(), base_nonce.clone(), exporter_secret.clone());
        for (i, (pt, aad)) in encryptions.iter().enumerate() {
            if i > 0 {
                o.push('\n');
            }
            let nonce = ctx.compute_nonce();
            let ct = ctx.seal(aad, pt);
            o.push_str(&format!("sequence number: {}\n", i));
            o.push_str(&field("pt: ", pt));
            o.push_str(&field("aad: ", aad));
            o.push_str(&field("nonce: ", &nonce));
            o.push_str(&field("ct: ", &ct));
        }
        o.push_str("~~~\n\n");
    }

    if !exports.is_empty() {
        o.push_str("#### Exported Values\n~~~\n");
        for (i, (ec, l)) in exports.iter().enumerate() {
            if i > 0 {
                o.push('\n');
            }
            let ev = H::export(&suite_id, &exporter_secret, ec, *l as usize);
            let ec_line = format!("exporter_context: {}", hex::encode(ec));
            o.push_str(ec_line.trim_end());
            o.push('\n');
            o.push_str(&format!("L: {}\n", l));
            o.push_str(&field("exported_value: ", &ev));
        }
        o.push_str("~~~\n\n");
    }

    o
}

fn main() {
    let mut out = String::new();
    out.push_str("# Edge-Case Test Vectors\n\n");
    out.push_str(
        "This appendix contains test vectors that exercise behavior defined by HPKE \
itself -- DeriveKeyPair rejection sampling, the labeled key schedule, and the \
handling of empty and zero-byte inputs -- rather than the underlying KEM, KDF, \
and AEAD primitives.  Except for the rejection-sampling vector in the first \
section, all vectors use the suite DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, \
AES-128-GCM, because the behavior exercised is independent of the choice of \
KEM, KDF, and AEAD.\n\n",
    );

    // ---- C.1: P-256 DeriveKeyPair rejection sampling ----
    let reject_ikm = h(P256_REJECT_IKM);
    let cand0 = HkdfSha256::derive_candidate(KEM_P256_SUITE_ID, &reject_ikm, 0, 32);
    let extra = vec![field("rejected_candidate (counter=0): ", &cand0)];
    out.push_str(&render_context::<DhkemP256HkdfSha256, HkdfSha256, Aes128Gcm>(
        "KEM Key Derivation with Rejection Sampling",
        "In this vector the recipient `ikm` is chosen so that the candidate private \
key derived with `counter = 0` (`rejected_candidate` below) is greater than or \
equal to the order of the P-256 group and is therefore rejected; the key pair is \
produced from the candidate at `counter = 1`.  This exercises the rejection \
sampling loop in `DeriveKeyPair`.",
        Mode::Base,
        &h(INFO),
        &[],
        &[],
        &reject_ikm,
        &h(P_IKM_E),
        &extra,
        &[(&h(PT), &h(AAD))],
        &[(&h(EXP_CTX), 32)],
    ));

    // ---- C.2: empty and zero-byte AEAD inputs + exporter_context ----
    let zb_aad = vec![0x00u8, 0xff, 0x00, 0xff, 0x00];
    let zb_pt = vec![0x00u8, 0x01, 0x00, 0x02, 0x00, 0x03, 0x00];
    let zb_ctx = vec![0x00u8, 0x11, 0x00, 0x22, 0x00];
    out.push_str(&render_context::<DhkemX25519HkdfSha256, HkdfSha256, Aes128Gcm>(
        "Empty and Zero-Byte AEAD Inputs",
        "This vector uses a normal context and exercises empty and zero-byte values \
for the per-message `aad` and `pt` inputs and the `exporter_context` input.",
        Mode::Base,
        &h(INFO),
        &[],
        &[],
        &h(X_IKM_R),
        &h(X_IKM_E),
        &[],
        &[
            (&[], &h(AAD)),       // empty pt
            (&h(PT), &[]),        // empty aad
            (&zb_pt, &h(AAD)),    // pt with embedded zero bytes
            (&h(PT), &zb_aad),    // aad with embedded zero bytes
        ],
        &[
            (&[], 32),       // empty exporter_context
            (&[0x00], 32),   // single zero byte
            (&zb_ctx, 32),   // embedded zero bytes
        ],
    ));

    // ---- C.3: empty info ----
    out.push_str(&render_context::<DhkemX25519HkdfSha256, HkdfSha256, Aes128Gcm>(
        "Empty info",
        "This vector uses an empty `info` value in the key schedule.",
        Mode::Base,
        &[],
        &[],
        &[],
        &h(X_IKM_R),
        &h(X_IKM_E),
        &[],
        &[(&h(PT), &h(AAD))],
        &[(&h(EXP_CTX), 32)],
    ));

    // ---- C.4: zero-byte info ----
    let zb_info = vec![0xf0u8, 0x00, 0x0f, 0x00, 0xff];
    out.push_str(&render_context::<DhkemX25519HkdfSha256, HkdfSha256, Aes128Gcm>(
        "info with Embedded Zero Bytes",
        "This vector uses an `info` value that contains embedded zero bytes in the \
key schedule.",
        Mode::Base,
        &zb_info,
        &[],
        &[],
        &h(X_IKM_R),
        &h(X_IKM_E),
        &[],
        &[(&h(PT), &h(AAD))],
        &[(&h(EXP_CTX), 32)],
    ));

    // ---- C.5: zero-byte psk and psk_id ----
    // psk retains 32 bytes of length, with embedded zero bytes.
    let zb_psk = h("0000000000000000111111111111111100000000000000002222222222222222");
    let zb_psk_id = vec![0x00u8, 0x50, 0x53, 0x4b, 0x00, 0x69, 0x64, 0x00]; // "\0PSK\0id\0"
    out.push_str(&render_context::<DhkemX25519HkdfSha256, HkdfSha256, Aes128Gcm>(
        "psk and psk_id with Embedded Zero Bytes",
        "This vector uses PSK mode with a `psk` and `psk_id` that contain embedded \
zero bytes.",
        Mode::Psk,
        &h(INFO),
        &zb_psk,
        &zb_psk_id,
        &h(X_PSK_IKM_R),
        &h(X_PSK_IKM_E),
        &[],
        &[(&h(PT), &h(AAD))],
        &[(&h(EXP_CTX), 32)],
    ));

    print!("{}", out);
}
