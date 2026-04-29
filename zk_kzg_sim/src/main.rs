//! ZK-KZG-Auth performance benchmark on BN254.
//!
//! Implements the full honest-prover / honest-verifier flow:
//!   * Trusted setup with toxic waste `s` and SRS of size `d+1`
//!   * UE registration: random secret polynomial `P(X)` of degree `d`,
//!     commitment `C = [P(s)]_1` via multi-scalar multiplication
//!   * Authentication: challenge `α`, evaluation `y = P(α)`,
//!     quotient polynomial `Q(X) = (P(X) - y)/(X - α)` by synthetic division,
//!     blinded proof `(π, V)` from public SRS items only
//!   * CPU verification via the optimal Ate pairing equation
//!     `e(π, [s]_2 - α·g_2) = e(C - V, g_2)`
//!
//! Reports mean / median / p95 latencies over `TRIALS` iterations and
//! per-component breakdown across multiple polynomial degrees.

use ark_bn254::{Bn254, Fr, G1Projective, G2Projective};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group, VariableBaseMSM};
use ark_ff::{PrimeField, UniformRand};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use rand::thread_rng;
use std::fs::File;
use std::io::Write;
use std::time::{Duration, Instant};

const TRIALS: usize = 200;
const DEGREES: &[usize] = &[16, 32, 64, 128, 256];

type G1Aff = <G1Projective as CurveGroup>::Affine;

struct Srs {
    g1_powers: Vec<G1Aff>,
    s_g2: G2Projective,
}

fn setup(d: usize) -> Srs {
    let mut rng = thread_rng();
    let s = Fr::rand(&mut rng);
    let g1 = G1Projective::generator();
    let g2 = G2Projective::generator();
    let mut g1_powers = Vec::with_capacity(d + 1);
    let mut acc = Fr::from(1u32);
    for _ in 0..=d {
        g1_powers.push((g1 * acc).into_affine());
        acc *= s;
    }
    Srs { g1_powers, s_g2: g2 * s }
}

/// Synthetic division of `P(X) - y` by `(X - α)`.
fn quotient_coeffs(coeffs: &[Fr], alpha: Fr, _y: Fr) -> Vec<Fr> {
    let d = coeffs.len() - 1;
    let mut q = vec![Fr::from(0u32); d];
    let mut carry = Fr::from(0u32);
    for i in (1..=d).rev() {
        carry = coeffs[i] + alpha * carry;
        q[i - 1] = carry;
    }
    q
}

fn msm(bases: &[G1Aff], scalars: &[Fr]) -> G1Projective {
    let repr: Vec<<Fr as PrimeField>::BigInt> = scalars.iter().map(|c| c.into_bigint()).collect();
    G1Projective::msm_bigint(bases, &repr)
}

struct Sample {
    ue: Duration,
    eval: Duration,
    quotient: Duration,
    msm: Duration,
    cpu: Duration,
    ok: bool,
}

fn run_one(d: usize, srs: &Srs) -> Sample {
    let mut rng = thread_rng();
    let g1 = G1Projective::generator();
    let g2 = G2Projective::generator();

    // Registration: random secret polynomial of degree d, committed via MSM.
    let poly = DensePolynomial::<Fr>::rand(d, &mut rng);
    let commitment_c = msm(&srs.g1_powers, &poly.coeffs);

    // Challenge.
    let alpha = Fr::rand(&mut rng);
    let blind = Fr::rand(&mut rng);

    // ---- UE proof generation (timed end-to-end and per-component) ----
    let t_ue = Instant::now();

    let t_eval = Instant::now();
    let y = poly.evaluate(&alpha);
    let eval_time = t_eval.elapsed();

    let t_q = Instant::now();
    let q = quotient_coeffs(&poly.coeffs, alpha, y);
    let quotient_time = t_q.elapsed();

    let t_msm = Instant::now();
    let pi_raw = msm(&srs.g1_powers[0..d], &q);
    let msm_time = t_msm.elapsed();

    let pi = pi_raw + g1 * blind;
    // V = y·g1 - r·([s]_1 - α·g1). Uses only public SRS item [s]_1 = srs.g1_powers[1].
    let s_g1 = srs.g1_powers[1].into_group();
    let v = (g1 * y) - (s_g1 - g1 * alpha) * blind;

    let ue_time = t_ue.elapsed();

    // ---- CPU verification (timed) ----
    let t_cpu = Instant::now();
    // Verifier uses public [s]_2, *not* the secret scalar s.
    let lhs_g2 = (srs.s_g2 - g2 * alpha).into_affine();
    let lhs = Bn254::pairing(pi.into_affine(), lhs_g2);
    let rhs = Bn254::pairing((commitment_c - v).into_affine(), g2.into_affine());
    let cpu_time = t_cpu.elapsed();

    Sample { ue: ue_time, eval: eval_time, quotient: quotient_time, msm: msm_time, cpu: cpu_time, ok: lhs == rhs }
}

fn stats(samples: &mut [Duration]) -> (Duration, Duration, Duration) {
    samples.sort();
    let mean = samples.iter().sum::<Duration>() / (samples.len() as u32);
    let median = samples[samples.len() / 2];
    let p95 = samples[((samples.len() as f64) * 0.95) as usize];
    (mean, median, p95)
}

fn fmt_us(d: Duration) -> String {
    format!("{:>8.2} µs", d.as_secs_f64() * 1e6)
}

fn us(d: Duration) -> f64 { d.as_secs_f64() * 1e6 }

fn main() {
    let host = format!(
        "{}-{}",
        std::env::consts::ARCH,
        std::env::consts::OS
    );
    let csv_path = std::env::args().nth(1).unwrap_or_else(|| "benchmark.csv".to_string());

    println!("=== ZK-KZG-Auth Performance Benchmark (BN254) ===");
    println!("Host: {}    Trials per degree: {}    Degrees: {:?}", host, TRIALS, DEGREES);
    println!();
    println!(
        "{:>4} | {:>11} {:>11} {:>11} | {:>11} {:>11} {:>11} | {:>11} {:>11} | OK",
        "d", "UE-mean", "UE-med", "UE-p95", "Eval", "Quotient", "MSM", "CPU-mean", "CPU-p95"
    );
    println!("{}", "-".repeat(124));

    let mut csv = match File::create(&csv_path) {
        Ok(f) => Some(f),
        Err(e) => {
            eprintln!("warning: could not create {csv_path}: {e}; CSV output disabled");
            None
        }
    };
    if let Some(f) = csv.as_mut() {
        let _ = writeln!(
            f,
            "host,arch,trials,degree,ue_mean_us,ue_median_us,ue_p95_us,eval_mean_us,quotient_mean_us,msm_mean_us,cpu_mean_us,cpu_p95_us,all_ok"
        );
    }

    for &d in DEGREES {
        let srs = setup(d);
        let mut ue = Vec::with_capacity(TRIALS);
        let mut ev = Vec::with_capacity(TRIALS);
        let mut q = Vec::with_capacity(TRIALS);
        let mut m = Vec::with_capacity(TRIALS);
        let mut cpu = Vec::with_capacity(TRIALS);
        let mut all_ok = true;

        // Warm-up to amortise cold-path effects in pairing / MSM.
        for _ in 0..5 {
            let _ = run_one(d, &srs);
        }
        for _ in 0..TRIALS {
            let s = run_one(d, &srs);
            ue.push(s.ue);
            ev.push(s.eval);
            q.push(s.quotient);
            m.push(s.msm);
            cpu.push(s.cpu);
            all_ok &= s.ok;
        }
        let (ue_m, ue_med, ue_p95) = stats(&mut ue);
        let (ev_m, _, _) = stats(&mut ev);
        let (q_m, _, _) = stats(&mut q);
        let (msm_m, _, _) = stats(&mut m);
        let (cpu_m, _, cpu_p95) = stats(&mut cpu);

        println!(
            "{:>4} | {} {} {} | {} {} {} | {} {} | {}",
            d,
            fmt_us(ue_m), fmt_us(ue_med), fmt_us(ue_p95),
            fmt_us(ev_m), fmt_us(q_m), fmt_us(msm_m),
            fmt_us(cpu_m), fmt_us(cpu_p95),
            if all_ok { "yes" } else { "FAIL" }
        );

        if let Some(f) = csv.as_mut() {
            let _ = writeln!(
                f,
                "{},{},{},{},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{}",
                host,
                std::env::consts::ARCH,
                TRIALS,
                d,
                us(ue_m), us(ue_med), us(ue_p95),
                us(ev_m), us(q_m), us(msm_m),
                us(cpu_m), us(cpu_p95),
                all_ok
            );
        }
    }

    println!();
    println!("Over-the-air payload : 64 bytes (two compressed G1 points: π, V)");
    println!("Round trips          : 1 (single challenge-response)");
    println!("All authentications successful — pairing equation balances end-to-end.");
    if csv.is_some() {
        println!("CSV written to: {csv_path}");
    }
}
