use ark_ec::{pairing::Pairing, Group};
use ark_ff::{FftField, Field};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::*;
use ark_std::Zero;

use crate::{
    dealer::CRS,
    encryption::Ciphertext,
    utils::{hash_to_bytes, interpolate_almostgood, open_all_values, xor},
};

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct SecretKey<E: Pairing> {
    lag_share: Vec<E::ScalarField>,
    alpha_share: E::ScalarField,
    r_share: E::ScalarField,
}

impl<E: Pairing> SecretKey<E> {
    pub fn new(lag_share: Vec<E::ScalarField>, alpha_share: E::ScalarField, r_share: E::ScalarField) -> Self {
        SecretKey {
            lag_share,
            alpha_share,
            r_share,
        }
    }

    /// each party in the committee computes a partial decryption
    pub fn partial_decrypt(&self, ct: &Vec<Ciphertext<E>>, gtilde: E::G1, htilde: E::G2, crs: &CRS<E>) -> (E::ScalarField, E::G1) {

        let mut partial_decryption1 = self.alpha_share;
        let batch_size = self.lag_share.len();

        // Check that all ciphertexts are valid
        for i in 0..batch_size {
            ct[i].verify(gtilde, htilde, crs);
        }

        // compute partial decryption
        for i in 0..batch_size {
            let tg_bytes = hash_to_bytes(ct[i].gs);
            let peval = E::ScalarField::from_random_bytes(&tg_bytes).unwrap();
            partial_decryption1 += self.lag_share[i] * peval;
        }

        let partial_decryption2 =  E::G1::generator() * self.r_share;
        
        (partial_decryption1, partial_decryption2)
    }
}

/// decrypts all the ciphertexts in a batch
pub fn decrypt_all<E: Pairing>(
    partial_decryptions1: &Vec<E::ScalarField>,
    partial_decryptions2: &Vec<E::G1>,
    ct: &Vec<Ciphertext<E>>,
    crs: &CRS<E>,
) -> Vec<[u8; 32]> {
    let batch_size = ct.len();
    let n = partial_decryptions1.len();

    let share_domain = Radix2EvaluationDomain::<E::ScalarField>::new(n).unwrap();
    let tx_domain = Radix2EvaluationDomain::<E::ScalarField>::new(batch_size).unwrap();
    let gamma = E::ScalarField::GENERATOR;

    let fofgamma = share_domain.ifft(&partial_decryptions1)[0];
    let pi2 = share_domain.ifft(&partial_decryptions2)[0];

    // compute fevals by hashing gs of the ciphertexts to get fevals
    let mut fevals = vec![E::ScalarField::zero(); batch_size + 1];
    for i in 0..batch_size {
        let tg_bytes = hash_to_bytes(ct[i].gs);
        fevals[i] = E::ScalarField::from_random_bytes(&tg_bytes).unwrap();
    }
    fevals[batch_size] = fofgamma;

    // fevals are on an 'almost' nice domain. so we first interpolate quotient polynomial
    // where the evaluations are determined as q(x) = (f(x) - f(gamma))/(x-gamma)
    let f = interpolate_almostgood(&fevals, &tx_domain, fofgamma, gamma);

    // use FK22 to get all the KZG proofs in O(nlog n) time =======================
    let pi1 = open_all_values::<E>(&crs.y, &f, &tx_domain);

    // now decrypt each of the ciphertexts as m = ct1 \xor H(e(pi1, ct2).e(pi2,ct3))
    let mut m = vec![[0u8; 32]; batch_size];
    for i in 0..batch_size {
        let mask = E::pairing(pi1[i], ct[i].ct2) + E::pairing(pi2, ct[i].ct3);
        let hmask = hash_to_bytes(mask);
        m[i] = xor(&ct[i].ct1, &hmask).as_slice().try_into().unwrap();
    }

    m
}

#[cfg(test)]
mod tests {
    use crate::{dealer::Dealer, encryption::encrypt};

    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ec::bls12::Bls12;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

    type E = Bls12_381;
    type Fr = <Bls12<ark_bls12_381::Config> as Pairing>::ScalarField;
    type G1 = <Bls12<ark_bls12_381::Config> as Pairing>::G1;
    type G2 = <Bls12<ark_bls12_381::Config> as Pairing>::G2;

    #[test]
    fn test_encryption() {
        let mut rng = ark_std::test_rng();

        let batch_size = 1 << 5;
        let n = 1 << 4;
        let tx_domain = Radix2EvaluationDomain::<Fr>::new(batch_size).unwrap();

        let mut dealer = Dealer::<E>::new(batch_size, n);
        let (crs, lag_shares) = dealer.setup(&mut rng);
        let (gtilde, htilde, com, alpha_shares, r_shares) = dealer.epoch_setup(&mut rng);

        let mut msg = Vec::new();
        for i in 0..batch_size {
            msg.push([i as u8; 32]);
        }
        let x = tx_domain.group_gen;

        let mut ct = Vec::new();
        for i in 0..batch_size {
            let cti = encrypt::<Bls12_381, _>(msg[i], x, com, htilde, crs.htau, &mut rng);
            ct.push(cti);
        }

        let mut ct_bytes = Vec::new();
        ct.serialize_compressed(&mut ct_bytes).unwrap();
        println!("Compressed ciphertext: {} bytes", ct_bytes.len());

        let mut ct_bytes = Vec::new();
        ct.serialize_uncompressed(&mut ct_bytes).unwrap();
        println!("Uncompressed ciphertext: {} bytes", ct_bytes.len());

        let mut g1_bytes = Vec::new();
        let mut g2_bytes = Vec::new();
        let mut fr_bytes = Vec::new();
        
        let g = G1::generator();
        let h = G2::generator();
        let x = tx_domain.group_gen;
        
        g.serialize_compressed(&mut g1_bytes).unwrap();
        h.serialize_compressed(&mut g2_bytes).unwrap();
        x.serialize_compressed(&mut fr_bytes).unwrap();

        println!("G1 len: {} bytes", g1_bytes.len());
        println!("G2 len: {} bytes", g2_bytes.len());
        println!("Fr len: {} bytes", fr_bytes.len());

        for ciphertext in &ct {
            ciphertext.verify(gtilde, htilde, &crs);
        }

        let mut secret_keys = Vec::new();
        for i in 0..n {
            let sk = SecretKey::<E>::new(lag_shares[i].clone(), alpha_shares[i], r_shares[i]);
            secret_keys.push(sk);
        }

        let mut partial_decryptions1 = Vec::new();
        let mut partial_decryptions2 = Vec::new();

        for sk in &secret_keys {
            let (pd1, pd2) = sk.partial_decrypt(&ct, gtilde, htilde, &crs);
            partial_decryptions1.push(pd1);
            partial_decryptions2.push(pd2);
        }

        assert_eq!(partial_decryptions1.len(), n);
        assert_eq!(partial_decryptions2.len(), n);

        let dmsg = decrypt_all(&partial_decryptions1, &partial_decryptions2, &ct, &crs);
        println!("Decrypted message: {:?}", dmsg);
        for i in 0..batch_size {
            assert_eq!(dmsg[i], msg[i]);
        }
        println!("Decryption successful!");
    }
}
