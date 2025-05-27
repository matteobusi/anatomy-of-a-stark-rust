use blake2::{Blake2b512, Digest};
use crypto_bigint::{NonZero, I256, U512};

use fiat_shamir::ProofStream;
use finite_fields::IntPG;
use merkle_tree::{MerkleTree, HL};
use polynomials::{degree::Degree, polynomial::Polynomial};

use serde::{Deserialize, Serialize};
use serde_with::{serde_as, Bytes};


// This structure represents the FRI on a domain D of size `domain_length` with generator `omega`
// and expansion factor. Follows "The Anatomy of a STARK" tutorial
#[derive(PartialEq,Debug)]
#[allow(dead_code)]
struct Fri {
    offset : IntPG,
    // The generator of the domain D
    omega : IntPG,
    // The length of the domain D
    domain_length : usize,
    // The expansion factor, the reciprocal of the code's rate. Integer because we do not like floats :)
    expansion_factor : u128,
    // Number of co-linearity tests
    num_colinearity_tests : usize
}

// The following structure represents the data inside the proof stream
#[serde_as]
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Debug)]
struct HashType(
    #[serde_as (as = "Bytes")]
    [u8; HL]
);

#[serde_as]
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Debug)]
#[allow(non_camel_case_types)]
enum ProofObj {
    MTRoot (HashType),
    CW (Vec<IntPG>),
    CWTriple (IntPG, IntPG, IntPG),
    MTAuthPath (Vec<HashType>)
}

impl Fri {
    // Creates a new Fri with the specified parameters
    pub fn new (offset : IntPG, omega : IntPG, domain_length : usize, expansion_factor : u128, num_colinearity_tests : usize) -> Self {
        Fri { offset, omega, domain_length, expansion_factor, num_colinearity_tests }
    }

    // Computes the number of rounds
    pub fn num_rounds (&self) -> usize {
        let mut codeword_len = self.domain_length;
        let mut num_rounds = 0usize;

        // The first condition makes the loop terminate in less than floor(log_2 (codeword_len)) steps,
        // the second condition is for early termination, as explained in the Anatomy:
        //      > Specifically, it terminates as soon as the number of colinearity checks is more than one quarter the
        //      > length of the working codeword. If there were another step, more than half the points in the codeword
        //      > would be a C point in some colinearity test. At this point, the entropy of a random selection of
        //      > indices drops significantly.
        while codeword_len as u128 > self.expansion_factor && 4 * self.num_colinearity_tests < codeword_len {
            codeword_len /= 2;
            num_rounds += 1;
        }

        num_rounds
    }

    pub fn eval_domain (&self) -> Vec<IntPG> {
        (0..self.domain_length).map(|i| IntPG::from(i as i128)).map(|i| self.offset * (self.omega^i)).collect()
    }

    pub fn prove (&self, codeword : &[IntPG], ps : &mut ProofStream<ProofObj>) -> Vec<usize> {
        assert_eq! (codeword.len(), self.domain_length);

        // The prove phase has 2 sub-phases:
        //      1. Commitment: the prover sends Merkle roots of codewords to the verifier, and the verifier supplies alpha, i.e., their random element of IntPG for the split-and-fold procedure
        let codewords = self.commit (codeword, ps);

        println!("codewords: {:?}", codewords);

        //      2. Query: the verifier selects the leaf indexes, the prover opens them for verifier's co-linearity checks
        let top_level_indexes = self.sample_indexes (ps.prover_fiat_shamir(),  codewords[0].len()/2,  codewords[codewords.len()-1].len(), self.num_colinearity_tests);
        let mut indexes = top_level_indexes.clone();

        for i in 0..(codewords.len()-1) {
            indexes = indexes.iter().map(|index| index % (codewords[i].len()/2)).collect();
            self.query (&codewords[i], &codewords[i+1], &indexes, ps);
        }

        top_level_indexes
    }

    fn commit (&self, codeword: &[IntPG], ps : &mut ProofStream<ProofObj>) -> Vec<Vec<IntPG>> {
        #[allow(non_snake_case)]
        let TWO = finite_fields::constant(I256::from(2));

        let mut omega = self.omega;
        let mut offset = self.offset;
        let mut codewords: Vec<Vec<IntPG>> = Vec::new();

        let mut codeword = codeword.to_vec();

        for r in 0..self.num_rounds() {
            #[allow(non_snake_case)]
            let N = codeword.len();
            assert_eq! (omega ^ (N - 1).into(), omega.inverse());

            let cwh: Vec<[u8; 64]> = Self::codeword_to_vec(&codeword.to_vec()).iter().map(|v| v.0).collect();
            let mt = MerkleTree::new(&cwh);

            // Now compute the root of mt and push it to the stream
            let root = HashType(mt.commit());
            ps.push(ProofObj::MTRoot(root));

            // If this is not the last round, prepare the values for the next
            if r < self.num_rounds() - 1 {
                // Obtain the challenge
                let alpha : IntPG = finite_fields::sample(&ps.prover_fiat_shamir());

                // Collect the codeword for later use
                codewords.push(codeword.to_vec());

                // And finally, split and fold
                codeword = (0..N/2).map(|i| TWO.inverse() * (
                        ((finite_fields::ONE + alpha / (offset * (omega^i.into())))*codeword[i]) +
                        ((finite_fields::ONE - alpha / (offset * (omega^i.into())))*codeword[N/2 + i]))).collect();

                omega ^= 2.into();
                offset ^= 2.into();
            }
        }

        // Send and collect the last codeword
        ps.push(ProofObj::CW(codeword.clone()));
        codewords.push(codeword.clone());

        codewords
    }

    fn query (&self, current_cw : &Vec<IntPG>, next_cw : &Vec<IntPG>, c_indexes : &[usize], ps : &mut ProofStream<ProofObj>) -> Vec<usize> {
        let a_indexes: Vec<usize> = c_indexes.to_vec().clone();
        let b_indexes: Vec<usize> = c_indexes.iter().map(|i| i + current_cw.len()/2).collect();

        // Reveal the leaves
        for s in 0..self.num_colinearity_tests {
            let po = ProofObj::CWTriple (current_cw[a_indexes[s]], current_cw[b_indexes[s]], next_cw[c_indexes[s]]);
            ps.push(po);
        }

        // Reveal the authentication paths
        let mt_current = MerkleTree::new(&Self::codeword_to_vec(current_cw).iter().map(|v| v.0).collect::<Vec<[u8; HL]>>());
        let mt_next = MerkleTree::new(&Self::codeword_to_vec(next_cw).iter().map(|v| v.0).collect::<Vec<[u8; HL]>>());
        for s in 0..self.num_colinearity_tests {
            ps.push (ProofObj::MTAuthPath(mt_current.open(a_indexes[s]).iter().map(|&i| HashType(i)).collect()));
            ps.push (ProofObj::MTAuthPath(mt_current.open(b_indexes[s]).iter().map(|&i| HashType(i)).collect()));
            ps.push (ProofObj::MTAuthPath(mt_next.open(c_indexes[s]).iter().map(|&i| HashType(i)).collect()));
        }

        [a_indexes, b_indexes].concat()
    }

    fn sample_indexes (&self, seed : [u8; 32], size : usize, reduced_size : usize, number : usize) -> Vec<usize> {
        // Basic sanity checks, see if the entropy is enough
        assert! (number <= 2*reduced_size);
        assert! (number <= reduced_size);

        let mut indexes = vec![];
        let mut reduced_indexes = vec![];
        let mut counter = 0usize;

        while indexes.len() < number {
            let h = Self::hash ([Vec::from(seed), Vec::from(counter.to_le_bytes())].concat()); // Here we concatenate the seed with the counter and then hash the result --- this is a bit different from the Anatomy, but should be secure nonetheless
            let index = Self::sample_index (HashType(h), size);
            let reduced_index = index % reduced_size;
            counter += 1;
            if !reduced_indexes.contains(&reduced_index) {
                indexes.push(index);
                reduced_indexes.push(reduced_index);
            }
        }

        indexes
    }

    fn sample_index ( data : HashType, size : usize) -> usize {
        // We want to create a number of HL=64 bytes, i.e., 64*8 = 512bits
        let mut acc : U512 = U512::ZERO;
        let m = NonZero::new(U512::from(size as u64)).unwrap();

        for b in data.0 {
            acc = acc.shl(8).bitxor(&U512::from(b as u16));
        }

        let res = acc.rem(&m).to_le_bytes();

        // We expect the bytes after the 8th to be all 0
        for &i in res.iter().skip(8) {
            assert_eq! (i, 0u8);
        }

        // The first 8 bytes are instead the resulting index
        usize::from_le_bytes([res[0], res[1], res[2], res[3], res[4], res[5], res[6], res[7]])
    }

    /// This internal function hashes a codeword into a vec of tuples of bytes to store them in the Merkle Tree
    fn codeword_to_vec (codeword : &Vec<IntPG>) -> Vec<HashType> {
        let mut res: Vec<HashType> = Vec::new();
        for cw in codeword {
            let codeword_str = serde_json::to_string(&cw).unwrap();
            let mut hasher = Blake2b512::new();
            hasher.update(codeword_str.as_bytes());
            res.push(HashType(hasher.finalize().into()))
        }

        res
    }

    /// Internal function for hashing stuff
    fn hash (data : Vec<u8>) -> [u8; HL] {
        let mut hasher = Blake2b512::new();
        hasher.update(data);
        hasher.finalize().into()
    }

    /// The verify function, returns `Ok(())` if the given polynomial values match the proof stream, `Err` if not.
    /// Panics upon malformed elements in the proof stream.
    fn verify (&self, ps : &mut ProofStream<ProofObj>, polynomial_values : &mut Vec<(usize, IntPG)>) -> Result<(), &'static str> {
        let mut polynomial_values = polynomial_values.to_vec();

        let mut omega = self.omega;
        let mut offset = self.offset;
        // Extract all roots and alphas from the proof stream
        let mut roots = Vec::new();
        let mut alphas : Vec<IntPG> = Vec::new();

        for _ in 0..self.num_rounds() {
            roots.push (ps.pull());
            alphas.push (finite_fields::sample(&ps.verifier_fiat_shamir()));
        }

        // Extract roots from corresponding proof objects
        let roots : Vec<[u8; HL]> = roots.iter().map(|r| match r {
            ProofObj::MTRoot(h) => h.0,
            _ => panic!("Expected a MTRoot, found {:?}", r)
        } ).collect();

        // And extract the last codeword from the Proof stream, which should be the result of the commitment in the Merkle Tree
        let last_cw = ps.pull();

        match last_cw {
            ProofObj::CW(last_cw) => {
                let last_cw_mt = MerkleTree::new(&Self::codeword_to_vec(&last_cw).iter().map(|v| v.0).collect::<Vec<[u8; HL]>>());
                // Check 1: make sure the last codeword is well-formed
                if *roots.last().unwrap() != last_cw_mt.commit() {
                    return Result::Err("Last codeword is not well formed");
                }

                let degree = (last_cw.len() as u128 / self.expansion_factor) - 1;
                let mut last_omega = omega;
                let mut last_offset = offset;
                for _ in 0..(self.num_rounds()-1) {
                    last_omega ^= IntPG::from(2);
                    last_offset ^= IntPG::from(2);
                }

                // Check 2: last_omega must have the correct order
                if last_omega.inverse() != last_omega ^ IntPG::from(last_cw.len() - 1) {
                    return Result::Err("Omega does not have the right order");
                }

                // Check 3: re-evaluate the codeword, it must match the original
                let last_domain : Vec<_> = (0..last_cw.len()).map(|i| last_offset * (last_omega ^ IntPG::from(i))).collect();

                println!("last_domain:\n{:?}", last_domain);
                println!("last_cw:\n{:?}", last_cw);
                // let last_points = last_domain.clone().into_iter().zip(last_cw.clone()).collect();
                let poly = Polynomial::interpolate(&last_domain, &last_cw);

                if poly.evaluate_domain(&last_domain) != last_cw {
                    return Result::Err("Re-evaluated codeword does not match the original");
                }

                // Check 4: check that the codeword corresponds to a polynomial of low enough degree
                if poly.degree() > Degree::Poly(degree) {
                    return Result::Err("Last codeword does not correspond to a low enough degree polynomial!");
                }

                let top_level_indexes = self.sample_indexes(ps.verifier_fiat_shamir(), self.domain_length >> 1, self.domain_length >> (self.num_rounds() - 1), self.num_colinearity_tests);

                // Check 5: for every round check consistency of subsequent layers
                for r in 0..(self.num_rounds()-1) {
                    let c_indexes : Vec<usize> = top_level_indexes.iter().map(|index| index % (self.domain_length >> (r+1))).collect();

                    let a_indexes : Vec<usize> = c_indexes.clone();
                    let b_indexes : Vec<usize> = a_indexes.iter().map(|index| index + (self.domain_length >> (r+1))).collect();

                    let mut aa : Vec<IntPG> = vec![];
                    let mut bb : Vec<IntPG> = vec![];
                    let mut cc : Vec<IntPG> = vec![];

                    // check colinarity...
                    for s in 0..self.num_colinearity_tests {
                        match ps.pull() {
                            ProofObj::CWTriple(ay, by , cy) => {
                                aa.push(ay);
                                bb.push(by);
                                cc.push(cy);

                                // Store top layer values for later
                                if r == 0 {
                                    polynomial_values.push((a_indexes[s], ay));
                                    polynomial_values.push((b_indexes[s], by));
                                }

                                // now the colinarity check
                                let ax = offset * (omega ^ IntPG::from(a_indexes[s]));
                                let bx = offset * (omega ^ IntPG::from(b_indexes[s]));
                                let cx = alphas[r];

                                if !Polynomial::test_colinearity (&vec![(ax, ay), (bx, by), (cx, cy)]) {
                                    return Result::Err("Colinearity check failed!");
                                }
                            },
                            _ => {
                                panic!("Expected a CWTriple in the proof streamm found {:?}", last_cw)
                            }
                        }
                    }

                    // verify authentication paths...
                    let aa_mt : Vec<[u8; HL]> = Self::codeword_to_vec(&aa).iter().map(|v| v.0).collect();
                    let bb_mt : Vec<[u8; HL]> = Self::codeword_to_vec(&bb).iter().map(|v| v.0).collect();
                    let cc_mt : Vec<[u8; HL]> = Self::codeword_to_vec(&cc).iter().map(|v| v.0).collect();

                    for i in 0..self.num_colinearity_tests {
                        match ps.pull() {
                            ProofObj::MTAuthPath (path) => {
                                let path: Vec<[u8; 64]> = path.iter().map(|n| n.0).collect();
                                // The proof object has the right shape, let's verify it
                                if !MerkleTree::verify(&roots[r+1], a_indexes[i], &path, &aa_mt[i]) {
                                    return Result::Err("Merkle auth failed for aa");
                                }

                                if !MerkleTree::verify(&roots[r+1], b_indexes[i], &path, &bb_mt[i]) {
                                    return Result::Err("Merkle auth failed for bb");
                                }

                                if !MerkleTree::verify(&roots[r+1], c_indexes[i], &path, &cc_mt[i]) {
                                    return Result::Err("Merkle auth failed for cc");
                                }
                            },
                            po => {
                                panic!("Expected a MTAuthPath in the proof stream, found {:?}", po);
                            }
                        };
                    }

                    omega ^= IntPG::from(2);
                    offset ^= IntPG::from(2);
                }
            },
            _ => { panic!("Last codeword is not well formed (Vec, but different)"); }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use finite_fields::IntPG;

    #[test]
    fn test_fri_valid () {
        let degree = 63;
        let expansion_factor = 4;
        let num_colinearity_tests = 17;

        let initial_codeword_len = (degree + 1) * expansion_factor;
        let mut log_codeword_len = 0;
        let mut codeword_len = initial_codeword_len as usize;
        while codeword_len > 1 {
            codeword_len /= 2;
            log_codeword_len += 1;
        }

        assert_eq! (1 << log_codeword_len, initial_codeword_len);

        let omega = finite_fields::primitive_nth_root(initial_codeword_len);
        let generator = finite_fields::constant(finite_fields::SIGNED_G);

        assert_eq! (omega ^ IntPG::from(1 << log_codeword_len), finite_fields::ONE);
        assert_ne! (omega ^ IntPG::from(1 << (log_codeword_len-1)), finite_fields::ONE);

        let fri = Fri::new(generator, omega, initial_codeword_len as usize, expansion_factor as u128, num_colinearity_tests);

        let coefficients : Vec<_> = (0..degree+1).map(|i| finite_fields::constant(I256::from(i))).collect();
        let poly = Polynomial::new(&coefficients);
        let domain = (0..initial_codeword_len).map(|i| omega ^ finite_fields::constant(I256::from(i))).collect::<Vec<IntPG>>();

        let codeword = poly.evaluate_domain(&domain);

        // println!("{:?}", codeword);

        let mut ps = ProofStream::<ProofObj>::default();

        fri.prove(&codeword, &mut ps);
        let mut points = vec![];
        let verdict = fri.verify(&mut ps, &mut points);

        match verdict {
            Ok(()) => {
                for (x, y) in points {
                    let v = omega^finite_fields::constant(I256::from(x as i128));
                    assert_eq!(poly.evaluate(&v), y, "Polynomial evaluates to the wrong value!");
                }
            },
            Err(_) => panic!("Proof rejected but it should be valid!")
        }

    }

    #[test]
    fn test_fri_invalid () {
        let degree = 63;
        let expansion_factor = 4;
        let num_colinearity_tests = 17;

        let initial_codeword_len = (degree + 1) * expansion_factor;
        let mut log_codeword_len = 0;
        let mut codeword_len = initial_codeword_len as usize;
        while codeword_len > 1 {
            codeword_len /= 2;
            log_codeword_len += 1;
        }

        assert_eq! (1 << log_codeword_len, initial_codeword_len);

        let omega = finite_fields::primitive_nth_root(initial_codeword_len);
        let generator = finite_fields::constant(finite_fields::SIGNED_G);

        assert_eq! (omega ^ IntPG::from(1 << log_codeword_len), finite_fields::ONE);
        assert_ne! (omega ^ IntPG::from(1 << (log_codeword_len-1)), finite_fields::ONE);

        let fri = Fri::new(generator, omega, initial_codeword_len as usize, expansion_factor as u128, num_colinearity_tests);

        let coefficients : Vec<_> = (0..degree+1).map(|i| finite_fields::constant(I256::from(i))).collect();
        let poly = Polynomial::new(&coefficients);
        let domain = (0..initial_codeword_len).map(|i| omega ^ finite_fields::constant(I256::from(i))).collect::<Vec<IntPG>>();

        let mut codeword = poly.evaluate_domain(&domain);

        // println!("{:?}", codeword);

        // Disturb the stream to invalidate the proof
        let mut ps = ProofStream::<ProofObj>::default();
        for i in 0..degree/3 {
            codeword[i as usize] = finite_fields::ZERO;
        }

        fri.prove(&codeword, &mut ps);
        let mut points = vec![];

        let verdict = fri.verify(&mut ps, &mut points);

        if let Ok(()) = verdict {
            panic!("Proof accepted but it should NOT be valid!")
        }
    }
}
