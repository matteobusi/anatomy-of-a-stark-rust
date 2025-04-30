use finite_fields::IntPG;

// This structure represents the FRI on a domain D of size `domain_length` with generator `omega`
// and expansion factor. Follows "The Anatomy of a STARK" tutorial
#[derive(PartialEq,Debug)]
struct Fri {
    offset : IntPG,
    // The generator of the domain D
    omega : IntPG,
    // The length of the domain D
    domain_length : usize,
    // The expansion factor, the reciprocal of the code's rate. Integer because we do not like floats :)
    expansion_factor : u128,
    // Number of co-linearity tests
    num_colinearity_tests : u128
}

impl Fri {
    // Creates a new Fri with the specified parameters
    pub fn new (offset : IntPG, omega : IntPG, domain_length : usize, expansion_factor : u128, num_colinearity_tests : u128) -> Self {
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
        while codeword_len as u128 > self.expansion_factor && 4 * self.num_colinearity_tests < codeword_len as u128 {
            codeword_len /= 2;
            num_rounds += 1;
        }

        num_rounds
    }

    pub fn eval_domain (&self) -> Vec<IntPG> {
        (0..self.domain_length).map(|i| IntPG::from(i as i128)).map(|i| self.offset * (self.omega^i)).collect()
    }

    pub fn prove (&self, codeword : IntPG, proofstream : Vec<IntPG>) -> Vec<usize> {

    }
}
