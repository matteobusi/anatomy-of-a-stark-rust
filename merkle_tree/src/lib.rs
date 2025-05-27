//! This is a simple implementation of the Merkle tree
use blake2::{Blake2b512, Digest};

pub const HL : usize = 64;

/// This is the data structure representing the Merkle tree
/// We conflate data and hashes because we assume that provided data are actually just hashes of the right kind :)
#[derive(Debug, PartialEq, Eq)]
pub enum MerkleTree {
    Leaf { data: [u8; HL]},
    Node { l : Box<MerkleTree>, leaves_count : usize, data: [u8; HL], r: Box<MerkleTree> },
}

impl MerkleTree {
    /// Creates the Merkle tree from the given list of leaves (its length must be a power of two!)
    pub fn new (leaves : &[[u8; HL]]) -> MerkleTree {
        assert!(leaves.len() & (leaves.len()-1) == 0); // The number of leaves must be a power of two

        if leaves.len() == 1 {
            MerkleTree::Leaf { data : leaves[0] }
        } else {
            let (l, r) = (MerkleTree::new(&leaves[..leaves.len()/2]), MerkleTree::new(&leaves[leaves.len()/2..]));

            let (lc, rc) = (l.commit(), r.commit());

            MerkleTree::Node { l: Box::from(l), leaves_count : leaves.len(), data: MerkleTree::hash(&[lc, rc].concat()), r: Box::from(r) }
        }
    }

    /// Returns the commitment, i.e., the data stored in the root of the Merkle tree
    pub fn commit (&self) -> [u8; HL] {
        match self {
            MerkleTree::Leaf { data } | MerkleTree::Node { l: _, leaves_count: _, data, r: _ } => *data
        }
    }

    /// Returns the authentication path of the given leaf index, i.e., the (ordered) vector of hashes of the nodes needed to compute the commitment
    pub fn open (&self, index : usize) -> Vec<[u8; HL]> {
        if let MerkleTree::Node { l: _, leaves_count, data: _, r: _ } = self {
            assert!(index < *leaves_count)
        } else {
            assert!(index == 0);
        }

        match self {
            // If we are in an internal node and the requested index is on the left, open the left path
            // recursively and return its concatenation with the commit of the right subtree
            MerkleTree::Node { l, leaves_count, data: _, r }
                if index < leaves_count/2 => [l.open(index), vec![r.commit()]].concat(),
            // Similarly if the index is on the right (remember to update the index!)
            MerkleTree::Node { l, leaves_count, data: _, r } =>
                [r.open(index - *leaves_count/2), vec![l.commit()]].concat(),
            // A leaf has empty authentication path
            MerkleTree::Leaf { data: _ } => vec![]
        }
    }

    /// Checks that the given `proof` (i.e., a candidate authentication path) matches the given `leaf`
    /// and index in the tree
    pub fn verify (root : &[u8; HL], index : usize, proof : &[[u8; HL]], leaf : &[u8; HL]) -> bool {
        // Notice that the following piece of code works because of the following fact:
        //
        // Fact 1. verify(...) holds for the given parameters iff verify(...) holds for a Merkle tree with
        // the second-to-last level of nodes as leaves with hashes unchanged, i.e., the target leaf
        // hash is now the hash of the old sibling in the right order (depending on the parity of the index),
        // and target index halved.
        //
        // More intuitively, the code maintains the (initially valid) invariant that `leaf` is the hash of
        // the sibling of the node whose hash appears in `proof[0]`.
        // Inductively, let the original index value be `I`, this means that after `log_2(I)` (i.e., when current
        // index equals `0`) to verify we just need to check that `root = hash( h_{[0..I/2)} || h_{[I/2..I)})`
        // matches `hash(leaf || proof[0])` which, by the above invariant, is `hash( h_{[0..I/2)} || h_{[I/2..I)})`.
        assert!(index < (1 << proof.len()));

        if proof.len() == 1 && index == 0 {
            *root == MerkleTree::hash(&[*leaf, proof[0]].concat())
        } else if proof.len() == 1 && index > 0 {
            *root == MerkleTree::hash(&[proof[0], *leaf].concat())
        } else if index % 2 == 0 {
            MerkleTree::verify(root, index/2, &proof[1..], &MerkleTree::hash(&[*leaf, proof[0]].concat()))
        } else {
            MerkleTree::verify(root, index/2, &proof[1..], &MerkleTree::hash(&[proof[0], *leaf].concat()))
        }
    }

    /// Internal function to simplify the hashing of data
    fn hash (data : &Vec<u8>) -> [u8; HL] {
        let mut hasher = Blake2b512::new();
        hasher.update(data);
        hasher.finalize().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_honest_proof_ok() {
        let leaves = [8u8, 99u8, 7u8, 21u8, 42u8, 4u8, 1u8, 11u8].map(|x| MerkleTree::hash(&[x].to_vec()));

        // Build the tree with correct leaves ...
        let tree = MerkleTree::new(&leaves);
        let root = tree.commit();

        // ... AND verify with CORRECT ones!
        for (i, leaf) in leaves.iter().enumerate() {
            let proof = tree.open(i);
            assert!(MerkleTree::verify(&root, i, &proof, leaf))
        }
    }

    #[test]
    fn test_fake_proof_fail() {
        let leaves = [8u8, 99u8, 7u8, 21u8, 42u8, 4u8, 1u8, 11u8].map(|x| MerkleTree::hash(&[x].to_vec()));
        let fake_leaves = [5u8, 7u8, 29u8, 33u8, 92u8, 48u8, 11u8, 1u8].map(|x| MerkleTree::hash(&[x].to_vec()));

        // Build the tree with correct leaves ...
        let tree = MerkleTree::new(&leaves);
        let root = tree.commit();

        // ... AND verify with FAKE ones!
        // Notice how the index matters, an existing leaf value with wrong index is rightfully deemed as fake!
        for (i, leaf) in fake_leaves.iter().enumerate() {
            let proof = tree.open(i);
            assert!(!MerkleTree::verify(&root, i, &proof, leaf))
        }
    }
}
