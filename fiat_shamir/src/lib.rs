use std::io::Read;

use serde::{Deserialize, Serialize};
use serde_json::value::Serializer;
use sha3::{Shake256, digest::{Update, ExtendableOutput}};

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
#[serde(bound = "M: Clone + Serialize + for<'a> Deserialize<'a>")]
pub struct ProofStream<M>
where
{
    transcript : Vec<M>,
    #[serde(skip)]
    read_index : usize // We must consider only the transcript when serializing!
}

impl<M> Default for ProofStream<M>
where
    M: Serialize + Clone + for<'de> Deserialize<'de>
{
    fn default() -> Self {
        Self { transcript: Vec::new(), read_index: 0usize }
    }
}

impl<M> ProofStream<M>
where
    M: Serialize + Clone + for<'de> Deserialize<'de>
{
    /// Push simply adds a message to the sequence of messages in the transcript
    pub fn push (&mut self, v : M) {
        self.transcript.push(v)
    }

    /// Pulling equals reading, so we return the message at the current index and increment it
    pub fn pull (&mut self) -> M {
        assert!(self.read_index < self.transcript.len());

        let res = self.transcript[self.read_index].clone();
        self.read_index += 1;
        res
    }

    /// Computes the hash of the transcript from the point of view of the prover, i.e., of the whole transcript
    pub fn prover_fiat_shamir (&self) -> [u8; 32] {
        let mut hasher = Shake256::default();
        let str = match self.serialize(Serializer) {
            Err (e) => panic!("{}", e),
            Ok (res) => res.to_string()
        };

        hasher.update(str.as_bytes());

        let mut res = [0u8; 32];
        let _ = hasher.finalize_xof().read_exact(&mut res);

        res
    }

    /// Computes the hash of the transcript from the point of view of the verifier, i.e., just of the read messages
    pub fn verifier_fiat_shamir (&self) -> [u8; 32] {
        let mut hasher = Shake256::default();

        let verifier_pov = Self { transcript: self.transcript[0..self.read_index].to_vec(), read_index: self.read_index };

        let str = match verifier_pov.serialize(Serializer) {
            Err (e) => panic!("{}", e),
            Ok (res) => res.to_string()
        };

        hasher.update(str.as_bytes());

        let mut res = [0u8; 32];
        let _ = hasher.finalize_xof().read_exact(&mut res);

        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serialize_deserialize() {
        let mut ps1 = ProofStream::<String>::default();

        ps1.push(String::from("1"));
        ps1.push(String::from("2"));
        ps1.push(String::from("3"));
        ps1.push(String::from("4"));

        let serialized = serde_json::to_string(&ps1).unwrap();
        let mut ps2 : ProofStream<String> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(ps1.pull(), ps2.pull());
        assert_eq!(ps1.pull(), ps2.pull());
        assert_eq!(ps1.pull(), ps2.pull());

        assert_eq!(ps1.pull(), "4");
        assert_eq!(ps2.pull(), "4");

        assert_eq!(ps1.prover_fiat_shamir(), ps2.prover_fiat_shamir());
    }
}
