use merlin::Transcript;
use ark_ec::pairing::Pairing;
use ark_poly_commit::kzg10::*;
use ark_ff::PrimeField;
use ark_ff::BigInteger;
use ark_std::{start_timer, end_timer, marker::PhantomData};
use ark_serialize::CanonicalSerialize;

pub(crate) fn sample_random_challenge_from_transcript<E: Pairing>(transcript: &mut Transcript, label: &'static [u8]) -> E::ScalarField {
    // let time = start_timer!(|| format!("function: sample_random_challenge_from_transcript"));
    let byte_len = (E::ScalarField::MODULUS_BIT_SIZE as usize + 7) / 8;
    let mut buf = vec![0u8; byte_len];
    transcript.challenge_bytes(label, &mut buf);
    // end_timer!(time);
    E::ScalarField::from_le_bytes_mod_order(&buf)
}

pub(crate) fn sample_random_challenge_vector_from_transcript<E: Pairing>(transcript: &mut Transcript, label: &'static [u8], len: usize) -> Vec<E::ScalarField> {
    // let time = start_timer!(|| format!("function: sample_random_challenge_vector_from_transcript"));
    let mut res = Vec::with_capacity(len);
    for i in 0..len {
        let byte_len = (E::ScalarField::MODULUS_BIT_SIZE as usize + 7) / 8;
        let mut buf = vec![0u8; byte_len];
        transcript.challenge_bytes(label, &mut buf);
        res.push(E::ScalarField::from_le_bytes_mod_order(&buf))
    }
    // end_timer!(time);
    res
}

pub(crate) fn append_field_element_to_transcript<E: Pairing>(transcript: &mut Transcript, label: &'static [u8], value_to_append: &E::ScalarField) {
    // let time = start_timer!(|| format!("function: append_field_element_to_transcript"));
    let bigint = value_to_append.into_bigint();
    let bytes = bigint.to_bytes_le();
    transcript.append_message(label, &bytes);
    // end_timer!(time);
}

pub(crate) fn append_field_element_vector_to_transcript<E: Pairing>(transcript: &mut Transcript, label: &'static [u8], vector_to_append: &Vec<E::ScalarField>) {
    // let time = start_timer!(|| format!("function: append_field_element_to_transcript"));
    for item in vector_to_append {
    	let bigint = item.into_bigint();
    	let bytes = bigint.to_bytes_le();
    	transcript.append_message(label, &bytes);
    }
    // end_timer!(time);
}

pub(crate) fn append_commitment_to_transcript<E: Pairing>(transcript: &mut Transcript, label: &'static [u8], commitment: &Commitment<E>) {
    // let time = start_timer!(|| format!("function: append_commitment_to_transcript"));
    let mut buf = Vec::new();
    commitment.serialize_compressed(&mut buf).expect("serialization failed");
    transcript.append_message(label, &buf);
    // end_timer!(time);
}

pub(crate) fn append_commitment_to_transcript_with_index<E: Pairing>(transcript: &mut Transcript, label: &'static [u8], index: Option<usize>, commitment: &Commitment<E>) {
    // let time = start_timer!(|| format!("function: append_commitment_to_transcript"));
    let mut buf = Vec::new();
    if let Some(ind) = index {
        buf.extend_from_slice(&ind.to_le_bytes());
    }
    commitment.serialize_compressed(&mut buf).expect("serialization failed");
    transcript.append_message(label, &buf);
    // end_timer!(time);
}

pub(crate) fn fe_to_index<E: Pairing>(val: E::ScalarField) -> usize {
    let ind = val.into_bigint();
    let limbs = ind.as_ref();
    debug_assert!(limbs[1..].iter().all(|&w| w == 0));
    limbs[0] as usize
}
