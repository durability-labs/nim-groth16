
import std/strutils
import std/times
import std/options
import std/random
import std/syncio

import taskpools

import constantine/named/properties_fields

# import groth16/bn128
import groth16/zkey_types
import groth16/files/witness
import groth16/misc
import groth16/files/export_json

import groth16/partial/types
import groth16/partial/precalc
import groth16/partial/finish

import groth16/prover
import groth16/prover/shared
import groth16/verifier

#-------------------------------------------------------------------------------

#[
proc testProveAndVerify*( zkey_fname, wtns_fname: string): (VKey,Proof) = 

  echo("parsing witness & zkey files...")
  let witness = parseWitness( wtns_fname)
  let zkey    = parseZKey( zkey_fname)

  echo("generating proof...")
  let start = cpuTime()
  let proof = generateProof( zkey, witness )
  let elapsed = cpuTime() - start
  echo("proving took ",seconds(elapsed))

  echo("verifying the proof...")
  let vkey = extractVKey( zkey)
  let ok   = verifyProof( vkey, proof )
  echo("verification succeeded = ",ok)

  return (vkey,proof)
]#

#-------------------------------------------------------------------------------

proc sanityCheckPartialProofs*( zkey: ZKey, wtns: Witness, pool: Taskpool, printTimings: bool) =

  let witness = wtns.values
  let M = witness.len

  var partial_mask:    seq[bool] = newSeq[bool]( M )
  var partial_witness: seq[Option[Fr[BN254_Snarks]]] = newSeq[Option[Fr[BN254_Snarks]]]( M )

  # generate randomized partial witness 
  partial_mask[0]    = true
  partial_witness[0] = some(witness[0])
  var count = 0 
  for i in 1..<M:
    let b : bool = rand(bool)
    partial_mask[i] = b
    if b:
      partial_witness[i] = some(witness[i])
      count += 1
    else:
      partial_witness[i] = none(Fr[BN254_Snarks])

  echo "\nrandomized a partial witness of size " & $(count) & " out of " & $(M)
  let partial_wtns = PartialWitness(values: partial_witness )

  let mask = randomMask()

  var fullProof : Proof
  withMeasureTime(true,"\ngenerating the full proof"):
    fullProof = generateProofWithMask( zkey, wtns, mask, pool, printTimings )
  writeProof(stdout,fullProof)

  let vkey = extractVKey(zkey)
  echo "verifying the full proof succeeds = " & $verifyProof(vkey, fullProof)

  var partialProof : PartialProof
  withMeasureTime(true,"\ngenerating the partial proof"):
    partialProof = generatePartialProof( zkey, partial_wtns, pool, printTimings )

  var finishedProof : Proof
  withMeasureTime(true,"\nfinishing the partial proof"):
    finishedProof = finishPartialProofWithMask( zkey, wtns, partialProof, mask, pool, printTimings )
  writeProof(stdout,finishedProof)

  echo "verifying the finished proof succeeds = " & $verifyProof(vkey, finishedProof)

  if (not isEqualProof(fullProof, finishedProof)):
    echo "PROBLEM! the two proofs DIFFER!!!"
  else:
    echo "OK. the two proofs agree"
  
#-------------------------------------------------------------------------------

