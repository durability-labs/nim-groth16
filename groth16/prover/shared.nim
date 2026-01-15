
#
# Groth16 prover
#
# WARNING! 
# the points H in `.zkey` are *NOT* what normal people would think they are
# See <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#

{.push raises:[].}

import system
import taskpools
import constantine/math/arithmetic
import constantine/named/properties_fields

import groth16/bn128
import groth16/math/domain
import groth16/math/poly
import groth16/zkey_types
#import groth16/misc

import groth16/prover/types

#-------------------------------------------------------------------------------

proc randomMask*(): Mask = 
  # masking coeffs
  let r = randFr()
  let s = randFr()
  let mask = Mask(r: r, s: s)
  return mask

#-------------------------------------------------------------------------------

# computes the vectors A*z, B*z, C*z where z is the witness
func buildABC*( zkey: ZKey, witness: seq[Fr[BN254_Snarks]] ): ABC =
  let hdr: GrothHeader = zkey.header
  let domSize = hdr.domainSize

  var valuesAz = newSeq[Fr[BN254_Snarks]](domSize)
  var valuesBz = newSeq[Fr[BN254_Snarks]](domSize)

  for entry in zkey.coeffs:
    case entry.matrix 
      of MatrixA: valuesAz[entry.row] += entry.coeff * witness[entry.col]
      of MatrixB: valuesBz[entry.row] += entry.coeff * witness[entry.col]
      else: raise newException(AssertionDefect, "fatal error")

  var valuesCz = newSeq[Fr[BN254_Snarks]](domSize)
  for i in 0..<domSize:
    valuesCz[i] = valuesAz[i] * valuesBz[i]

  return ABC( valuesAz:valuesAz, valuesBz:valuesBz, valuesCz:valuesCz )

#-------------------------------------------------------------------------------
# quotient poly
#

# interpolates A,B,C, and computes the quotient polynomial Q = (A*B - C) / Z
func computeQuotientNaive*( abc: ABC ): Poly=
  let n = abc.valuesAz.len
  assert( abc.valuesBz.len == n )
  assert( abc.valuesCz.len == n )
  let D = createDomain(n)
  let polyA : Poly = polyInverseNTT( abc.valuesAz , D )
  let polyB : Poly = polyInverseNTT( abc.valuesBz , D )
  let polyC : Poly = polyInverseNTT( abc.valuesCz , D )
  let polyBig = polyMulFFT( polyA , polyB ) - polyC
  var polyQ   = polyDivideByVanishing(polyBig, D.domainSize)
  polyQ.coeffs.add( zeroFr )    # make it a power of two
  return polyQ

#---------------------------------------

# returns [ eta^i * xs[i] | i<-[0..n-1] ]
func multiplyByPowers*( xs: seq[Fr[BN254_Snarks]], eta: Fr[BN254_Snarks] ): seq[Fr[BN254_Snarks]] =
  let n = xs.len
  assert(n >= 1)
  var ys = newSeq[Fr[BN254_Snarks]](n)
  ys[0] = xs[0]
  if n >= 1: ys[1] = eta * xs[1]
  var spow = eta
  for i in 2..<n: 
    spow *= eta
    ys[i] = spow * xs[i]
  return ys

# interpolates a polynomial, shift the variable by `eta`, and compute the shifted values
func shiftEvalDomain*(
  values: seq[Fr[BN254_Snarks]],
  D: Domain,
  eta: Fr[BN254_Snarks] ): seq[Fr[BN254_Snarks]] =
  let poly : Poly = polyInverseNTT( values , D )
  let cs : seq[Fr[BN254_Snarks]] = poly.coeffs
  var ds : seq[Fr[BN254_Snarks]] = multiplyByPowers( cs, eta )
  return polyForwardNTT( Poly(coeffs:ds), D )

# Wraps shiftEvalDomain such that it can be called by Taskpool.spawn. The result
# is written to the output parameter. Has an unused return type because
# Taskpool.spawn cannot handle a void return type.
func shiftEvalDomainTask*(
  values: seq[Fr[BN254_Snarks]],
  D: Domain,
  eta: Fr[BN254_Snarks],
  output: ptr Isolated[seq[Fr[BN254_Snarks]]]): bool =

  output[] = isolate shiftEvalDomain(values, D, eta)

# computes the quotient polynomial Q = (A*B - C) / Z
# by computing the values on a shifted domain, and interpolating the result
# remark: Q has degree `n-2`, so it's enough to use a domain of size n
proc computeQuotientPointwise*( abc: ABC, pool: TaskPool ): Poly =
  let n    = abc.valuesAz.len
  assert( abc.valuesBz.len == n )
  assert( abc.valuesCz.len == n )

  let D    = createDomain(n)
  
  # (eta*omega^j)^n - 1 = eta^n - 1 
  # 1 / [ (eta*omega^j)^n - 1] = 1/(eta^n - 1)
  let eta   = createDomain(2*n).domainGen
  let invZ1 = invFr( smallPowFr(eta,n) - oneFr )

  var outputA1, outputB1, outputC1: Isolated[seq[Fr[BN254_Snarks]]]

  var taskA1 = pool.spawn shiftEvalDomainTask( abc.valuesAz, D, eta, addr outputA1 )
  var taskB1 = pool.spawn shiftEvalDomainTask( abc.valuesBz, D, eta, addr outputB1 )
  var taskC1 = pool.spawn shiftEvalDomainTask( abc.valuesCz, D, eta, addr outputC1 )

  discard sync taskA1
  discard sync taskB1
  discard sync taskC1

  let A1 = outputA1.extract()
  let B1 = outputB1.extract()
  let C1 = outputC1.extract()

  var ys : seq[Fr[BN254_Snarks]] = newSeq[Fr[BN254_Snarks]]( n )
  for j in 0..<n: ys[j] = ( A1[j]*B1[j] - C1[j] ) * invZ1
  let Q1 = polyInverseNTT( ys, D )
  let cs = multiplyByPowers( Q1.coeffs, invFr(eta) )

  return Poly(coeffs: cs)

#---------------------------------------

# Snarkjs does something different, not actually computing the quotient poly
# they can get away with this, because during the trusted setup, they
# replace the points encoding the values `delta^-1 * tau^i * Z(tau)` by 
# (shifted) Lagrange bases.
# see <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#
proc computeSnarkjsScalarCoeffs*( abc: ABC, pool: TaskPool ): seq[Fr[BN254_Snarks]] =
  let n    = abc.valuesAz.len
  assert( abc.valuesBz.len == n )
  assert( abc.valuesCz.len == n )
  let D    = createDomain(n)
  let eta  = createDomain(2*n).domainGen

  var outputA1, outputB1, outputC1: Isolated[seq[Fr[BN254_Snarks]]]

  var taskA1 = pool.spawn shiftEvalDomainTask( abc.valuesAz, D, eta, addr outputA1 )
  var taskB1 = pool.spawn shiftEvalDomainTask( abc.valuesBz, D, eta, addr outputB1 )
  var taskC1 = pool.spawn shiftEvalDomainTask( abc.valuesCz, D, eta, addr outputC1 )

  discard sync taskA1
  discard sync taskB1
  discard sync taskC1

  let A1 = outputA1.extract()
  let B1 = outputB1.extract()
  let C1 = outputC1.extract()

  var ys : seq[Fr[BN254_Snarks]] = newSeq[Fr[BN254_Snarks]]( n )
  for j in 0..<n: ys[j] = ( A1[j] * B1[j] - C1[j] ) 

  return ys

#-------------------------------------------------------------------------------
