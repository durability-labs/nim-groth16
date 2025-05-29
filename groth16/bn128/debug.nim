#
# the `alt-bn128` elliptic curve
#
# See for example <https://hackmd.io/@jpw/bn254>
#
# p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
# r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
#
# equation: y^2 = x^3 + 3
#

import pkg/constantine/math/io/io_fields
import pkg/constantine/named/properties_fields
import pkg/constantine/math/extension_fields/towers

import groth16/bn128/fields
import groth16/bn128/curves
import groth16/bn128/io

#-------------------------------------------------------------------------------

proc debugPrintFp*(prefix: string, x: Fp[BN254_Snarks]) =
  echo(prefix & toDecimalFp(x))

proc debugPrintFp2*(prefix: string, z: Fp2[BN254_Snarks]) =
  echo(prefix & " 1 ~> " & toDecimalFp(z.coords[0]))
  echo(prefix & " u ~> " & toDecimalFp(z.coords[1]))

proc debugPrintFr*(prefix: string, x: Fr[BN254_Snarks]) =
  echo(prefix & toDecimalFr(x))

proc debugPrintFrSeq*(msg: string, xs: seq[Fr[BN254_Snarks]]) =
  echo "---------------------"
  echo msg
  for x in xs:
    debugPrintFr( "  " , x )

proc debugPrintG1*(msg: string, pt: G1) =
  echo(msg & ":")
  debugPrintFp( " x = ", pt.x )
  debugPrintFp( " y = ", pt.y )

proc debugPrintG2*(msg: string, pt: G2) =
  echo(msg & ":")
  debugPrintFp2( " x = ", pt.x )
  debugPrintFp2( " y = ", pt.y )

#-------------------------------------------------------------------------------

