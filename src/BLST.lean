
namespace BLST

/--
BLST_ERROR
-/
inductive Error
  | Success
  | BadEncoding
  | PointNotOnCurve
  | PointNotInGroup
  | AggrTypeMismatch
  | VerifyFail
  | PkIsInfinity
  | BadScalar

private constant ScalarP : NonemptyType

def Scalar := ScalarP.type

instance : Nonempty Scalar := ScalarP.property

namespace Scalar

@[extern "lean_blst_scalar_from_uint32"]
constant fromUInt32 (a : { arr : Array UInt32 // arr.size = 8 }) : Scalar

end Scalar

private constant FrP : NonemptyType

def Fr := FrP.type

instance : Nonempty Fr := FrP.property

private constant FpP : NonemptyType

def Fp := FpP.type

instance : Nonempty Fp := FpP.property

end BLST
