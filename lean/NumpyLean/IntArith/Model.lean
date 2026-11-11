import NumpyLean.Common.Intp

/-
Models of the integer arithmetic loops of NumPy 2.5.4 for the ten fixed-width integer types int8 to int64 and uint8 to uint64.

Two code paths are modelled for each operation. The array path is the ufunc inner loop in `_core/src/umath/loops_arithmetic.dispatch.c.src`, `loops_modulo.dispatch.c.src`, `loops.c.src` and `loops_autovec.dispatch.c.src`, with the helpers from `_core/src/npymath/npy_math_internal.h.src`. The scalar path is the Python operator on NumPy scalars in `_core/src/umath/scalarmath.c.src`.

Values are kept as `Int`. C signed overflow is undefined behaviour, and the model assumes two's complement wrap at every point where the C code can overflow, which is what the arm64 and x86-64 builds do. The wrap is written as `IntTy.wrap` so that it is visible.

The floating point status flags that the loops set are modelled as `Flags`. NumPy turns them into a `RuntimeWarning` or a `FloatingPointError` after the loop, according to `np.errstate`.
-/
namespace NumpyLean.IntArith

/-- One of the ten integer dtypes, given by its bit width and signedness. -/
structure IntTy where
  bits : Nat
  signed : Bool
  deriving Repr, DecidableEq

namespace IntTy

def i8 : IntTy := ⟨8, true⟩
def i16 : IntTy := ⟨16, true⟩
def i32 : IntTy := ⟨32, true⟩
def i64 : IntTy := ⟨64, true⟩
def u8 : IntTy := ⟨8, false⟩
def u16 : IntTy := ⟨16, false⟩
def u32 : IntTy := ⟨32, false⟩
def u64 : IntTy := ⟨64, false⟩

/-- `NPY_MIN_<TYPE>`. -/
def minVal (t : IntTy) : Int := if t.signed then -((2 : Int) ^ (t.bits - 1)) else 0

/-- `NPY_MAX_<TYPE>`. -/
def maxVal (t : IntTy) : Int := if t.signed then (2 : Int) ^ (t.bits - 1) - 1 else (2 : Int) ^ t.bits - 1

/-- The C conversion of an integer to this type, assuming two's complement wrap. -/
def wrap (t : IntTy) (x : Int) : Int := if t.signed then wrapSigned t.bits x else wrapUnsigned t.bits x

def inRange (t : IntTy) (x : Int) : Bool := t.minVal ≤ x && x ≤ t.maxVal

/--
The width of the C type that `npy_gcd` and `npy_lcm` compute in. `loops.c.src:564` calls `npy_gcd` (on `npy_int`) for BYTE, SHORT and INT and `npy_gcdl` or `npy_gcdll` (on 64-bit `npy_long` or `npy_longlong`) for LONG and LONGLONG. The unsigned loop at `loops.c.src:583` does the same with `npy_gcdu`, `npy_gcdul` and `npy_gcdull`. The model assumes the LP64 data model of macOS and Linux, where `long` has 64 bits.
-/
def gcdWidth (t : IntTy) : Nat := if t.bits ≤ 32 then 32 else 64

end IntTy

/-- The floating point status flags that an integer loop can set. -/
structure Flags where
  divbyzero : Bool := false
  overflow : Bool := false
  deriving Repr, DecidableEq

namespace Flags
def clear : Flags := {}
/-- `npy_set_floatstatus_divbyzero()`. -/
def dbz : Flags := { divbyzero := true }
/-- `npy_set_floatstatus_overflow()`. -/
def ovf : Flags := { overflow := true }
def union (a b : Flags) : Flags := ⟨a.divbyzero || b.divbyzero, a.overflow || b.overflow⟩
end Flags

/-! ## floor_divide -/

/--
`floor_div_@TYPE@` at `_core/src/umath/loops_arithmetic.dispatch.c.src:346` for signed types, and the unsigned `@TYPE@_divide` loop body at `loops_arithmetic.dispatch.c.src:480-487`. `floor_divide` is defined as `divide` for integers at `loops.c.src:429`.

The SIMD path `simd_divide_by_scalar_contig` at `loops_arithmetic.dispatch.c.src:46` is taken for a contiguous array divided by a nonzero broadcast scalar. It is modelled separately as `floorDivSimdLane` below.
-/
def floorDivArray (t : IntTy) (n d : Int) : Int × Flags :=
  if t.signed then
    if d == 0 || (n == t.minVal && d == -1) then
      if d == 0 then (0, .dbz) else (t.minVal, .ovf)
    else
      -- C `/` truncates toward zero.
      let r := Int.tdiv n d
      -- `r * d` cannot overflow in C because `|r * d| ≤ |n|`, so no wrap is needed here.
      if (decide (n > 0) != decide (d > 0)) && r * d != n then (t.wrap (r - 1), .clear)
      else (r, .clear)
  else
    if d == 0 then (0, .dbz) else (Int.tdiv n d, .clear)

/--
One lane of the signed SIMD loop at `loops_arithmetic.dispatch.c.src:80-89`, for a divisor that is neither 0 nor -1. `nsign_d` is 1 for a negative divisor, `nsign_a` is 1 when `a < nsign_d`, and the truncating division of `a + nsign_a - nsign_d` is moved down by `nsign_a xor nsign_d`.
-/
def floorDivSimdLane (t : IntTy) (a d : Int) : Int :=
  let nsignD : Int := if d < 0 then 1 else 0
  let nsignA : Int := if a < nsignD then 1 else 0
  let diffSign := nsignA - nsignD
  let toNinf : Int := if nsignA != nsignD then 1 else 0
  let trunc := Int.tdiv (t.wrap (a + diffSign)) d
  t.wrap (trunc - toNinf)

/--
`@name@_ctype_divide` at `_core/src/umath/scalarmath.c.src:175`, which is also `@name@_ctype_floor_divide` (`scalarmath.c.src:202`). It returns `NPY_FPE_DIVIDEBYZERO` or `NPY_FPE_OVERFLOW`, which `scalarmath.c.src:1293` turns into a warning.
-/
def floorDivScalar (t : IntTy) (a b : Int) : Int × Flags :=
  if b == 0 then (0, .dbz)
  else if t.signed && b == -1 && a == t.minVal then (t.minVal, .ovf)
  else if t.signed then
    let tmp := Int.tdiv a b
    if (decide (a > 0) != decide (b > 0)) && Int.tmod a b != 0 then (t.wrap (tmp - 1), .clear)
    else (tmp, .clear)
  else (Int.tdiv a b, .clear)

/-! ## remainder -/

/--
The `@TYPE@_remainder` loop body at `_core/src/umath/loops_modulo.dispatch.c.src:586-610`. `DIVIDEBYZERO_OVERFLOW_CHECK` (`loops_modulo.dispatch.c.src:13`) sends both `b == 0` and `MIN % -1` to the zero result, and `FLAG_IF_DIVIDEBYZERO` sets a flag only for `b == 0`.
-/
def remainderArray (t : IntTy) (a b : Int) : Int × Flags :=
  if t.signed then
    if b == 0 || (a == t.minVal && b == -1) then
      (0, if b == 0 then .dbz else .clear)
    else
      let rem := Int.tmod a b
      if decide (a > 0) == decide (b > 0) || rem == 0 then (rem, .clear)
      else (t.wrap (rem + b), .clear)
  else
    if b == 0 then (0, .dbz) else (Int.tmod a b, .clear)

/-- `@name@_ctype_remainder` at `_core/src/umath/scalarmath.c.src:205`. -/
def remainderScalar (t : IntTy) (a b : Int) : Int × Flags :=
  let check := if t.signed then b == 0 || (a == t.minVal && b == -1) else b == 0
  if check then (0, if b == 0 then .dbz else .clear)
  else if t.signed then
    if decide (a > 0) == decide (b > 0) then (Int.tmod a b, .clear)
    else
      let out := Int.tmod a b
      if out != 0 then (t.wrap (out + b), .clear) else (out, .clear)
  else (Int.tmod a b, .clear)

/-! ## divmod -/

/-- The `@TYPE@_divmod` loop bodies at `_core/src/umath/loops_modulo.dispatch.c.src:629-670`. -/
def divmodArray (t : IntTy) (a b : Int) : (Int × Int) × Flags :=
  if t.signed then
    if b == 0 || (a == t.minVal && b == -1) then
      if b == 0 then ((0, 0), .dbz) else ((t.minVal, 0), .ovf)
    else
      let quo := Int.tdiv a b
      let rem := Int.tmod a b
      if decide (a > 0) == decide (b > 0) || rem == 0 then ((quo, rem), .clear)
      else ((t.wrap (quo - 1), t.wrap (rem + b)), .clear)
  else
    if b == 0 then ((0, 0), .dbz) else ((Int.tdiv a b, Int.tmod a b), .clear)

/-- `@name@_ctype_divmod` at `_core/src/umath/scalarmath.c.src:463`, which calls floor_divide and remainder and joins their status. -/
def divmodScalar (t : IntTy) (a b : Int) : (Int × Int) × Flags :=
  let (q, f1) := floorDivScalar t a b
  let (r, f2) := remainderScalar t a b
  ((q, r), f1.union f2)

/-! ## power -/

inductive PowErr where
  /-- "Integers to negative integer powers are not allowed." (ValueError) -/
  | negativeExponent
  deriving Repr, DecidableEq

/--
The loop of `_@TYPE@_squared_exponentiation_helper` at `_core/src/umath/loops.c.src:476-488`, and the identical loop of `@name@_ctype_power` at `scalarmath.c.src:254-262`. `e2` is the exponent shifted right by one and `out` starts as the base when the low bit of the exponent is set.
-/
def sqLoop (t : IntTy) (base : Int) (e2 : Nat) (out : Int) : Int :=
  if h : e2 = 0 then out
  else
    let base' := t.wrap (base * base)
    let out' := if e2 % 2 = 1 then t.wrap (out * base') else out
    sqLoop t base' (e2 / 2) out'
termination_by e2
decreasing_by omega

/-- `_@TYPE@_squared_exponentiation_helper(base, exponent_two, first_bit)` at `loops.c.src:476`. -/
def squaredExp (t : IntTy) (base : Int) (e2 : Nat) (firstBit : Bool) : Int :=
  sqLoop t base e2 (if firstBit then base else 1)

/-- `_@TYPE@_power_fast_path_helper` at `loops.c.src:491`. `none` stands for the return value 1, which means no fast path applied. -/
def powerFastPath (t : IntTy) (in1 in2 : Int) : Option Int :=
  if in2 == 0 || in1 == 1 then some 1
  else if in2 == 1 then some in1
  else if in2 == 2 then some (t.wrap (in1 * in1))
  else none

/-- One element of the general `BINARY_LOOP` of `@TYPE@_power` at `loops.c.src:540-556`. -/
def powerArrayElem (t : IntTy) (in1 in2 : Int) : Except PowErr Int :=
  if t.signed && in2 < 0 then .error .negativeExponent
  else
    match powerFastPath t in1 in2 with
    | some r => .ok r
    | none => .ok (squaredExp t in1 (in2.toNat / 2) (in2.toNat % 2 == 1))

/-- The general loop of `@TYPE@_power`, used when the exponent operand has a nonzero stride. The first negative exponent stops the loop with the error. -/
def powerArray (t : IntTy) (xs ys : List Int) : Except PowErr (List Int) :=
  (xs.zip ys).mapM fun (a, b) => powerArrayElem t a b

/--
The branch of `@TYPE@_power` at `loops.c.src:512-538` for an exponent with stride 0. The sign check runs once before the loop. Its fast path is chosen from the exponent alone, so a base of 1 goes through the squaring loop. The ufunc machinery does not call the inner loop for an empty array, so an empty array gives no error.
-/
def powerArrayBcast (t : IntTy) (xs : List Int) (in2 : Int) : Except PowErr (List Int) :=
  if xs.isEmpty then .ok []
  else if t.signed && in2 < 0 then .error .negativeExponent
  else
    let firstBit := in2.toNat % 2 == 1
    let in2start := in2.toNat / 2
    let fastop := in2 == 0 || in2 == 1 || in2 == 2
    .ok (xs.map fun in1 =>
      if fastop then (powerFastPath t in1 in2).getD 0
      else squaredExp t in1 in2start firstBit)

/-- `@name@_power` at `_core/src/umath/scalarmath.c.src:1549-1557` with `@name@_ctype_power` at `scalarmath.c.src:244`. The C function always returns status 0 (`scalarmath.c.src:263`), so the flags are always clear and no overflow is reported. -/
def powerScalar (t : IntTy) (a b : Int) : Except PowErr (Int × Flags) :=
  if t.signed && b < 0 then .error .negativeExponent
  else if b == 0 then .ok (1, .clear)
  else if a == 1 then .ok (1, .clear)
  else .ok (squaredExp t a (b.toNat / 2) (b.toNat % 2 == 1), .clear)

/-! ## multiply

Multiplication is not one of the operations of this area. It is modelled because the properties compare `x ** 2` with `x * x`.
-/

/--
`@name@_ctype_multiply` at `_core/src/umath/scalarmath.c.src:122` for types narrower than `long long`, which multiplies in a wider type and reports `NPY_FPE_OVERFLOW` when the product leaves the range, and at `scalarmath.c.src:149` for 64-bit types, which uses `npy_mul_with_overflow`. Both report overflow exactly when the true product is out of range.
-/
def multiplyScalar (t : IntTy) (a b : Int) : Int × Flags :=
  let p := a * b
  (t.wrap p, if t.inRange p then .clear else .ovf)

/-- The `@TYPE@_multiply` loop at `_core/src/umath/loops_autovec.dispatch.c.src:60`, which wraps and sets no flag. -/
def multiplyArray (t : IntTy) (a b : Int) : Int := t.wrap (a * b)

/-! ## gcd and lcm -/

/-- The loop of `npy_gcdu` at `_core/src/npymath/npy_math_internal.h.src:630` on unsigned values. -/
def gcdLoop (a b : Nat) : Nat :=
  if _h : a = 0 then b else gcdLoop (b % a) a
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

/-- `npy_lcmu` at `npy_math_internal.h.src:642`. The product `a / gcd * b` wraps at the width `w` of the unsigned C type. -/
def lcmU (w : Nat) (a b : Nat) : Nat :=
  let g := gcdLoop a b
  if g == 0 then 0 else (a / g * b) % 2 ^ w

/--
Convert an element to the unsigned C type of width `w` that the gcd helper works in. For signed types this is the absolute value taken in unsigned arithmetic at `npy_math_internal.h.src:665-666`, `(utype)0 - (utype)a` for negative `a`. For unsigned types the value is already non-negative.
-/
def gcdAbs (t : IntTy) (a : Int) : Nat :=
  let w := t.gcdWidth
  if t.signed && a < 0 then ((0 - a) % (2 : Int) ^ w).toNat else (a % (2 : Int) ^ w).toNat

/--
`@TYPE@_gcd` at `_core/src/umath/loops.c.src:564` and `:583`. For signed types `npy_gcd` at `npy_math_internal.h.src:657` casts the unsigned result back to the signed type of width `w`, and the loop then stores it in the element type.
-/
def gcdElem (t : IntTy) (a b : Int) : Int :=
  let w := t.gcdWidth
  let g : Int := gcdLoop (gcdAbs t a) (gcdAbs t b)
  if t.signed then t.wrap (wrapSigned w g) else t.wrap (wrapUnsigned w g)

/-- `@TYPE@_lcm` at `loops.c.src:564` and `:583`, the same as `gcdElem` with `npy_lcmu`. -/
def lcmElem (t : IntTy) (a b : Int) : Int :=
  let w := t.gcdWidth
  let l : Int := lcmU w (gcdAbs t a) (gcdAbs t b)
  if t.signed then t.wrap (wrapSigned w l) else t.wrap (wrapUnsigned w l)

/-! ## left_shift and right_shift -/

/--
`npy_lshift@u@@c@` at `_core/src/npymath/npy_math_internal.h.src:685`. The test `(size_t)b < sizeof(a) * CHAR_BIT` turns a negative shift into a huge unsigned value, so a negative shift gives 0. The array loop at `loops_autovec.dispatch.c.src:76` and the scalar `@name@_ctype_lshift` at `scalarmath.c.src:294` both call this helper. Shifting a negative signed value left is undefined in C and is modelled as a wrapping multiplication.
-/
def lshift (t : IntTy) (a b : Int) : Int :=
  if 0 ≤ b && b < t.bits then t.wrap (a * 2 ^ b.toNat) else 0

/--
`npy_rshift@u@@c@` at `npy_math_internal.h.src:695`, called by `loops_autovec.dispatch.c.src:92` and `scalarmath.c.src:301`. In range the C `>>` on a signed value is an arithmetic shift, which is a floor division by a power of two. Out of range the sign is kept.
-/
def rshift (t : IntTy) (a b : Int) : Int :=
  if 0 ≤ b && b < t.bits then a >>> b.toNat
  else if t.signed && a < 0 then -1
  else 0

/-! ## absolute and sign -/

/-- `@TYPE@_absolute` at `_core/src/umath/loops_autovec.dispatch.c.src:220` for signed types and `:120` for unsigned types. The loop sets no flag. -/
def absArray (t : IntTy) (a : Int) : Int :=
  if t.signed then (if a ≥ 0 then a else t.wrap (-a)) else a

/-- `@name@_ctype_absolute` at `_core/src/umath/scalarmath.c.src:610` for signed types, and `@name@_ctype_positive` (`scalarmath.c.src:599`) for unsigned types. -/
def absScalar (t : IntTy) (a : Int) : Int × Flags :=
  if t.signed then
    if a == t.minVal then (a, .ovf) else (if a < 0 then -a else a, .clear)
  else (a, .clear)

/-- `@TYPE@_sign` at `loops_autovec.dispatch.c.src:226` for signed types and `:126` for unsigned types. -/
def signElem (t : IntTy) (a : Int) : Int :=
  if t.signed then (if a > 0 then 1 else if a < 0 then -1 else 0)
  else (if a > 0 then 1 else 0)

end NumpyLean.IntArith
