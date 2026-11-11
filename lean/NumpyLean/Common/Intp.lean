/-
Fixed-width integer helpers shared by every model.

NumPy's `npy_intp` is a signed 64-bit integer on every platform this project tests. Models keep values as `Int` and call these helpers at each point where the C code can wrap or checks for overflow, so that the wrap is visible in the model.
-/
-- Equality of results is decidable, so that concrete counterexamples can be checked by `decide`.
deriving instance DecidableEq for Except

namespace NumpyLean

def intpMax : Int := 9223372036854775807
def intpMin : Int := -9223372036854775808

/-- Reduce an integer to the signed range of the given bit width, as a C cast does. -/
def wrapSigned (bits : Nat) (x : Int) : Int :=
  let m : Int := (2 : Int) ^ bits
  let r := x % m
  if r ≥ m / 2 then r - m else r

/-- Reduce an integer to the unsigned range of the given bit width. -/
def wrapUnsigned (bits : Nat) (x : Int) : Int := x % (2 : Int) ^ bits

def wrap64 (x : Int) : Int := wrapSigned 64 x

def inIntp (x : Int) : Bool := intpMin ≤ x && x ≤ intpMax

/--
`npy_mul_sizes_with_overflow` from `numpy/_core/src/common/templ_common.h.src:57`, on the `__builtin_mul_overflow` path that GCC and Clang take. It returns the overflow flag and the wrapped product.
-/
def mulSizesWithOverflow (a b : Int) : Bool × Int :=
  let p := a * b
  (!(inIntp p), wrap64 p)

end NumpyLean
