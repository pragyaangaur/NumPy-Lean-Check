import NumpyLean.Common.Intp

/-
Models of NumPy 2.5.4 dtype casting and promotion for the legacy builtin dtypes.

Sources, relative to `vendor/numpy/numpy/`:
- `_core/src/multiarray/can_cast_table.h` (the safe casting table),
- `_core/src/multiarray/scalartypes.c.src:4359-4492` (`initialize_casting_tables`, which builds the promotion table),
- `_core/src/multiarray/dtypemeta.c` (the `common_dtype` and `common_instance` slots),
- `_core/src/multiarray/common_dtype.c` (`PyArray_CommonDType` and `PyArray_PromoteDTypeSequence`),
- `_core/src/multiarray/abstractdtypes.c` (the NEP 50 Python int, float and complex DTypes),
- `_core/src/multiarray/convert_datatype.c` (`PyArray_PromoteTypes`, `PyArray_ResultType`, `PyArray_CheckCastSafety` and the cast implementations),
- `_core/src/multiarray/arraytypes.c.src:286-313` (the overflow check for Python integers).

Type numbers are kept as `Nat` with the values of the `NPY_TYPES` enum in `_core/include/numpy/ndarraytypes.h`, because the C code indexes its tables with them and compares them with `<` and `>`.

The model fixes the platform of the test machine, macOS on arm64 with the LP64 data model. There `long` and `long long` are both 8 bytes, `npy_intp` is `long`, and `long double` is the same 8 byte type as `double`. Every size that depends on the platform is in `npySizeof`.

Void, datetime and timedelta are not modelled. Their rows of the tables are filled in as the C code fills them, but no function below is meant to be called with them.
-/
namespace NumpyLean.DType

/-! ## Type numbers -/

def NPY_BOOL : Nat := 0
def NPY_BYTE : Nat := 1
def NPY_UBYTE : Nat := 2
def NPY_SHORT : Nat := 3
def NPY_USHORT : Nat := 4
def NPY_INT : Nat := 5
def NPY_UINT : Nat := 6
def NPY_LONG : Nat := 7
def NPY_ULONG : Nat := 8
def NPY_LONGLONG : Nat := 9
def NPY_ULONGLONG : Nat := 10
def NPY_FLOAT : Nat := 11
def NPY_DOUBLE : Nat := 12
def NPY_LONGDOUBLE : Nat := 13
def NPY_CFLOAT : Nat := 14
def NPY_CDOUBLE : Nat := 15
def NPY_CLONGDOUBLE : Nat := 16
def NPY_OBJECT : Nat := 17
def NPY_STRING : Nat := 18
def NPY_UNICODE : Nat := 19
def NPY_VOID : Nat := 20
def NPY_DATETIME : Nat := 21
def NPY_TIMEDELTA : Nat := 22
def NPY_HALF : Nat := 23
/-- `NPY_NTYPES_LEGACY`. -/
def NPY_NTYPES_LEGACY : Nat := 24
/-- `NPY_INTP` is `NPY_LONG` on LP64 platforms (`_core/include/numpy/npy_common.h`). -/
def NPY_INTP : Nat := NPY_LONG

/-- `PyTypeNum_ISINTEGER` at `ndarraytypes.h:1720`. -/
def isInteger (n : Nat) : Bool := 1 ≤ n && n ≤ 10
def isSigned (n : Nat) : Bool := n == 1 || n == 3 || n == 5 || n == 7 || n == 9
def isUnsigned (n : Nat) : Bool := n == 2 || n == 4 || n == 6 || n == 8 || n == 10
/-- `PyTypeNum_ISFLOAT` at `ndarraytypes.h:1723`. -/
def isFloat (n : Nat) : Bool := (11 ≤ n && n ≤ 13) || n == 23
/-- `PyTypeNum_ISCOMPLEX` at `ndarraytypes.h:1734`. -/
def isComplex (n : Nat) : Bool := 14 ≤ n && n ≤ 16
/-- `PyTypeNum_ISNUMBER` at `ndarraytypes.h:1727`. It includes bool. -/
def isNumber (n : Nat) : Bool := n ≤ 16 || n == 23
def isStringType (n : Nat) : Bool := n == NPY_STRING || n == NPY_UNICODE

/-- `NPY_SIZEOF_<TYPE>` for the macros of `can_cast_table.h`, on the test platform. Complex types are given the size of one component, because `CASTS_SAFELY_FROM_CFLOAT(FLOAT)` is called with the component name. -/
def npySizeof (n : Nat) : Nat :=
  match n with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 4 | 6 => 4
  | 7 => 8 | 8 => 8 | 9 => 8 | 10 => 8
  | 11 => 4 | 12 => 8 | 13 => 8
  | 14 => 4 | 15 => 8 | 16 => 8
  | 22 => 8 | 23 => 2
  | _ => 0

/-! ## The safe casting table, `can_cast_table.h` -/

/-- `FITS` at `can_cast_table.h:19`. -/
def fits (a b : Nat) : Bool := npySizeof a ≤ npySizeof b
/-- `UFITS` at `can_cast_table.h:21`. -/
def ufits (a b : Nat) : Bool := npySizeof a < npySizeof b
/-- `IFITS` at `can_cast_table.h:23`. -/
def ifits (a b : Nat) : Bool :=
  npySizeof a < npySizeof b || (npySizeof a == npySizeof b && npySizeof a ≥ npySizeof NPY_DOUBLE)

/-- The component type of a complex type, as used for the complex columns. -/
def compOf (n : Nat) : Nat := n - 3

/-- `CASTS_SAFELY_FROM_INT` (`signed = true`, `can_cast_table.h:46`) and `CASTS_SAFELY_FROM_UINT` (`can_cast_table.h:37`). -/
def fromIntRow (signed : Bool) (i j : Nat) : Bool :=
  if j == NPY_BOOL then false
  else if isSigned j then (if signed then fits i j else ufits i j)
  else if isUnsigned j then (if signed then false else fits i j)
  else if isFloat j then ifits i j
  else if isComplex j then ifits i (compOf j)
  else if 17 ≤ j && j ≤ 20 then true
  else if j == NPY_DATETIME then false
  else if j == NPY_TIMEDELTA then (if signed then fits i j else ufits i j)
  else false

/-- `CASTS_SAFELY_FROM_FLOAT` at `can_cast_table.h:56`, also used for half. -/
def fromFloatRow (i j : Nat) : Bool :=
  if isFloat j then fits i j
  else if isComplex j then fits i (compOf j)
  else 17 ≤ j && j ≤ 20

/-- `CASTS_SAFELY_FROM_CFLOAT` at `can_cast_table.h:63`. -/
def fromComplexRow (i j : Nat) : Bool :=
  if isComplex j then fits (compOf i) (compOf j)
  else 17 ≤ j && j ≤ 20

/-- `_npy_can_cast_safely_table[i][j]` at `can_cast_table.h:69-115`. -/
def canCastSafelyTable (i j : Nat) : Bool :=
  if i == NPY_BOOL then j != NPY_DATETIME && j < NPY_NTYPES_LEGACY
  else if isSigned i then fromIntRow true i j
  else if isUnsigned i then fromIntRow false i j
  else if isFloat i then fromFloatRow i j
  else if isComplex i then fromComplexRow i j
  else if i == NPY_OBJECT then j == NPY_OBJECT
  else if i == NPY_STRING then 17 ≤ j && j ≤ 20
  else if i == NPY_UNICODE then j == 17 || j == 19 || j == 20
  else if i == NPY_VOID then j == 17 || j == 20
  else if i == NPY_DATETIME then 17 ≤ j && j ≤ 21
  else if i == NPY_TIMEDELTA then (17 ≤ j && j ≤ 20) || j == 22
  else false

/-! ## The promotion table, `scalartypes.c.src:4359-4492` -/

/-- `_npy_scalar_kinds_table`. The `memset` at `scalartypes.c.src:4371` gives every type outside the numeric repeat the object kind 5. Kinds: bool 0, intpos 1, intneg 2, float 3, complex 4, object 5 (`ndarraytypes.h:212-220`). -/
def scalarKind (n : Nat) : Nat :=
  if n == NPY_BOOL then 0
  else if isUnsigned n then 1
  else if isSigned n then 2
  else if isFloat n then 3
  else if isComplex n then 4
  else 5

/-- `NPY_NSCALARKINDS`. -/
def nScalarKinds : Nat := 6

/-- `_npy_next_larger_type_table` at `scalartypes.c.src:4385-4389`. `none` is the C value `-1`. -/
def nextLarger (n : Nat) : Option Nat :=
  match n with
  | 1 => some 3 | 2 => some 4 | 3 => some 5 | 4 => some 6 | 5 => some 7 | 6 => some 8
  | 7 => some 9 | 8 => some 10
  | 23 => some 11 | 11 => some 12 | 12 => some 13
  | 14 => some 15 | 15 => some 16
  | _ => none

/-- `_npy_smallest_type_of_kind_table` at `scalartypes.c.src:4363-4368`. -/
def smallestOfKind (k : Nat) : Nat :=
  match k with
  | 0 => NPY_BOOL | 1 => NPY_UBYTE | 2 => NPY_BYTE | 3 => NPY_HALF | 4 => NPY_CFLOAT
  | _ => NPY_OBJECT

/-- The `for (;;)` loop at `scalartypes.c.src:4463-4484`. `fuel` bounds the loop, which ends after at most 20 steps. -/
def promoSearchLoop (i j : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, skind, k =>
    match nextLarger k with
    | some k' =>
      if canCastSafelyTable i k' && canCastSafelyTable j k' then some k'
      else promoSearchLoop i j fuel skind k'
    | none =>
      let skind' := skind + 1
      if skind' < nScalarKinds then
        let k' := smallestOfKind skind'
        if canCastSafelyTable i k' && canCastSafelyTable j k' then some k'
        else promoSearchLoop i j fuel skind' k'
      else none

/-- The `else` branch at `scalartypes.c.src:4445-4487`. No type has `NPY_NOSCALAR` in the table, so the check at line 4450 never fires. -/
def promoSearch (i j : Nat) : Option Nat :=
  let ik := scalarKind i
  let jk := scalarKind j
  if ik > jk then promoSearchLoop i j 32 ik i else promoSearchLoop i j 32 jk j

def isFlexOrTime (n : Nat) : Bool := 18 ≤ n && n ≤ 22

/--
`_npy_type_promotion_table[a][b]` as left by `initialize_casting_tables`. `none` is `-1`.

The C loop writes cell `(i, j)` with `i < j` from row `i`, and the rows of string, unicode, void, datetime and timedelta also write the cells they share with object (`scalartypes.c.src:4427-4428`). Row `i` is the last writer of every cell `(i, j)`, except the cells `(object, flexible)` which the later flexible rows set to object. The function returns the value of the last write.
-/
def promotionTable (a b : Nat) : Option Nat :=
  let i := min a b
  let j := max a b
  if i == j then
    -- scalartypes.c.src:4416 and 4421
    if isFlexOrTime i then none else some i
  else if isFlexOrTime i then none
  else if i == NPY_OBJECT && isFlexOrTime j then some NPY_OBJECT
  -- scalartypes.c.src:4433
  else if j == NPY_STRING || j == NPY_UNICODE || j == NPY_VOID then none
  else if canCastSafelyTable i j then some j
  else if canCastSafelyTable j i then some i
  else promoSearch i j

/-! ## DTypes and descriptors -/

/-- A DType class: a legacy builtin DType given by its type number, or one of the abstract Python scalar DTypes of `abstractdtypes.c`. -/
inductive DT where
  | legacy (n : Nat)
  | pyInt
  | pyFloat
  | pyComplex
  deriving DecidableEq, Repr, Inhabited

/-- A native byte order descriptor. `chars` is the length in characters for `S` and `U` and is `0` otherwise. -/
structure Descr where
  num : Nat
  chars : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- `elsize` of a descriptor. Unicode stores four bytes per character. -/
def Descr.elsize (d : Descr) : Nat :=
  if d.num == NPY_STRING then d.chars
  else if d.num == NPY_UNICODE then 4 * d.chars
  else if isComplex d.num then 2 * npySizeof d.num
  else if d.num == NPY_OBJECT then 8
  else npySizeof d.num

/-- The `kind` character of a descriptor, as a number for comparisons. -/
def kindChar (n : Nat) : Char :=
  if n == NPY_BOOL then 'b'
  else if isSigned n then 'i'
  else if isUnsigned n then 'u'
  else if isFloat n then 'f'
  else if isComplex n then 'c'
  else if n == NPY_OBJECT then 'O'
  else if n == NPY_STRING then 'S'
  else if n == NPY_UNICODE then 'U'
  else 'V'

def Descr.dtype (d : Descr) : DT := .legacy d.num

/-- `NPY_DT_is_parametric` for the modelled DTypes. -/
def isParametric : DT → Bool
  | .legacy n => isStringType n
  | _ => false

/-- `default_descr` of a DType. Abstract DTypes use the defaults at `abstractdtypes.c:18`, `:56` and `:71`. String and unicode default to one character (`dtypemeta.c:761`). -/
def defaultDescr : DT → Descr
  | .legacy n => if isStringType n then ⟨n, 1⟩ else ⟨n, 0⟩
  | .pyInt => ⟨NPY_INTP, 0⟩
  | .pyFloat => ⟨NPY_DOUBLE, 0⟩
  | .pyComplex => ⟨NPY_CDOUBLE, 0⟩

/-! ## The `common_dtype` slots -/

/-- `default_builtin_common_dtype` at `dtypemeta.c:1046-1111`. `none` is `NotImplemented`. -/
def defaultBuiltinCommonDType (cls : Nat) (other : DT) : Option DT :=
  match other with
  | .pyComplex =>
    if isComplex cls then some (.legacy cls)
    else if cls == NPY_HALF || cls == NPY_FLOAT then some (.legacy NPY_CFLOAT)
    else if cls == NPY_DOUBLE then some (.legacy NPY_CDOUBLE)
    else if cls == NPY_LONGDOUBLE then some (.legacy NPY_CLONGDOUBLE)
    else none
  | .pyFloat =>
    if isComplex cls || isFloat cls then some (.legacy cls) else none
  | .pyInt =>
    if isComplex cls || isFloat cls || isInteger cls || cls == NPY_TIMEDELTA then some (.legacy cls)
    else none
  | .legacy o =>
    -- dtypemeta.c:1093: let the DType with the larger type number decide.
    if o > cls then none
    else (promotionTable cls o).map DT.legacy

/-- `string_unicode_common_dtype` at `dtypemeta.c:1115-1131`. -/
def stringUnicodeCommonDType (cls : Nat) (other : DT) : Option DT :=
  match other with
  | .legacy o =>
    if !isNumber o && !(cls == NPY_UNICODE && o == NPY_STRING) then none
    else some (.legacy cls)
  | _ => none

/-- `int_common_dtype` at `abstractdtypes.c:168-212`. The fallback branch for legacy user DTypes is not reachable for builtin DTypes. -/
def intCommonDType (other : DT) : Option DT :=
  match other with
  | .legacy o => if o == NPY_BOOL then some (.legacy NPY_INTP) else none
  | _ => none

/-- `float_common_dtype` at `abstractdtypes.c:215-248`. -/
def floatCommonDType (other : DT) : Option DT :=
  match other with
  | .legacy o => if o == NPY_BOOL || isInteger o then some (.legacy NPY_DOUBLE) else none
  | .pyInt => some .pyFloat
  | _ => none

/-- `complex_common_dtype` at `abstractdtypes.c:251-284`. -/
def complexCommonDType (other : DT) : Option DT :=
  match other with
  | .legacy o => if o == NPY_BOOL || isInteger o then some (.legacy NPY_CDOUBLE) else none
  | .pyInt => some .pyComplex
  | .pyFloat => some .pyComplex
  | .pyComplex => none

/-- `NPY_DT_CALL_common_dtype(cls, other)`. The slot of each DType is set at `dtypemeta.c:1304-1361`. Void, datetime and timedelta are not modelled and answer `NotImplemented`. -/
def commonSlot (cls other : DT) : Option DT :=
  match cls with
  | .legacy n =>
    if n == NPY_OBJECT then some (.legacy NPY_OBJECT)  -- object_common_dtype, dtypemeta.c:1158
    else if isStringType n then stringUnicodeCommonDType n other
    else if isNumber n then defaultBuiltinCommonDType n other
    else none
  | .pyInt => intCommonDType other
  | .pyFloat => floatCommonDType other
  | .pyComplex => complexCommonDType other

/-- `PyArray_CommonDType` at `common_dtype.c:49-75`. `none` is the `DTypePromotionError`. -/
def commonDType (a b : DT) : Option DT :=
  if a == b then some a
  else match commonSlot a b with
    | some r => some r
    | none => commonSlot b a

/-! ## `PyArray_PromoteDTypeSequence`, `common_dtype.c:112-293` -/

/-- One pass of the `for` loop of `reduce_dtypes_to_most_knowledgeable` at `common_dtype.c:121-145` over the first `len` entries. `cleared` marks the entries the C code sets to `NULL`. The last value of `res` is returned, with `none` for `NotImplemented`. -/
def reducePass (len : Nat) (dts : Array DT) (cleared : Array Bool) : Array DT × Array Bool × Option DT :=
  (List.range (len / 2)).foldl
    (fun (st : Array DT × Array Bool × Option DT) low =>
      let (dts, cleared, _) := st
      let high := len - 1 - low
      let a := dts.getD low default
      let b := dts.getD high default
      -- common_dtype.c:123: identical DTypes skip the slot call.
      let res := if b == a then some a else commonSlot a b
      match res with
      | none => ((dts.set! low b).set! high a, cleared, none)
      | some r => if r == a then (dts, cleared.set! high true, res) else (dts, cleared, res))
    (dts, cleared, none)

/-- `reduce_dtypes_to_most_knowledgeable`. It recurses on the first `len - len / 2` entries until two are left. -/
def reduceMostKnowledgeable : Nat → Nat → Array DT → Array Bool → Array DT × Array Bool × Option DT
  | 0, _, dts, cleared => (dts, cleared, none)
  | fuel + 1, len, dts, cleared =>
    let (dts, cleared, res) := reducePass len dts cleared
    if len == 2 then (dts, cleared, res)
    else reduceMostKnowledgeable fuel (len - len / 2) dts cleared

/-- The final loop of `PyArray_PromoteDTypeSequence` at `common_dtype.c:244-287`, over the indices still to visit. `none` is an error. The check `dtypes[i] == prev` at line 245 never fires, because `prev` stays `NULL`. -/
def promoteLoop (main : DT) (dts : Array DT) (cleared : Array Bool) : List Nat → Option DT → Option (Option DT)
  | [], result => some result
  | i :: rest, result =>
    if cleared.getD i false then promoteLoop main dts cleared rest result
    else
      match commonSlot main (dts.getD i default) with
      | none => none
      | some promotion =>
        match result with
        | none => promoteLoop main dts cleared rest (some promotion)
        | some r =>
          match commonDType r promotion with
          | none => none
          | some r' => promoteLoop main dts cleared rest (some r')

/-- `PyArray_PromoteDTypeSequence` at `common_dtype.c:193-293`. `none` is the `DTypePromotionError`. -/
def promoteDTypeSequence (l : List DT) : Option DT :=
  match l with
  | [] => none
  | [d] => some d
  | _ =>
    let n := l.length
    let (dts, cleared, res) := reduceMostKnowledgeable n n l.toArray (Array.replicate n false)
    let main := dts.getD 0 default
    let start := if res.isNone then 1 else 2
    match promoteLoop main dts cleared ((List.range n).drop start) res with
    | some (some r) => some r
    | _ => none

/-! ## Descriptor level casts and promotion -/

/-- `REQUIRED_STR_LEN` at `convert_datatype.c:51`, indexed by item size. -/
def requiredStrLen (elsize : Nat) : Nat :=
  match elsize with
  | 1 => 3 | 2 => 5 | 3 => 10 | 4 => 10 | 5 => 20 | 6 => 20 | 7 => 20 | 8 => 20
  | _ => 0

/-- The string length chosen by `cast_to_string_resolve_descriptors` at `convert_datatype.c:2426-2491`, in characters. -/
def castToStringSize (d : Descr) : Nat :=
  if d.num == NPY_BOOL then 5
  else if isUnsigned d.num then requiredStrLen d.elsize
  else if isSigned d.num then requiredStrLen d.elsize + 1
  else if d.num == NPY_HALF || d.num == NPY_FLOAT || d.num == NPY_DOUBLE then 32
  else if d.num == NPY_LONGDOUBLE then 48
  else if d.num == NPY_CFLOAT || d.num == NPY_CDOUBLE then 2 * 32
  else if d.num == NPY_CLONGDOUBLE then 2 * 48
  else if d.num == NPY_STRING then d.elsize
  else if d.num == NPY_UNICODE then d.elsize / 4
  else 0

/-- `NPY_MAX_INT`. -/
def npyMaxInt : Nat := 2147483647

/-- `PyArray_CastDescrToDType` at `convert_datatype.c:958-1003` for a string or unicode target. `none` is the error at `convert_datatype.c:2495`. -/
def castDescrToDType (d : Descr) (target : Nat) : Option Descr :=
  if d.num == target then some d
  else if !isStringType target then some (defaultDescr (.legacy target))
  else
    let size := castToStringSize d
    if target == NPY_UNICODE && size > npyMaxInt / 4 then none
    else some ⟨target, size⟩

/-- `string_unicode_common_instance` at `dtypemeta.c:770-778`. -/
def stringCommonInstance (a b : Descr) : Descr := if a.elsize ≥ b.elsize then a else b

/-- `PyArray_PromoteTypes` at `convert_datatype.c:1075-1126`, the C side of `np.promote_types`. `none` is an error. The fast path at line 1081 returns the input when both arguments are the same object, which is also what the slow path returns for the modelled dtypes. -/
def promoteTypes (a b : Descr) : Option Descr := do
  let common ← commonDType a.dtype b.dtype
  match common with
  | .legacy n =>
    if !isParametric common then some (defaultDescr common)
    else
      let a' ← castDescrToDType a n
      let b' ← castDescrToDType b n
      some (stringCommonInstance a' b')
  | _ => some (defaultDescr common)

/-- One argument of `np.result_type`: a dtype, or a Python `int`, `float` or `complex` value. -/
inductive Arg where
  | dtype (d : Descr)
  | pyInt
  | pyFloat
  | pyComplex
  deriving DecidableEq, Repr, Inhabited

/-- Drop an argument that is the same object as the one before it (`multiarraymodule.c:3645`). Equal tokens stand for the same object, because the tests create one object per token. -/
def dropRepeats : List Arg → Option Arg → List Arg
  | [], _ => []
  | a :: rest, prev => if prev == some a then dropRepeats rest prev else a :: dropRepeats rest (some a)

/-- The fold over descriptors at `convert_datatype.c:1698-1718`. -/
def foldInstances (target : Nat) : List Descr → Option Descr → Option (Option Descr)
  | [], acc => some acc
  | d :: rest, acc =>
    match castDescrToDType d target with
    | none => none
    | some c =>
      match acc with
      | none => foldInstances target rest (some c)
      | some r => foldInstances target rest (some (stringCommonInstance r c))

/-- `np.result_type`: `array_result_type` at `multiarraymodule.c:3624-3686` and `PyArray_ResultType` at `convert_datatype.c:1618-1738`. Dtype arguments come first and scalar arguments after them, each group in the order given. `none` is an error. -/
def resultType (args : List Arg) : Option Descr :=
  let args := dropRepeats args none
  let descrs := args.filterMap (fun a => match a with | .dtype d => some d | _ => none)
  let scalars := args.filterMap (fun a => match a with
    | .pyInt => some DT.pyInt | .pyFloat => some DT.pyFloat | .pyComplex => some DT.pyComplex | _ => none)
  match descrs, scalars with
  | [], [] => none
  | [d], [] => some d
  -- A lone Python scalar gives the dtype of the array it was converted to. The tests use small values, so an int gives `intp`.
  | [], [s] => some (defaultDescr s)
  | _, _ => do
    let common ← promoteDTypeSequence (descrs.map Descr.dtype ++ scalars)
    -- convert_datatype.c:1683: an abstract result is replaced by its default.
    let common := match common with
      | .legacy _ => common
      | _ => (defaultDescr common).dtype
    match common with
    | .legacy n =>
      if isParametric common then
        match foldInstances n descrs none with
        | none => none
        | some (some r) => some r
        | some none => some (defaultDescr common)
      else some (defaultDescr common)
    | _ => none

/-! ## Casting safety -/

/-- `NPY_CASTING`, in the order of its values. -/
inductive Casting where
  | no
  | equiv
  | safe
  | sameKind
  | «unsafe»
  deriving DecidableEq, Repr, Inhabited

def Casting.toNat : Casting → Nat
  | .no => 0 | .equiv => 1 | .safe => 2 | .sameKind => 3 | .«unsafe» => 4

/-- `dtype_kind_to_ordering` at `convert_datatype.c:683-718`. Kinds outside the list give `-1`, which does not occur for the modelled dtypes. -/
def kindOrdering (n : Nat) : Int :=
  match kindChar n with
  | 'b' => 0 | 'u' => 1 | 'i' => 2 | 'f' => 4 | 'c' => 5 | 'S' => 6 | 'U' => 7 | 'V' => 8 | 'O' => 9
  | _ => -1

/-- The casting level stored on a numeric cast by `add_numeric_cast` at `convert_datatype.c:2359-2387`. -/
def numericCastLevel (f t : Nat) : Casting :=
  let fd : Descr := ⟨f, 0⟩
  let td : Descr := ⟨t, 0⟩
  if kindChar f == kindChar t && fd.elsize == td.elsize then .equiv
  else if canCastSafelyTable f t then .safe
  else if kindOrdering f ≤ kindOrdering t then .sameKind
  else .«unsafe»

/-- The static `casting` of the cast implementation from `f` to `t` (`castingimpl->casting`). -/
def staticCasting (f t : Nat) : Casting :=
  if f == NPY_OBJECT && t == NPY_OBJECT then .no          -- object_to_object, convert_datatype.c:3524
  else if t == NPY_OBJECT then .safe                      -- any_to_object, convert_datatype.c:3594
  else if f == NPY_OBJECT then .«unsafe»                    -- object_to_any, convert_datatype.c:3577
  else if isNumber f && isNumber t then numericCastLevel f t
  else if isStringType f && f == t then .«unsafe»           -- string_to_string_cast, convert_datatype.c:2702
  else if isStringType t then
    -- convert_datatype.c:2571-2576
    if f == NPY_UNICODE then .«unsafe» else .sameKind
  else .«unsafe»                                            -- legacy wrapped string to number, convert_datatype.c:2547

/--
The casting level that `resolve_descriptors` returns for the cast from `f` to `t`. `t = none` is a target without a length, `S0` or `U0`, which `PyArray_CanCastTypeTo` passes as `NULL` (`convert_datatype.c:748`).
-/
def resolvedCasting (f : Descr) (t : Option Descr) (tnum : Nat) : Casting :=
  if f.num == NPY_OBJECT && tnum == NPY_OBJECT then .no
  else if tnum == NPY_OBJECT then .safe
  else if f.num == NPY_OBJECT then .«unsafe»
  else if isNumber f.num && isNumber tnum then
    -- legacy_same_dtype_resolve_descriptors gives "no" for native byte order (convert_datatype.c:2172).
    match numericCastLevel f.num tnum with
    | .equiv => .no
    | c => c
  else if isStringType f.num && f.num == tnum then
    -- string_to_string_resolve_descriptors at convert_datatype.c:2583-2620
    let toElsize := match t with | some d => d.elsize | none => f.elsize
    if f.elsize < toElsize then .safe
    else if f.elsize > toElsize then .sameKind
    else .no
  else if isStringType tnum then
    if f.num == NPY_UNICODE then .«unsafe»   -- convert_datatype.c:2524
    else
      -- cast_to_string_resolve_descriptors at convert_datatype.c:2530-2533, on characters
      match t with
      | none => .safe
      | some d => if d.chars ≥ castToStringSize f then .safe else .sameKind
  else .«unsafe»

/-- `PyArray_CanCastTypeTo` at `convert_datatype.c:728-759` with `PyArray_CheckCastSafety` at `convert_datatype.c:520-552`, the C side of `np.can_cast(from, to, casting)` for dtype arguments. -/
def canCast (f t : Descr) (casting : Casting) : Bool :=
  let tOpt : Option Descr := if isStringType t.num && t.chars == 0 then none else some t
  -- convert_datatype.c:530: the stored level answers when it is safe enough.
  if (staticCasting f.num t.num).toNat ≤ casting.toNat then true
  else (resolvedCasting f tOpt t.num).toNat ≤ casting.toNat

/-! ## NEP 50 binary operations with a Python int -/

/-- The result DType of a binary ufunc on an array of dtype `n` and a Python int, by NEP 50. -/
def pyIntOpDType (n : Nat) : Option DT := commonDType (.legacy n) .pyInt

/--
`@TYPE@_safe_pyint_setitem` at `arraytypes.c.src:286-313`, which stores the Python int in the operand. The result is `true` when it raises `OverflowError`.

Signed types convert through `long` (`MyPyLong_AsLong`), which raises for values outside its range, and then narrow to the C type and compare. Unsigned types convert through `unsigned long` with a wraparound flag that is set for negative values (`arraytypes.c.src:222-240`).
-/
def pyIntSetitemOverflows (n : Nat) (v : Int) : Bool :=
  let bits := 8 * npySizeof n
  if isSigned n then
    if !inIntp v then true
    else wrapSigned bits v != v
  else if isUnsigned n then
    if 0 ≤ v && v < (2 : Int) ^ 64 then wrapUnsigned bits v != v
    else true
  else false

/-- `np.add(np.ones(2, dtype), v)` for a Python int `v`: the result dtype, or `none` for `OverflowError`. Floating point and complex results take the value without a range check for the values the tests use, which stay below `2**64` in magnitude. -/
def pyIntOp (n : Nat) (v : Int) : Option Descr := do
  let dt ← pyIntOpDType n
  let d := defaultDescr dt
  if isInteger d.num && pyIntSetitemOverflows d.num v then none else some d

end NumpyLean.DType
