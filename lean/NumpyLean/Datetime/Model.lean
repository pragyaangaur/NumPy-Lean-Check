import NumpyLean.Common.Intp

/-
Models of the `datetime64` machinery of NumPy 2.5.4.

The sources are `_core/src/multiarray/datetime.c` (calendar conversion, unit conversion factors, casting and the common unit of two datetimes), `_core/src/multiarray/_datetime.h` (the overflow checked scaling), `_core/src/multiarray/dtype_transfer.c` (which cast loop is chosen), `_core/src/multiarray/datetime_strings.c` (ISO 8601 parsing and printing) and `_core/src/multiarray/datetime_busday.c` with `datetime_busdaycal.c` (business days). Every line reference below is relative to `vendor/numpy/numpy/`.

Values are kept as `Int`. C signed overflow is undefined behaviour, and the model assumes two's complement wrap at every point where the C code can overflow, which is what the arm64 and x86-64 builds do. A chain of additions and multiplications is wrapped once at the end, which gives the same result as wrapping after every step. Divisions are applied to values that are already wrapped. The `npy_uint32` arithmetic of the calendar algorithms is written with `u32`.

The fields of `npy_datetimestruct` other than the year are `npy_int32`. On every path modelled here they stay far inside that range, so they are not wrapped.
-/
namespace NumpyLean.Datetime

/-- `NPY_DATETIME_NAT`, which is `NPY_MIN_INT64` (`_core/include/numpy/ndarraytypes.h:276`). -/
def nat : Int := intpMin

/-- Reduction to `npy_uint32`. -/
def u32 (x : Int) : Int := wrapUnsigned 32 x

/-- Reduction to `npy_uint64`. -/
def u64 (x : Int) : Int := wrapUnsigned 64 x

/-! ## Units -/

/-- `NPY_DATETIMEUNIT` from `_core/include/numpy/ndarraytypes.h:295`. The value 3 is a gap left by the removed business day unit. -/
inductive DUnit
  | Y | M | W | D | h | m | s | ms | us | ns | ps | fs | att | generic
  deriving DecidableEq, Repr, Inhabited

namespace DUnit

def code : DUnit → Nat
  | Y => 0 | M => 1 | W => 2 | D => 4 | h => 5 | m => 6 | s => 7 | ms => 8
  | us => 9 | ns => 10 | ps => 11 | fs => 12 | att => 13 | generic => 14

/-- `_datetime_strings` at `_core/src/multiarray/datetime.c:82`. -/
def name : DUnit → String
  | Y => "Y" | M => "M" | W => "W" | D => "D" | h => "h" | m => "m" | s => "s"
  | ms => "ms" | us => "us" | ns => "ns" | ps => "ps" | fs => "fs" | att => "as"
  | generic => "generic"

def all : List DUnit := [Y, M, W, D, h, m, s, ms, us, ns, ps, fs, att, generic]

def ofName (n : String) : Option DUnit := all.find? (·.name == n)

/-- The unit with a given enum value. Value 3 and values above 14 have none. -/
def ofCode (c : Nat) : Option DUnit := all.find? (·.code == c)

end DUnit

/-- `PyArray_DatetimeMetaData`: a base unit and a multiplier `num`, which is a C `int`. -/
structure Meta where
  base : DUnit
  num : Int := 1
  deriving DecidableEq, Repr

/-- The specific (non generic) units, in enum order. -/
def specificUnits : List DUnit := [.Y, .M, .W, .D, .h, .m, .s, .ms, .us, .ns, .ps, .fs, .att]

/-! ## Errors -/

inductive Err
  /-- "Cannot create a NumPy datetime other than NaT with generic units" or the matching message for the reverse conversion. -/
  | genericUnits
  /-- `OverflowError`: "Overflow when converting between datetime64 units" from `_datetime_scale_with_overflow_check` (`_core/src/multiarray/_datetime.h:364`). -/
  | scaleOverflow
  /-- `OverflowError`: "Integer overflow while computing the conversion factor between NumPy datetime units" (`datetime.c:1137`). -/
  | factorOverflow
  /-- `ValueError`: "Cannot convert from specific units to generic units" (`datetime.c:1078`). -/
  | toGeneric
  /-- `OverflowError`: "Integer overflow getting a common metadata divisor" (`datetime.c:1629`). -/
  | gcdOverflow
  /-- `TypeError`: "Cannot get a common metadata divisor ... incompatible nonlinear base time units" (`datetime.c:1609`). -/
  | incompatibleUnits
  deriving DecidableEq, Repr

/-! ## Calendar -/

/-- `npy_datetimestruct` (`_core/include/numpy/ndarraytypes.h:899`). NaT is a year equal to `NPY_DATETIME_NAT`. `att` is the C field `as`. -/
structure DTS where
  year : Int := 1970
  month : Int := 1
  day : Int := 1
  hour : Int := 0
  min : Int := 0
  sec : Int := 0
  us : Int := 0
  ps : Int := 0
  att : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- `extract_unit_64` and `extract_unit_32` (`datetime.c:44`). Returns the floor quotient and the new value of `*d`, which is the remainder in `[0, unit)`. The C code computes the truncated quotient and corrects it. -/
def extractUnit (d unit : Int) : Int × Int :=
  let q := d.tdiv unit
  let r := d.tmod unit
  if r < 0 then (q - 1, r + unit) else (q, r)

/-- `is_leapyear` (`datetime.c:110`). `year & 0x3` on a two's complement value is the Euclidean remainder by 4. -/
def isLeap (y : Int) : Bool :=
  y % 4 == 0 && (y.tmod 100 != 0 || y.tmod 400 == 0)

/-- `_days_per_month_table` (`datetime.c:103`), indexed by month 1 to 12. -/
def daysInMonth (leap : Bool) (month : Int) : Int :=
  let t : List Int := if leap then [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    else [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
  t.getD (month - 1).toNat 0

/--
`get_datetimestruct_days` (`datetime.c:131`), Hinnant's `days_from_civil`. The year is `npy_int64` and wraps. `yoe`, `doy` and `doe` are `npy_uint32`.
-/
def getDays (d : DTS) : Int :=
  let y := wrap64 (d.year - (if d.month ≤ 2 then 1 else 0))
  let era := (if y ≥ 0 then y else wrap64 (y - 399)).tdiv 400
  let yoe := u32 (y - era * 400)
  let mm := u32 (if d.month > 2 then d.month - 3 else d.month + 9)
  let doy := u32 ((u32 (153 * mm + 2)).tdiv 5 + u32 d.day - 1)
  let doe := u32 (yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy)
  wrap64 (era * 146097 + doe - 719468)

/-- `days_to_yearsdays` (`datetime.c:167`). Returns the year and the day within the year. -/
def daysToYearsdays (days : Int) : Int × Int :=
  let per400 : Int := 400 * 365 + 100 - 4 + 1
  let offset : Int := 365 * 30 + 7
  let (year0, d0) :=
    if days < intpMin + offset then
      let (q, r) := extractUnit (days + (per400 - offset)) per400
      (400 * q - 400, r)
    else
      let (q, r) := extractUnit (days - offset) per400
      (400 * q, r)
  let (year, d) :=
    if d0 ≥ 366 then
      let year1 := year0 + 100 * ((d0 - 1).tdiv (100 * 365 + 25 - 1))
      let d1 := (d0 - 1).tmod (100 * 365 + 25 - 1)
      if d1 ≥ 365 then
        let year2 := year1 + 4 * ((d1 + 1).tdiv (4 * 365 + 1))
        let d2 := (d1 + 1).tmod (4 * 365 + 1)
        if d2 ≥ 366 then (year2 + (d2 - 1).tdiv 365, (d2 - 1).tmod 365)
        else (year2, d2)
      else (year1, d1)
    else (year0, d0)
  (year + 2000, d)

/-- The month loop at `datetime.c:285`. If the loop ran out, the C code would leave the month and day at the values the caller set, which are 1 and 1. -/
def monthLoop (leap : Bool) : Nat → Int → Int × Int
  | 0, _ => (1, 1)
  | fuel + 1, d =>
    let i : Int := 12 - (fuel : Int)
    let len := daysInMonth leap i
    if d < len then (i, d + 1) else monthLoop leap fuel (d - len)

/--
`set_datetimestruct_days` (`datetime.c:236`). Returns the year, month and day. Inside `[-12699422, 1061042401]` it is the Neri and Schneider algorithm on `npy_uint32`. Outside it falls back to `days_to_yearsdays` and a month loop.
-/
def setDays (days : Int) : Int × Int × Int :=
  if -12699422 ≤ days ∧ days ≤ 1061042401 then
    let K : Int := 12699422
    let L : Int := 32800
    let N := u32 (u32 days + K)
    let N1 := u32 (4 * N + 3)
    let C := N1.tdiv 146097
    let NC := (N1.tmod 146097).tdiv 4
    let N2 := u32 (4 * NC + 3)
    let P2 := 2939745 * N2
    let Z := P2.tdiv 4294967296
    let NY := ((P2.tmod 4294967296).tdiv 2939745).tdiv 4
    let N3 := u32 (2141 * NY + 197913)
    let Mo := N3.tdiv 65536
    let Dd := (N3.tmod 65536).tdiv 2141
    let J : Int := if NY ≥ 306 then 1 else 0
    let Yr := u32 (100 * C + Z)
    (wrapSigned 32 (Yr - L) + J, (if J == 1 then Mo - 12 else Mo), Dd + 1)
  else
    let (year, d) := daysToYearsdays days
    let (mo, dd) := monthLoop (isLeap year) 12 d
    (year, mo, dd)

/-- A struct with the calendar date of a day count and every time field zero. -/
def dateOfDays (days : Int) (base : DTS := {}) : DTS :=
  let (y, mo, d) := setDays days
  { base with year := y, month := mo, day := d }

/--
`_datetime_scale_with_overflow_check` (`_core/src/multiarray/_datetime.h:354`). `none` is the `OverflowError`. NaT passes through.
-/
def scaleCheck (dt num denom : Int) : Option Int :=
  if dt == nat then some dt
  else
    let posLimit := intpMax.tdiv num
    let negLimit := (intpMax - denom + 1).tdiv num
    if dt > posLimit ∨ dt < -negLimit then none
    else if dt < 0 then some (wrap64 ((wrap64 (dt * num) - (denom - 1)).tdiv denom))
    else some ((wrap64 (dt * num)).tdiv denom)

/--
`NpyDatetime_ConvertDatetime64ToDatetimeStruct` (`datetime.c:440`).
-/
def toStruct (md : Meta) (dt0 : Int) : Except Err DTS :=
  if dt0 == nat then .ok { year := nat }
  else if md.base == .generic then .error .genericUnits
  else
    let dtE : Option Int := if md.num > 1 then scaleCheck dt0 md.num 1 else some (wrap64 (dt0 * md.num))
    match dtE with
    | none => .error .scaleOverflow
    | some dt =>
      let z : DTS := {}
      match md.base with
      | .Y => .ok { z with year := wrap64 (1970 + dt) }
      | .M =>
        let (q, r) := extractUnit dt 12
        .ok { z with year := 1970 + q, month := r + 1 }
      | .W => .ok (dateOfDays (wrap64 (dt * 7)))
      | .D => .ok (dateOfDays dt)
      | .h =>
        let (days, r) := extractUnit dt 24
        .ok { dateOfDays days with hour := r }
      | .m =>
        let (days, r) := extractUnit dt (60 * 24)
        let (hh, r) := extractUnit r 60
        .ok { dateOfDays days with hour := hh, min := r }
      | .s =>
        let (days, r) := extractUnit dt (60 * 60 * 24)
        let (hh, r) := extractUnit r (60 * 60)
        let (mi, r) := extractUnit r 60
        .ok { dateOfDays days with hour := hh, min := mi, sec := r }
      | .ms =>
        let (days, r) := extractUnit dt (1000 * 60 * 60 * 24)
        let (hh, r) := extractUnit r (1000 * 60 * 60)
        let (mi, r) := extractUnit r (1000 * 60)
        let (se, r) := extractUnit r 1000
        .ok { dateOfDays days with hour := hh, min := mi, sec := se, us := r * 1000 }
      | .us =>
        let (days, r) := extractUnit dt (1000 * 1000 * 60 * 60 * 24)
        let (hh, r) := extractUnit r (1000 * 1000 * 60 * 60)
        let (mi, r) := extractUnit r (1000 * 1000 * 60)
        let (se, r) := extractUnit r (1000 * 1000)
        .ok { dateOfDays days with hour := hh, min := mi, sec := se, us := r }
      | .ns =>
        let (days, r) := extractUnit dt (1000 * 1000 * 1000 * 60 * 60 * 24)
        let (hh, r) := extractUnit r (1000 * 1000 * 1000 * 60 * 60)
        let (mi, r) := extractUnit r (1000 * 1000 * 1000 * 60)
        let (se, r) := extractUnit r (1000 * 1000 * 1000)
        let (u, r) := extractUnit r 1000
        .ok { dateOfDays days with hour := hh, min := mi, sec := se, us := u, ps := r * 1000 }
      | .ps =>
        let (days, r) := extractUnit dt (1000 * 1000 * 1000 * 1000 * 60 * 60 * 24)
        let (hh, r) := extractUnit r (1000 * 1000 * 1000 * 1000 * 60 * 60)
        let (mi, r) := extractUnit r (1000 * 1000 * 1000 * 1000 * 60)
        let (se, r) := extractUnit r (1000 * 1000 * 1000 * 1000)
        let (u, r) := extractUnit r (1000 * 1000)
        .ok { dateOfDays days with hour := hh, min := mi, sec := se, us := u, ps := r }
      | .fs =>
        -- The whole range is about 2.6 hours either side of the epoch (`datetime.c:556`).
        let (hh, r) := extractUnit dt (1000 * 1000 * 1000 * 1000 * 1000 * 60 * 60)
        let z := if hh < 0 then { z with year := 1969, month := 12, day := 31, hour := hh + 24 }
          else { z with hour := hh }
        let (mi, r) := extractUnit r (1000 * 1000 * 1000 * 1000 * 1000 * 60)
        let (se, r) := extractUnit r (1000 * 1000 * 1000 * 1000 * 1000)
        let (u, r) := extractUnit r (1000 * 1000 * 1000)
        let (p, r) := extractUnit r 1000
        .ok { z with min := mi, sec := se, us := u, ps := p, att := r * 1000 }
      | .att =>
        -- The whole range is about 9.2 seconds either side of the epoch (`datetime.c:574`).
        let (se, r) := extractUnit dt (1000 * 1000 * 1000 * 1000 * 1000 * 1000)
        let z := if se < 0 then { z with year := 1969, month := 12, day := 31, hour := 23, min := 59, sec := se + 60 }
          else { z with sec := se }
        let (u, r) := extractUnit r (1000 * 1000 * 1000 * 1000)
        let (p, r) := extractUnit r (1000 * 1000)
        .ok { z with us := u, ps := p, att := r }
      | .generic => .error .genericUnits

/--
`NpyDatetime_ConvertDatetimeStructToDatetime64` (`datetime.c:301`). There is no overflow check anywhere in this function. The source says "TODO: If meta->num is really big, there could be overflow" at `datetime.c:296`, but the products below overflow for ordinary dates too.
-/
def fromStruct (md : Meta) (d : DTS) : Except Err Int :=
  if d.year == nat then .ok nat
  else if md.base == .generic then .error .genericUnits
  else
    let ret : Int :=
      match md.base with
      | .Y => wrap64 (d.year - 1970)
      | .M => wrap64 (12 * (d.year - 1970) + (d.month - 1))
      | b =>
        let days := getDays d
        let hms := ((days * 24 + d.hour) * 60 + d.min) * 60 + d.sec
        match b with
        | .W => if days ≥ 0 then days.tdiv 7 else (wrap64 (days - 6)).tdiv 7
        | .D => days
        | .h => wrap64 (days * 24 + d.hour)
        | .m => wrap64 ((days * 24 + d.hour) * 60 + d.min)
        | .s => wrap64 hms
        | .ms => wrap64 (hms * 1000 + d.us.tdiv 1000)
        | .us => wrap64 (hms * 1000000 + d.us)
        | .ns => wrap64 ((hms * 1000000 + d.us) * 1000 + d.ps.tdiv 1000)
        | .ps => wrap64 ((hms * 1000000 + d.us) * 1000000 + d.ps)
        | .fs => wrap64 (((hms * 1000000 + d.us) * 1000000 + d.ps) * 1000 + d.att.tdiv 1000)
        | .att => wrap64 (((hms * 1000000 + d.us) * 1000000 + d.ps) * 1000000 + d.att)
        | _ => 0
    if md.num > 1 then
      if ret ≥ 0 then .ok (ret.tdiv md.num)
      -- `ret - meta->num + 1` can overflow for `ret` near the int64 minimum. The arm64 and x86-64 builds do not wrap here: the compiler uses the fact that signed overflow is undefined and computes the exact quotient, which the differential test confirms. So this one step is modelled without a wrap.
      else .ok ((ret - md.num + 1).tdiv md.num)
    else .ok ret

/-! ## Conversion factors -/

/-- `_datetime_factors` (`datetime.c:984`), indexed by the enum value. -/
def factorTable : List Int := [1, 1, 7, 1, 24, 60, 60, 1000, 1000, 1000, 1000, 1000, 1000, 1, 0]

/-- The loop of `get_datetime_units_factor` (`datetime.c:1009`). A factor with any of the top eight bits set is reported as 0. -/
def unitsFactorLoop : Nat → Nat → Nat → Int → Int
  | 0, _, _, f => f
  | fuel + 1, unit, little, f =>
    if unit < little then
      let f := u64 (f * factorTable.getD unit 0)
      if f / 72057594037927936 != 0 then 0 else unitsFactorLoop fuel (unit + 1) little f
    else f

/-- `get_datetime_units_factor` (`datetime.c:1009`). It walks every enum value from `big` up to `little`, including the gap value 3. -/
def unitsFactor (big little : DUnit) : Int := unitsFactorLoop 16 big.code little.code 1

/-- `_uint64_euclidean_gcd` (`datetime.c:1033`). On non-negative inputs the loop computes the greatest common divisor, with gcd(0, y) = y. -/
def euclidGcd (x y : Int) : Int := Int.ofNat (Nat.gcd x.toNat y.toNat)

/--
`get_datetime_conversion_factor` (`datetime.c:1057`). Returns the reduced fraction `(num, denom)`. Years and months use the average over the 400 year cycle.
-/
def convFactor (src dst : Meta) : Except Err (Int × Int) :=
  if src.base == .generic then .ok (1, 1)
  else if dst.base == .generic then .error .toGeneric
  else
    let (sb, db, swapped) := if src.base.code ≤ dst.base.code then (src.base, dst.base, false)
      else (dst.base, src.base, true)
    let (num, denom) : Int × Int :=
      if sb == db then (1, 1)
      else if sb == .Y then
        if db == .M then (12, 1)
        else if db == .W then (97 + 400 * 365, 400 * 7)
        else (u64 ((97 + 400 * 365) * unitsFactor .D db), 400)
      else if sb == .M then
        if db == .W then (97 + 400 * 365, 400 * 12 * 7)
        else (u64 ((97 + 400 * 365) * unitsFactor .D db), 400 * 12)
      else (unitsFactor sb db, 1)
    if num == 0 then .error .factorOverflow
    else
      let (num, denom) := if swapped then (denom, num) else (num, denom)
      let num := u64 (num * u64 src.num)
      let denom := u64 (denom * u64 dst.num)
      let g := euclidGcd num denom
      .ok (wrap64 (num / g), wrap64 (denom / g))

/-! ## Casting between datetime units -/

/-- The nonlinear units, whose datetimes are cast through a struct (`dtype_transfer.c:1018`). -/
def nonlinear (u : DUnit) : Bool := u == .Y || u == .M

/--
`astype` from `datetime64[src]` to `datetime64[dst]`. Equal metadata is a plain copy (`time_to_time_get_loop`, `datetime.c:4016`). Otherwise `get_nbo_cast_datetime_transfer_function` (`dtype_transfer.c:974`) first computes the conversion factor and fails if it overflowed. If either unit is years or months it converts through `npy_datetimestruct` with `_strided_to_strided_datetime_general_cast` (`dtype_transfer.c:775`), which has no overflow check. Otherwise it scales with `_datetime_scale_with_overflow_check`.
-/
def castDatetime (src dst : Meta) (v : Int) : Except Err Int :=
  if src.base == dst.base && src.num == dst.num then .ok v
  else
    match convFactor src dst with
    | .error e => .error e
    | .ok (num, denom) =>
      if nonlinear src.base || nonlinear dst.base then
        match toStruct src v with
        | .error e => .error e
        | .ok d => fromStruct dst d
      else
        match scaleCheck v num denom with
        | some r => .ok r
        | none => .error .scaleOverflow

/-! ## Common unit of two datetimes -/

/--
`compute_datetime_metadata_greatest_common_divisor` (`datetime.c:1495`) with both strict flags off, as `datetime_type_promotion` (`datetime.c:1651`) calls it for two datetimes.

When one unit is years or months and the other is a linear unit, the comments say "Don't multiply num1 since there is no even factor". The code then falls through to the block that takes the finer base and multiplies by `get_datetime_units_factor` anyway. That factor walks through the week entry and so contains a factor of 7, which this model keeps.
-/
def commonMeta (m1 m2 : Meta) (strict1 strict2 : Bool := false) : Except Err Meta :=
  if m1.base == .generic then .ok m2
  else if m2.base == .generic then .ok m1
  else
    let step : Except Err (DUnit × Int × Int) :=
      if m1.base == m2.base then .ok (m1.base, u64 m1.num, u64 m2.num)
      else
        let pre : Except Err (Int × Int) :=
          if m1.base == .Y then
            if m2.base == .M then .ok (u64 (m1.num * 12), m2.num)
            else if strict1 then .error .incompatibleUnits else .ok (m1.num, m2.num)
          else if m2.base == .Y then
            if m1.base == .M then .ok (m1.num, u64 (m2.num * 12))
            else if strict2 then .error .incompatibleUnits else .ok (m1.num, m2.num)
          else if m1.base == .M then
            if strict1 then .error .incompatibleUnits else .ok (m1.num, m2.num)
          else if m2.base == .M then
            if strict2 then .error .incompatibleUnits else .ok (m1.num, m2.num)
          else .ok (m1.num, m2.num)
        match pre with
        | .error e => .error e
        | .ok (n1, n2) =>
          if m1.base.code > m2.base.code then
            let n2 := u64 (n2 * unitsFactor m2.base m1.base)
            if n2 == 0 then .error .gcdOverflow else .ok (m1.base, n1, n2)
          else
            let n1 := u64 (n1 * unitsFactor m1.base m2.base)
            if n1 == 0 then .error .gcdOverflow else .ok (m2.base, n1, n2)
    match step with
    | .error e => .error e
    | .ok (base, n1, n2) =>
      let g := euclidGcd n1 n2
      let gi := wrapSigned 32 g
      if gi ≤ 0 || g != gi then .error .gcdOverflow else .ok ⟨base, gi⟩

/-- The result of a comparison ufunc on two datetimes: both operands are cast to the common unit and the integers are compared. NaT compares false except under `!=` (`_core/src/umath/loops.c.src`, `@TYPE@_@kind@` for DATETIME). The pair is `(a < b, a == b)`. -/
def compareDatetimes (m1 : Meta) (v1 : Int) (m2 : Meta) (v2 : Int) : Except Err (Bool × Bool) :=
  match commonMeta m1 m2 with
  | .error e => .error e
  | .ok c =>
    match castDatetime m1 c v1, castDatetime m2 c v2 with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok a, .ok b =>
      if a == nat || b == nat then .ok (false, false) else .ok (decide (a < b), a == b)

/-! ## ISO 8601 printing -/

/-- `lossless_unit_from_datetimestruct` (`datetime_strings.c:803`). -/
def losslessUnit (d : DTS) : DUnit :=
  if d.att.tmod 1000 != 0 then .att
  else if d.att != 0 then .fs
  else if d.ps.tmod 1000 != 0 then .ps
  else if d.ps != 0 then .ns
  else if d.us.tmod 1000 != 0 then .us
  else if d.us != 0 then .ms
  else if d.sec != 0 then .s
  else if d.min != 0 then .m
  else if d.hour != 0 then .h
  else if d.day != 1 then .D
  else if d.month != 1 then .M
  else .Y

def digitChar (n : Int) : Char := Char.ofNat (48 + n.toNat)

def padLeft (w : Nat) (s : String) : String := String.ofList (List.replicate (w - s.length) '0') ++ s

/-- `snprintf("%04" NPY_INT64_FMT, year)`. The width counts the minus sign, so a negative year gets at least three digits. -/
def fmtYear (y : Int) : String :=
  if y < 0 then "-" ++ padLeft 3 (toString y.natAbs) else padLeft 4 (toString y)

def two (n : Int) : String := String.ofList [digitChar (n.tdiv 10), digitChar (n.tmod 10)]

def three (n : Int) (scale : Int) : String :=
  String.ofList [digitChar ((n.tdiv (100 * scale)).tmod 10), digitChar ((n.tdiv (10 * scale)).tmod 10), digitChar ((n.tdiv scale).tmod 10)]

/--
`NpyDatetime_MakeISO8601Datetime` (`datetime_strings.c:868`) with `local = 0`, `utc = 0` and `same_kind` casting, which is what `np.datetime_as_string` uses by default. `base = none` is `NPY_FR_ERROR`, the automatic unit. The output buffer is always long enough on this path, so the "too short" error is not modelled.
-/
def makeISO (d : DTS) (base : Option DUnit) : String :=
  if d.year == nat || base == some .generic then "NaT"
  else
    let base : DUnit := match base with
      | none =>
        let b := losslessUnit d
        if b == .h then .m else if b.code < DUnit.D.code then .D else b
      | some .W => .D
      | some b => b
    let parts : List (DUnit × String) :=
      [(.M, "-" ++ two d.month), (.D, "-" ++ two d.day), (.h, "T" ++ two d.hour),
       (.m, ":" ++ two d.min), (.s, ":" ++ two d.sec), (.ms, "." ++ three d.us 1000),
       (.us, three d.us 1), (.ns, three d.ps 1000), (.ps, three d.ps 1),
       (.fs, three d.att 1000), (.att, three d.att 1)]
    let body := parts.filter (fun (u, _) => u.code ≤ base.code) |>.map (·.2)
    fmtYear d.year ++ String.join body

/-- `np.datetime_as_string(np.array([v], f"M8[{num}{unit}]"), unit=...)` for `unit` none (the dtype unit), `auto` or a named unit. -/
def datetimeAsString (md : Meta) (v : Int) (unit : Option (Option DUnit)) : Except Err String :=
  match toStruct md v with
  | .error e => .error e
  | .ok d =>
    let base : Option DUnit := match unit with
      | none => some md.base
      | some u => u
    .ok (makeISO d base)

/-! ## ISO 8601 parsing -/

/-- Errors of `NpyDatetime_ParseISO8601Datetime` (`datetime_strings.c:220`). -/
inductive PErr
  /-- "Error parsing datetime string ... at position N". -/
  | parse (pos : Nat)
  | month | day | hour | minute | second | tzHour | tzMinute
  /-- The strings "today" and "now", which depend on the clock and are not modelled. -/
  | special
  /-- "Cannot create a NumPy datetime other than NaT with generic units". -/
  | generic
  deriving DecidableEq, Repr

def isSpaceC (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'
def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def digitVal (c : Char) : Int := (c.toNat : Int) - 48
def lowerC (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- `add_minutes_to_datetimestruct` (`datetime.c:2032`). The year is `npy_int64` and wraps on increment and decrement. -/
def addMinutes (d : DTS) (minutes : Int) : DTS :=
  let mi := d.min + minutes
  let (hq, mi) := extractUnit mi 60
  let hr := d.hour + hq
  let (dq, hr) := extractUnit hr 24
  let dy := d.day + dq
  let d : DTS := { d with min := mi, hour := hr, day := dy }
  if d.day < 1 then
    let (y, mo) := if d.month - 1 < 1 then (wrap64 (d.year - 1), 12) else (d.year, d.month - 1)
    { d with year := y, month := mo, day := d.day + daysInMonth (isLeap y) mo }
  else if d.day > 28 then
    let len := daysInMonth (isLeap d.year) d.month
    if d.day > len then
      let (y, mo) := if d.month + 1 > 12 then (wrap64 (d.year + 1), 1) else (d.year, d.month + 1)
      { d with year := y, month := mo, day := d.day - len }
    else d
  else d

/-- Read two digits at the front, as the repeated `sublen >= 2 && isdigit(substr[0]) && isdigit(substr[1])` tests do. -/
def twoDigits : List Char → Option (Int × List Char)
  | a :: b :: rest => if isDigitC a && isDigitC b then some (10 * digitVal a + digitVal b, rest) else none
  | _ => none

/-- Up to six fractional digits, multiplied up to six places (`datetime_strings.c:551`). Returns the value, the digit count and the rest. -/
def sixDigits (cs : List Char) : Int × Nat × List Char :=
  (List.range 6).foldl (fun (v, n, cs) _ =>
    match cs with
    | c :: rest => if isDigitC c then (10 * v + digitVal c, n + 1, rest) else (10 * v, n, cs)
    | [] => (10 * v, n, cs)) (0, 0, cs)

/-- The year digit loop at `datetime_strings.c:396`. `out->year` is `npy_int64` and wraps. -/
def yearDigits : List Char → Int → Nat → Int × Nat × List Char
  | c :: rest, y, n => if isDigitC c then yearDigits rest (wrap64 (10 * y + digitVal c)) (n + 1) else (y, n, c :: rest)
  | [], y, n => (y, n, [])

def skipSpaces : List Char → Nat → List Char × Nat
  | c :: rest, n => if isSpaceC c then skipSpaces rest (n + 1) else (c :: rest, n)
  | [], n => ([], n)

/-- The code after the `parse_timezone` label (`datetime_strings.c:655`) and the trailing whitespace check. `pos` is the index of the first character of `cs`. -/
def parseTimezone (d : DTS) (cs : List Char) (pos : Nat) : Except PErr DTS :=
  match cs with
  | [] => .ok d
  | c :: rest =>
    let tail (d : DTS) (cs : List Char) (pos : Nat) : Except PErr DTS :=
      let (cs, pos) := skipSpaces cs pos
      if cs.isEmpty then .ok d else .error (.parse pos)
    if c == 'Z' then
      if rest.isEmpty then .ok d else tail d rest (pos + 1)
    else if c == '-' || c == '+' then
      let neg := c == '-'
      match twoDigits rest with
      | none => .error (.parse (pos + 1))
      | some (oh, rest2) =>
        if oh ≥ 24 then .error .tzHour
        else
          let r : Except PErr (Int × List Char × Nat) :=
            match rest2 with
            | [] => .ok (0, [], pos + 3)
            | c2 :: rest3 =>
              let (cs4, p4) := if c2 == ':' then (rest3, pos + 4) else (c2 :: rest3, pos + 3)
              match twoDigits cs4 with
              | none => .error (.parse p4)
              | some (om, rest5) => if om ≥ 60 then .error .tzMinute else .ok (om, rest5, p4 + 2)
          match r with
          | .error e => .error e
          | .ok (om, rest6, p6) =>
            let (oh, om) := if neg then (-oh, -om) else (oh, om)
            tail (addMinutes d (-60 * oh - om)) rest6 p6
    else tail d cs pos

/-- The fractional seconds at `datetime_strings.c:551-632`. `cs` starts after the '.'. -/
def parseFraction (d : DTS) (cs : List Char) (pos : Nat) : Except PErr (DTS × DUnit) :=
  let more (cs : List Char) : Bool := match cs with | c :: _ => isDigitC c | [] => false
  let (u, n1, cs1) := sixDigits cs
  let d := { d with us := u }
  let p1 := pos + n1
  if !more cs1 then (parseTimezone d cs1 p1).map (·, if n1 > 3 then .us else .ms)
  else
    let (p, n2, cs2) := sixDigits cs1
    let d := { d with ps := p }
    let p2 := p1 + n2
    if !more cs2 then (parseTimezone d cs2 p2).map (·, if n2 > 3 then .ps else .ns)
    else
      let (a, n3, cs3) := sixDigits cs2
      let d := { d with att := a }
      (parseTimezone d cs3 (p2 + n3)).map (·, if n3 > 3 then .att else .fs)

/-- The time part, from the hour on (`datetime_strings.c:478`). `cs` starts after the 'T' or ' '. -/
def parseTime (d : DTS) (cs : List Char) (pos : Nat) : Except PErr (DTS × DUnit) :=
  match twoDigits cs with
  | none => .error (.parse pos)
  | some (hh, cs) =>
    if hh ≥ 24 then .error .hour
    else
      let d := { d with hour := hh }
      let pos := pos + 2
      match cs with
      | ':' :: cs =>
        let pos := pos + 1
        if cs.isEmpty then .error (.parse pos)
        else match twoDigits cs with
        | none => .error (.parse pos)
        | some (mi, cs) =>
          if mi ≥ 60 then .error .minute
          else
            let d := { d with min := mi }
            let pos := pos + 2
            match cs with
            | ':' :: cs =>
              let pos := pos + 1
              if cs.isEmpty then .error (.parse pos)
              else match twoDigits cs with
              | none => .error (.parse pos)
              | some (se, cs) =>
                if se ≥ 60 then .error .second
                else
                  let d := { d with sec := se }
                  let pos := pos + 2
                  match cs with
                  | '.' :: cs => parseFraction d cs (pos + 1)
                  | _ => (parseTimezone d cs pos).map (·, .s)
            | _ => (parseTimezone d cs pos).map (·, .m)
      | _ => (parseTimezone d cs pos).map (·, .h)

/--
`NpyDatetime_ParseISO8601Datetime` (`datetime_strings.c:220`) for a string of ASCII characters. Returns the struct and the best unit for the string. `unitGeneric` is true when the caller asked for generic units.

Note that the sign test at `datetime_strings.c:404` looks at `str[0]`, the first character of the whole string, and not at the character that the sign skip at `datetime_strings.c:383` consumed after the leading whitespace.
-/
def parseISO (s : List Char) (unitGeneric : Bool := false) : Except PErr (DTS × DUnit) :=
  let low := s.map lowerC
  if s.length == 0 || low == ['n', 'a', 't'] then .ok ({ year := nat, month := 1, day := 1 }, .generic)
  else if unitGeneric then .error .generic
  else if low == ['t', 'o', 'd', 'a', 'y'] || low == ['n', 'o', 'w'] then .error .special
  else
    let (cs, pos) := skipSpaces s 0
    let (cs, pos) := match cs with
      | c :: rest => if c == '-' || c == '+' then (rest, pos + 1) else (cs, pos)
      | [] => (cs, pos)
    if cs.isEmpty then .error (.parse pos)
    else
      let (y, n, cs) := yearDigits cs 0 0
      let pos := pos + n
      let y := if s.head? == some '-' then wrap64 (-y) else y
      let leap := isLeap y
      let d : DTS := { year := y, month := 1, day := 1 }
      match cs with
      | [] => .ok (d, .Y)
      | '-' :: cs =>
        let pos := pos + 1
        if cs.isEmpty then .error (.parse pos)
        else match twoDigits cs with
        | none => .error (.parse pos)
        | some (mo, cs) =>
          if mo < 1 || mo > 12 then .error .month
          else
            let d := { d with month := mo }
            let pos := pos + 2
            match cs with
            | [] => .ok (d, .M)
            | '-' :: cs =>
              let pos := pos + 1
              if cs.isEmpty then .error (.parse pos)
              else match twoDigits cs with
              | none => .error (.parse pos)
              | some (dd, cs) =>
                if dd < 1 || dd > daysInMonth leap mo then .error .day
                else
                  let d := { d with day := dd }
                  let pos := pos + 2
                  match cs with
                  | [] => .ok (d, .D)
                  | c :: cs =>
                    if c != 'T' && c != ' ' then .error (.parse pos)
                    else parseTime d cs (pos + 1)
            | _ => .error (.parse pos)
      | _ => .error (.parse pos)

/--
`np.datetime64(s)` or `np.datetime64(s, unit)` through `convert_pyobject_to_datetime` (`datetime.c:2343`). With no unit the best unit of the string is used with multiplier 1. A NaT string gives NaT with generic units.
-/
def parseDatetime (s : List Char) (md : Option Meta) : Except PErr (Meta × Int) :=
  match parseISO s (md.map (·.base) == some .generic) with
  | .error e => .error e
  | .ok (d, best) =>
    let m : Meta := md.getD ⟨best, 1⟩
    match fromStruct m d with
    | .ok v => .ok (m, v)
    | .error _ => .ok (m, nat)

/-! ## Business days -/

/-- `get_day_of_week` (`datetime_busday.c:28`). `date - 4` is `npy_int64` and wraps. 1970-01-05 is a Monday, which is day 0. -/
def dayOfWeek (date : Int) : Nat :=
  let r := (wrap64 (date - 4)).tmod 7
  (if r < 0 then r + 7 else r).toNat

/-- `normalize_holidays_list` (`datetime_busdaycal.c:224`): sort, drop NaT and duplicates, and keep only holidays on a weekmask day. -/
def normalizeHolidays (mask : List Bool) (hs : List Int) : List Int :=
  let sorted := (hs.toArray.qsort (· < ·)).toList
  let (out, _) := sorted.foldl (fun (acc, last) h =>
    if h != nat && h != last then
      if mask.getD (dayOfWeek h) false then (acc ++ [h], h) else (acc, last)
    else (acc, last)) (([] : List Int), nat)
  out

/-- `find_earliest_holiday_on_or_after` (`datetime_busday.c:90`) on a strictly sorted list: the index of the first holiday that is not before `date`. The binary search returns this index. -/
def lowerBound (date : Int) (hs : List Int) : Nat := (hs.filter (· < date)).length

/-- `find_earliest_holiday_after` (`datetime_busday.c:129`) on a strictly sorted list: the index of the first holiday after `date`. -/
def upperBound (date : Int) (hs : List Int) : Nat := (hs.filter (· ≤ date)).length

/-- `is_holiday` (`datetime_busday.c:50`). -/
def isHoliday (date : Int) (hs : List Int) : Bool := hs.contains date

def isBus (mask : List Bool) (hs : List Int) (date : Int) (dow : Nat) : Bool :=
  mask.getD dow false && !isHoliday date hs

/-- Step forward until a business day. Returns the date and its day of the week. -/
def stepFwd (mask : List Bool) (hs : List Int) : Nat → Int → Nat → Int × Nat
  | 0, d, w => (d, w)
  | fuel + 1, d, w =>
    let d := wrap64 (d + 1)
    let w := if w + 1 == 7 then 0 else w + 1
    if isBus mask hs d w then (d, w) else stepFwd mask hs fuel d w

def stepBwd (mask : List Bool) (hs : List Int) : Nat → Int → Nat → Int × Nat
  | 0, d, w => (d, w)
  | fuel + 1, d, w =>
    let d := wrap64 (d - 1)
    let w := if w == 0 then 6 else w - 1
    if isBus mask hs d w then (d, w) else stepBwd mask hs fuel d w

/-- `NPY_BUSDAY_ROLL` (`datetime_busday.h`). -/
inductive Roll
  | forward | following | backward | preceding | modifiedfollowing | modifiedpreceding | nat | raise
  deriving DecidableEq, Repr

inductive BErr
  /-- "NaT input in busday_offset". -/
  | natInput
  /-- "Non-business day date in busday_offset". -/
  | nonBusiness
  /-- "the business day weekmask must have at least one valid business day". -/
  | emptyMask
  /-- "Cannot compute a business day count with a NaT (not-a-time) date". -/
  | natCount
  deriving DecidableEq, Repr

/-- A loop bound that is enough for every search for the next business day: at most six weekend days and every holiday lie in between. -/
def rollFuel (hs : List Int) : Nat := 7 * (hs.length + 2)

def monthNumber (days : Int) : Int := (setDays days).2.1

/-- `apply_business_day_roll` (`datetime_busday.c:159`). `forward` is the same as `following` and `backward` the same as `preceding`. -/
def applyRoll (date : Int) (roll : Roll) (mask : List Bool) (hs : List Int) : Except BErr (Int × Nat) :=
  if date == nat then
    if roll == .raise then .error .natInput else .ok (nat, 0)
  else
    let w := dayOfWeek date
    if !isBus mask hs date w then
      let f := rollFuel hs
      match roll with
      | .forward | .following | .modifiedfollowing =>
        let (d2, w2) := stepFwd mask hs f date w
        if roll == .modifiedfollowing && monthNumber date != monthNumber d2 then .ok (stepBwd mask hs f date w)
        else .ok (d2, w2)
      | .backward | .preceding | .modifiedpreceding =>
        let (d2, w2) := stepBwd mask hs f date w
        if roll == .modifiedpreceding && monthNumber date != monthNumber d2 then .ok (stepFwd mask hs f date w)
        else .ok (d2, w2)
      | .nat => .ok (nat, w)
      | .raise => .error .nonBusiness
    else .ok (date, w)

/-- The stepping loop of `apply_business_day_offset` for a positive remaining offset (`datetime_busday.c:313`). -/
def offsetFwd (mask : List Bool) (hs : List Int) : Nat → Int → Nat → Int → Int
  | 0, d, _, _ => d
  | fuel + 1, d, w, off =>
    if off > 0 then
      let d := wrap64 (d + 1)
      let w := if w + 1 == 7 then 0 else w + 1
      offsetFwd mask hs fuel d w (if isBus mask hs d w then off - 1 else off)
    else d

def offsetBwd (mask : List Bool) (hs : List Int) : Nat → Int → Nat → Int → Int
  | 0, d, _, _ => d
  | fuel + 1, d, w, off =>
    if off < 0 then
      let d := wrap64 (d - 1)
      let w := if w == 0 then 6 else w - 1
      offsetBwd mask hs fuel d w (if isBus mask hs d w then off + 1 else off)
    else d

/-- When the test for NaT after the roll fires in the compiled library: for a NaT input, for the 'nat' roll, and when a backward roll steps down onto the int64 minimum. A forward roll that wraps onto the int64 minimum does not count. -/
def rolledToNat (orig rolled : Int) (roll : Roll) : Bool :=
  orig == nat || (rolled == nat && (roll == .nat || roll == .backward || roll == .preceding || roll == .modifiedpreceding))

/--
`apply_business_day_offset` (`datetime_busday.c:272`) together with the weekmask check of `business_day_offset` (`datetime_busday.c:476`). `hs` must be normalized. The whole week jump `date += (offset / busdays_in_weekmask) * 7` is `npy_int64` and wraps.
-/
def busdayOffset (date0 offset : Int) (roll : Roll) (mask : List Bool) (hs : List Int) : Except BErr Int :=
  let b : Int := (mask.filter id).length
  if b == 0 then .error .emptyMask
  else
    match applyRoll date0 roll mask hs with
    | .error e => .error e
    | .ok (date1, w) =>
      -- The C code tests `date == NPY_DATETIME_NAT` after the roll (`datetime_busday.c:291`). In the compiled library this test only fires when the input was NaT or the roll was 'nat'. A forward roll from the int64 maximum steps with `++date` onto the int64 minimum, and the compiler, which may assume that the increment does not overflow, has removed the test for that case. The differential test confirms this, so the model tests the cause of NaT and not the value.
      let date := date1
      if rolledToNat date0 date roll then .ok nat
      else if offset > 0 then
        let hs := hs.drop (lowerBound date hs)
        let date := wrap64 (date + (offset.tdiv b) * 7)
        let off := offset.tmod b
        let k := upperBound date hs
        let off := off + k
        let hs := hs.drop k
        .ok (offsetFwd mask hs ((off.toNat + 1) * rollFuel hs) date w off)
      else if offset < 0 then
        let hs := hs.take (upperBound date hs)
        let date := wrap64 (date + (offset.tdiv b) * 7)
        let off := offset.tmod b
        let k := lowerBound date hs
        let off := off - (hs.length - k)
        let hs := hs.take k
        .ok (offsetBwd mask hs (((-off).toNat + 1) * rollFuel hs) date w off)
      else .ok date

/-- The remaining days loop of `apply_business_day_count` (`datetime_busday.c:412`). The fuel stands in for the C `while (date_begin < date_end)`, which has no bound of its own. -/
def countLoop (mask : List Bool) : Nat → Int → Int → Nat → Int → Option Int
  | 0, b, e, _, c => if b < e then none else some c
  | fuel + 1, b, e, w, c =>
    if b < e then
      let c := if mask.getD w false then c + 1 else c
      countLoop mask fuel (b + 1) e (if w + 1 == 7 then 0 else w + 1) c
    else some c

/--
`apply_business_day_count` (`datetime_busday.c:362`). `hs` must be normalized. `none` means the remaining days loop would run for more than `fuel` steps. The C loop runs `date_end - date_begin` times, which is normally below 7, but after the subtraction `date_end - date_begin` wraps it can be close to 2^64.
-/
def busdayCount (fuel : Nat) (b0 e0 : Int) (mask : List Bool) (hs : List Int) : Except BErr (Option Int) :=
  let bm : Int := (mask.filter id).length
  if bm == 0 then .error .emptyMask
  else if b0 == nat || e0 == nat then .error .natCount
  else if b0 == e0 then .ok (some 0)
  else
    let (b, e, swapped) := if b0 > e0 then (wrap64 (e0 + 1), wrap64 (b0 + 1), true) else (b0, e0, false)
    let lo := lowerBound b hs
    let hs := hs.drop lo
    let hi := lowerBound e hs
    let count : Int := -(hi : Int)
    let weeks := (wrap64 (e - b)).tdiv 7
    let count := wrap64 (count + weeks * bm)
    let b := wrap64 (b + weeks * 7)
    let r := if b < e then countLoop mask fuel b e (dayOfWeek b) count else some count
    .ok (r.map fun c => if swapped then wrap64 (-c) else c)

/-- `is_business_day` (`datetime_busday.c:729`). -/
def isBusday (date : Int) (mask : List Bool) (hs : List Int) : Bool :=
  isBus mask hs date (dayOfWeek date) && date != nat

end NumpyLean.Datetime
