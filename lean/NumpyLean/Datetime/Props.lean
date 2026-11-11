import NumpyLean.Datetime.Model

/-
Properties of the datetime models. Each property carries a status line that `scripts/check_props.py` counts.

Most properties are about all `int64` values or all strings, which is far too many to check, so a `PROVEN` property is stated over a finite sample that sits on the edges of the code: both ends of the Neri and Schneider range of `set_datetimestruct_days`, the 400 year cycle, the int64 limits and the boundaries between units. A `REFUTED` property states the negation of the general claim and gives a concrete counterexample, which has been checked against NumPy 2.5.4.
-/
namespace NumpyLean.Datetime

-- The string round trip proofs evaluate long chains of string and list operations.
set_option maxRecDepth 100000

def mD : Meta := ⟨.D, 1⟩
def mY : Meta := ⟨.Y, 1⟩
def mM : Meta := ⟨.M, 1⟩
def mW : Meta := ⟨.W, 1⟩
def ms' : Meta := ⟨.s, 1⟩
def mns : Meta := ⟨.ns, 1⟩

/-- Day counts on the edges of the calendar code. -/
def daySample : List Int :=
  [0, 1, -1, 59, 60, -719468, -719469, -719528, -719162, 10957, 11016, 2932896, -146097, 146097,
   -12699422, -12699423, -12699421, 1061042401, 1061042402, 1061042400, 2147483647, -2147483648,
   4294967296, -4294967296, 1000000000000000, -1000000000000000, intpMax, intpMin + 1, intpMax - 146097, intpMin + 146097]

/-- Values on the edges of every unit, including the int64 limits. -/
def valueSample : List Int :=
  [0, 1, -1, 6, -6, 7, -7, 23, -24, 59, -60, 86399, -86400, 1000, -1001, 4294967296, -4294967297,
   1000000000000000000, -1000000000000000000, intpMax, intpMin + 1, intpMax - 1970, intpMax - 1969, intpMin + 2]

/-! ## Calendar -/

/-- PROP datetime.set_days.round_trip : PROVEN
Source: `set_datetimestruct_days` (`datetime.c:236`) and `get_datetimestruct_days` (`datetime.c:131`) are meant to be inverse. Checked on `daySample`, which covers both branches of `set_datetimestruct_days` and both int64 limits. -/
theorem set_days_round_trip :
    (daySample.all fun d => getDays (dateOfDays d) == d) = true := by
  decide

/-- The fallback branch of `set_datetimestruct_days`, used for every input. -/
def setDaysFallback (days : Int) : Int × Int × Int :=
  let (year, d) := daysToYearsdays days
  let (mo, dd) := monthLoop (isLeap year) 12 d
  (year, mo, dd)

/-- PROP datetime.set_days.neri_agrees_with_fallback : PROVEN
Source: the comment at `datetime.c:232` says the Neri and Schneider algorithm replaces the classical one inside its range. On every sample day inside the range the two branches give the same date. -/
theorem set_days_neri_agrees_with_fallback :
    ((daySample.filter fun d => decide (-12699422 ≤ d ∧ d ≤ 1061042401)).all fun d =>
      setDays d == setDaysFallback d) = true := by
  decide

/-- Years around the epoch, year zero, negative years and the century years. -/
def yearSample : List Int :=
  (List.range 41).map (fun (i : Nat) => (i : Int) - 20) ++ [1600, 1700, 1800, 1900, 2000, 2100, 2400, -100, -400, -401, 1969, 1970, 1971]

/-- PROP datetime.is_leap.year_length : PROVEN
Source: `doc/source/reference/arrays.datetime.rst`, dates follow the proleptic Gregorian calendar. A year has 366 days exactly when `is_leapyear` says so, for every year of `yearSample`. -/
theorem is_leap_year_length :
    (yearSample.all fun y =>
      getDays { year := y + 1 } - getDays { year := y } == (if isLeap y then 366 else 365)) = true := by
  decide

/-- PROP datetime.day_of_week.matches_calendar : REFUTED
Source: `get_day_of_week` (`datetime_busday.c:28`), 1970-01-05 is Monday. The day of the week should be `(date - 4) mod 7`. `date - 4` is computed in `npy_int64` and wraps for the three dates just above the int64 minimum, so those dates get a weekday that is off by two. Only the very bottom of the 2.5e16 year range is affected, so this has no bug record. -/
theorem day_of_week_matches_calendar_refuted :
    ¬ (∀ d : Int, d ≠ nat → (dayOfWeek d : Int) = (d - 4) % 7) := by
  intro h
  exact absurd (h (intpMin + 1) (by decide)) (by decide)

/-! ## Struct conversion and printing -/

/-- PROP datetime.struct.round_trip : PROVEN
Source: `NpyDatetime_ConvertDatetime64ToDatetimeStruct` (`datetime.c:440`) and `NpyDatetime_ConvertDatetimeStructToDatetime64` (`datetime.c:301`) are used as inverse in `cast_datetime_to_datetime` (`datetime.c:3171`). For every specific unit other than weeks with multiplier 1 and every value of `valueSample` whose struct is not NaT, converting to the struct and back gives the value. -/
theorem struct_round_trip :
    ((specificUnits.filter (· != .W)).all fun u => valueSample.all fun v =>
      match toStruct ⟨u, 1⟩ v with
      | .ok d => d.year == nat || fromStruct ⟨u, 1⟩ d == .ok v
      | .error _ => false) = true := by
  decide

/-- PROP datetime.struct.week_round_trip : REFUTED
Source: as above, for weeks. `set_datetimestruct_days(dt * 7, out)` (`datetime.c:491`) wraps for week values beyond about 1.3e18, so the int64 maximum in weeks comes back as 1317624576693539400. Bug record `datetime-year-week-print-wrap`. -/
theorem struct_week_round_trip_refuted :
    ¬ (∀ v : Int, ∀ d, toStruct mW v = .ok d → fromStruct mW d = .ok v) := by
  intro h
  exact absurd (h intpMax _ rfl) (by decide)

/-- PROP datetime.to_struct.nat_only_from_nat : REFUTED
Source: `ndarraytypes.h:898`, "NaT is represented by year == NPY_DATETIME_NAT". A year value of `2**63 - 1970` is a valid datetime64[Y] that `np.isnat` reports as not NaT, but `out->year = 1970 + dt` (`datetime.c:483`) wraps to the int64 minimum, so the struct says NaT. It prints as `NaT` and casts to datetime64[M] as NaT. Bug record `datetime-year-week-print-wrap`. -/
theorem to_struct_nat_only_from_nat_refuted :
    ¬ (∀ v : Int, v ≠ nat → ∀ d, toStruct mY v = .ok d → d.year ≠ nat) := by
  intro h
  exact h (intpMax - 1969) (by decide) _ rfl (by decide)

/-- PROP datetime.to_struct.week_year_sign : REFUTED
Source: `doc/source/reference/arrays.datetime.rst`, weeks span 1.7e17 years either side of 1970, so a positive week value is a date after 1970. `set_datetimestruct_days(dt * 7, out)` (`datetime.c:491`) multiplies without an overflow check, so `2**61` weeks prints as the year -6313183731939669. The cast of the same value to days raises `OverflowError`. Bug record `datetime-year-week-print-wrap`. -/
theorem to_struct_week_year_sign_refuted :
    ¬ (∀ v : Int, v > 0 → ∀ d, toStruct mW v = .ok d → d.year ≥ 1970) := by
  intro h
  exact absurd (h (2 ^ 61) (by decide) _ rfl) (by decide)

/-- PROP datetime.print_parse.day_round_trip : PROVEN
Source: `NpyDatetime_MakeISO8601Datetime` (`datetime_strings.c:868`) and `NpyDatetime_ParseISO8601Datetime` (`datetime_strings.c:220`) are documented as the ISO 8601 printer and parser. For every day value of `daySample`, including years far outside 0 to 9999 and negative years, printing with unit D and parsing with unit D gives the value back. -/
theorem print_parse_day_round_trip :
    (daySample.all fun v =>
      match datetimeAsString mD v none with
      | .ok s => parseDatetime s.toList (some mD) == .ok (mD, v)
      | .error _ => false) = true := by
  decide

/-- PROP datetime.print_parse.second_round_trip : PROVEN
Source: as above, for unit s and every value of `valueSample`. -/
theorem print_parse_second_round_trip :
    (valueSample.all fun v =>
      match datetimeAsString ms' v none with
      | .ok s => parseDatetime s.toList (some ms') == .ok (ms', v)
      | .error _ => false) = true := by
  decide

/-- PROP datetime.print_parse.year_round_trip : REFUTED
Source: as above, for unit Y. The year value `2**63 - 1970` prints as `NaT` (see `to_struct.nat_only_from_nat`), and `NaT` parses back to NaT. Bug record `datetime-year-week-print-wrap`. -/
theorem print_parse_year_round_trip_refuted :
    ¬ (∀ v : Int, v ≠ nat → ∀ s, datetimeAsString mY v none = .ok s →
        parseDatetime s.toList (some mY) = .ok (mY, v)) := by
  intro h
  exact absurd (h (intpMax - 1969) (by decide) _ rfl) (by decide)

/-! ## Casting -/

/-- PROP datetime.cast.linear_round_trip : PROVEN
Source: `_datetime_scale_with_overflow_check` (`_datetime.h:354`) raises instead of wrapping. Casting a day value to seconds and back gives the value, or the first cast raises, for every value of `valueSample`. -/
theorem cast_linear_round_trip :
    (valueSample.all fun v =>
      match castDatetime mD ms' v with
      | .ok r => castDatetime ms' mD r == .ok v
      | .error e => e == .scaleOverflow) = true := by
  decide

/-- PROP datetime.cast.nonlinear_preserves_or_raises : REFUTED
Source: the linear casts raise `OverflowError` when the value does not fit (`_datetime.h:364`). The casts from years or months go through `npy_datetimestruct` (`dtype_transfer.c:775`) and `NpyDatetime_ConvertDatetimeStructToDatetime64` has no overflow check. Year 2300 (value 330) cast to nanoseconds gives a value in 1715 with no error, and casting it back gives -255. Bug record `datetime-nonlinear-cast-wraps`. -/
theorem cast_nonlinear_preserves_or_raises_refuted :
    ¬ (∀ v r : Int, castDatetime mY mns v = .ok r → castDatetime mns mY r = .ok v) := by
  intro h
  exact absurd (h 330 _ rfl) (by decide)

/-- PROP datetime.cast.nonlinear_never_makes_nat : REFUTED
Source: as above. The year value `2**63 - 1970` is not NaT, but its cast to datetime64[M] is NaT. Bug record `datetime-year-week-print-wrap`. -/
theorem cast_nonlinear_never_makes_nat_refuted :
    ¬ (∀ v : Int, v ≠ nat → castDatetime mY mM v ≠ .ok nat) := by
  intro h
  exact h (intpMax - 1969) (by decide) (by decide)

/-! ## Common unit and comparison -/

def metaSample : List Meta :=
  specificUnits.flatMap fun u => [1, 2, 3, 7, 14].map fun n => ⟨u, n⟩

/-- PROP datetime.common_unit.commutative : PROVEN
Source: `np.result_type` and `np.promote_types` are documented as symmetric. `compute_datetime_metadata_greatest_common_divisor` gives the same unit for both orders on every pair of `metaSample`, which holds every specific unit with multipliers 1, 2, 3, 7 and 14. -/
theorem common_unit_commutative :
    (metaSample.all fun a => metaSample.all fun b => commonMeta a b == commonMeta b a) = true := by
  decide

def linearUnits : List DUnit := [.W, .D, .h, .m, .s, .ms, .us, .ns, .ps, .fs, .att]

/-- PROP datetime.common_unit.linear_is_finer_unit : PROVEN
Source: `datetime.c:1580`, "Take the greater base". For two linear units with multiplier 1, the common unit is the finer one with multiplier 1, or the factor overflows. -/
theorem common_unit_linear_is_finer_unit :
    (linearUnits.all fun a => linearUnits.all fun b =>
      match commonMeta ⟨a, 1⟩ ⟨b, 1⟩ with
      | .ok c => c == ⟨if a.code ≤ b.code then b else a, 1⟩
      | .error e => e == .gcdOverflow) = true := by
  decide

/-- PROP datetime.compare.equal_means_same_day : REFUTED
Source: comparison of two datetimes should compare the instants. `np.datetime64('1971', 'Y') == np.datetime64(26, '14D')` is True, but the second value is 1970-12-31. The common unit of years and 14 days is computed as 7 days, because `datetime.c:1580-1594` multiplies the year multiplier by `get_datetime_units_factor(Y, D)`, which is 7 (the week entry of `_datetime_factors`), although the comment above says years have "no even factor". The year is then truncated to whole weeks before the comparison. Bug record `datetime-compare-nonlinear-common-unit`. -/
theorem compare_equal_means_same_day_refuted :
    ¬ (∀ m1 v1 m2 v2 lt, compareDatetimes m1 v1 m2 v2 = .ok (lt, true) →
        castDatetime m1 mD v1 = castDatetime m2 mD v2) := by
  intro h
  exact absurd (h mY 1 ⟨.D, 14⟩ 26 false rfl) (by decide)

/-- PROP datetime.compare.common_unit_of_year_and_day : REFUTED
Source: the comments at `datetime.c:1546` and `datetime.c:1558` say that a year multiplier is not multiplied because years have no even factor in days. The common unit of `Y` and `14D` is `7D` and not `D`. -/
theorem common_unit_of_year_and_day_refuted :
    ¬ (commonMeta mY ⟨.D, 14⟩ = .ok mD) := by
  decide

/-! ## Parsing -/

/-- PROP datetime.parse.nat_spellings : PROVEN
Source: `doc/source/reference/arrays.datetime.rst`, "NAT, in any combination of lowercase/uppercase letters". Every spelling and the empty string parse to NaT with generic units. -/
theorem parse_nat_spellings :
    ([[], "NaT".toList, "nat".toList, "NAT".toList, "nAt".toList, "Nat".toList, "naT".toList, "NAt".toList, "nAT".toList].all fun s =>
      parseDatetime s none == .ok (⟨.generic, 1⟩, nat)) = true := by
  decide

/-- PROP datetime.parse.leading_space_keeps_sign : REFUTED
Source: `NpyDatetime_ParseISO8601Datetime` skips leading whitespace (`datetime_strings.c:377`) and then a sign (`datetime_strings.c:383`), so `" -2000"` should be the year -2000. The negation test at `datetime_strings.c:404` reads `str[0]`, which is the space, so the sign is dropped and the result is the year 2000. Bug record `datetime-parse-leading-space-drops-sign`. -/
theorem parse_leading_space_keeps_sign_refuted :
    ¬ (parseDatetime " -2000".toList none = parseDatetime "-2000".toList none) := by
  decide

/-- PROP datetime.parse.digits_never_nat : REFUTED
Source: a string of digits is a year (`datetime_strings.c:396`). The year accumulates in `npy_int64` with no overflow check, so `"9223372036854775808"` wraps to the int64 minimum and comes out as NaT, and `"18446744073709551616"` comes out as the year 0. Bug record `datetime-parse-year-digits-wrap`. -/
theorem parse_digits_never_nat_refuted :
    ¬ (∀ s : List Char, s ≠ [] → s.all isDigitC = true →
        ∀ m v, parseDatetime s none = .ok (m, v) → v ≠ nat) := by
  intro h
  exact h "9223372036854775808".toList (by decide) (by decide) mY nat (by decide) rfl

/-- PROP datetime.parse.digits_year_value : REFUTED
Source: as above. `"18446744073709551616"` parses as the year 0, which is `1970` years before the epoch. -/
theorem parse_digits_year_value_refuted :
    ¬ (parseDatetime "18446744073709551616".toList none ≠ .ok (mY, -1970)) := by
  decide

/-- PROP datetime.parse.explicit_unit_matches_cast : REFUTED
Source: `np.datetime64(s, unit)` should give the same value as `np.datetime64(s).astype(f"M8[{unit}]")`, which raises `OverflowError` when the date does not fit. `np.datetime64('2300-01-01', 'ns')` instead returns 1715-06-13T00:25:26.290448384, because `NpyDatetime_ConvertDatetimeStructToDatetime64` (`datetime.c:301`) multiplies the day count up to nanoseconds without an overflow check. Bug record `datetime-parse-unit-overflow-wraps`. -/
theorem parse_explicit_unit_matches_cast_refuted :
    ¬ (∀ s : List Char, ∀ v,
        parseDatetime s (some mns) = .ok (mns, v) →
        ∀ m w, parseDatetime s none = .ok (m, w) → castDatetime m mns w = .ok v) := by
  intro h
  exact absurd (h "2300-01-01".toList _ rfl mD 120530 (by decide)) (by decide)

/-! ## Business days -/

def mask5 : List Bool := [true, true, true, true, true, false, false]
def maskOdd : List Bool := [true, false, true, false, true, false, false]
def busDates : List Int := (List.range 24).map fun (i : Nat) => 10950 + (i : Int)
def busHolidays (mask : List Bool) : List Int := normalizeHolidays mask [10957, 10960, 10960, 10966, nat]

/-- PROP datetime.busday_count.reverse_excludes_end : PROVEN
Source: the `busday_count` docstring, the end date is "excluded from the count" and an end date earlier than the begin date gives a negative count. So for `a < b`, `busday_count(b, a)` is minus the count over the days after `a` up to and including `b`, which is `-busday_count(a + 1, b + 1)`. This is the fix for gh-23197 at `datetime_busday.c:384`. Checked on every pair of 24 dates with two weekmasks and a holiday list with a duplicate and a NaT. -/
theorem busday_count_reverse_excludes_end :
    ([mask5, maskOdd].all fun m => busDates.all fun a => busDates.all fun b =>
      !(decide (a < b)) ||
        busdayCount 7 b a m (busHolidays m) == (busdayCount 7 (a + 1) (b + 1) m (busHolidays m)).map (·.map (- ·))) = true := by
  decide

/-- PROP datetime.busday_count.antisymmetric : REFUTED
Source: algebraic law that a reader might expect, `busday_count(a, b) == -busday_count(b, a)`. It fails whenever exactly one of the two dates is a business day, because the end date is always the excluded one. `busday_count('1999-12-25', '1999-12-27')` is 0 and `busday_count('1999-12-27', '1999-12-25')` is -1. The docstring describes this ("not including the day of enddates"), so there is no bug record. -/
theorem busday_count_antisymmetric_refuted :
    ¬ (∀ a b : Int, busdayCount 7 a b mask5 [] = (busdayCount 7 b a mask5 []).map (·.map (- ·))) := by
  intro h
  exact absurd (h 10950 10952) (by decide)

/-- PROP datetime.busday_count.loop_bounded : REFUTED
Source: the remaining days loop of `apply_business_day_count` (`datetime_busday.c:412`) is meant to run fewer than 7 times, after `whole_weeks` has removed the full weeks. When `date_end - date_begin` wraps, `whole_weeks` is wrong and the loop runs about 2**64 times. `np.busday_count(np.datetime64(-2**63 + 1, 'D'), np.datetime64(2**63 - 1, 'D'))` does not return. Bug record `datetime-busday-count-hang`. -/
theorem busday_count_loop_bounded_refuted :
    ¬ (∀ b e : Int, ∀ m hs, busdayCount 7 b e m hs ≠ .ok none) := by
  intro h
  exact h (intpMin + 1) intpMax mask5 [] (by decide)

/-- PROP datetime.is_busday.agrees_with_count : PROVEN
Source: the `busday_count` docstring, it counts the valid days in the half-open range. `is_busday(d)` is the same as `busday_count(d, d + 1) == 1` on the sample dates, masks and holidays. -/
theorem is_busday_agrees_with_count :
    ([mask5, maskOdd].all fun m => busDates.all fun d =>
      isBusday d m (busHolidays m) == (busdayCount 7 d (d + 1) m (busHolidays m) == .ok (some 1))) = true := by
  decide

/-- PROP datetime.busday_offset.lands_on_business_day : PROVEN
Source: the `busday_offset` docstring, the result is a valid day. For roll 'following' and every offset from -8 to 8 the result is a business day on the sample dates, masks and holidays. -/
theorem busday_offset_lands_on_business_day :
    ([mask5, maskOdd].all fun m => busDates.all fun d =>
      ((List.range 17).map fun (i : Nat) => (i : Int) - 8).all fun off =>
        match busdayOffset d off .following m (busHolidays m) with
        | .ok r => isBusday r m (busHolidays m)
        | .error _ => false) = true := by
  decide

/-- PROP datetime.busday_offset.counts_match : PROVEN
Source: the `busday_offset` and `busday_count` docstrings. From a business day, moving forward by `k` business days and counting back gives `k`, for `k` from 0 to 8 on the sample dates, masks and holidays. -/
theorem busday_offset_counts_match :
    ([mask5, maskOdd].all fun m => busDates.all fun d =>
      !isBusday d m (busHolidays m) || ((List.range 9).all fun k =>
        match busdayOffset d k .raise m (busHolidays m) with
        | .ok r => busdayCount 7 d r m (busHolidays m) == .ok (some k)
        | .error _ => false)) = true := by
  decide

end NumpyLean.Datetime
