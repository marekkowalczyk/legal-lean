/-
  LegalLean.Time — Calendar-date deadlines and end-of-month clamping.

  Models civil-law calendar-date deadline computation (such as Polish
  Art. 112 Kodeksu cywilnego applied to procedural time limits via
  Art. 165 § 1 Kodeksu postępowania cywilnego):
  A deadline expressed in months expires on the day that by date corresponds
  to the initial day of the period, or—if there is no such day in the target
  month—on the last day of that month (end-of-month clamping).

  Provides:
  - Gregorian leap-year and `daysInMonth` functions
  - `Date.isValid`: structural validity predicate for calendar dates
  - `Date.addMonths`: adding N months with end-of-month clamping
  - `Date.withinDeadline` / `Date.withinMonthsDeadline`: decidable deadline checks
  - Order and arithmetic lemmas (`le_refl`, `le_trans`, `le_antisymm`, `le_total`,
    `not_le_iff_lt`, `addMonths_isValid`, `addMonths_zero`, `le_addMonths`,
    `lt_addMonths_of_pos`, and concrete end-of-month clamping theorems).
-/

import LegalLean.Core

set_option autoImplicit false

namespace LegalLean

/-- Alias for `LegalLean.Date` highlighting full calendar-date semantics. -/
abbrev CalendarDate := Date

namespace Date

-- ============================================================
-- §1  Gregorian leap year and month lengths
-- ============================================================

/-- Gregorian leap-year test: divisible by 4, except centuries not divisible by 400. -/
def isLeapYear (year : Nat) : Bool :=
  (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)

/-- Number of days in `month` (1–12) of `year`.
    Out-of-range month values default to 30 so the function is total. -/
def daysInMonth (year month : Nat) : Nat :=
  match month with
  | 1  => 31
  | 2  => if isLeapYear year then 29 else 28
  | 3  => 31
  | 4  => 30
  | 5  => 31
  | 6  => 30
  | 7  => 31
  | 8  => 31
  | 9  => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _  => 30

/-- Structural validity of a calendar date (`1 ≤ month ≤ 12` and `1 ≤ day ≤ daysInMonth`). -/
def isValid (d : Date) : Bool :=
   decide (1 ≤ d.month) &&
   decide (d.month ≤ 12) &&
   decide (1 ≤ d.day) &&
   decide (d.day ≤ daysInMonth d.year d.month)

-- ============================================================
-- §2  Adding N months with end-of-month clamping
-- ============================================================

/-- Advance a calendar date by `months` calendar months, clamping `day` to the
    last day of the target month when the initial day exceeds the target month's
    length (e.g. `2025-01-31 + 1 month = 2025-02-28`, `2025-08-31 + 6 months = 2026-02-28`).
    Directly implements Art. 112 k.c. in connection with Art. 165 § 1 k.p.c. -/
def addMonths (d : Date) (months : Nat) : Date :=
  let totalMonths := d.year * 12 + (d.month - 1) + months
  let targetYear  := totalMonths / 12
  let targetMonth := (totalMonths % 12) + 1
  let maxDay      := daysInMonth targetYear targetMonth
  let clampedDay  := Nat.min d.day maxDay
  { year := targetYear, month := targetMonth, day := clampedDay }

/-- Advance a calendar date by `years` calendar years (with Feb 29 clamping in non-leap years). -/
def addYears (d : Date) (years : Nat) : Date :=
  d.addMonths (years * 12)

/-- Compute a statutory deadline `months` calendar months from `startDate`. -/
def deadlineAfterMonths (startDate : Date) (months : Nat) : Date :=
  startDate.addMonths months

/-- Check whether `filedOn` is on or before `deadline`. -/
def withinDeadline (filedOn deadline : Date) : Bool :=
  decide (filedOn ≤ deadline)

/-- Check whether `filedOn` is on or before `startDate.addMonths months`. -/
def withinMonthsDeadline (startDate filedOn : Date) (months : Nat) : Bool :=
  decide (filedOn ≤ startDate.addMonths months)

/-- Three-way chronological comparison on `Date`. -/
def compare (a b : Date) : Ordering :=
  if a < b then Ordering.lt
  else if a = b then Ordering.eq
  else Ordering.gt

instance : Ord Date where
  compare := Date.compare

/-- Format a `Date` as `YYYY-MM-DD`. -/
def toISO8601 (d : Date) : String :=
  let pad2 (n : Nat) : String := if n < 10 then "0" ++ Nat.repr n else Nat.repr n
  s!"{d.year}-{pad2 d.month}-{pad2 d.day}"

instance : ToString Date where
  toString := Date.toISO8601

-- ============================================================
-- §3  Order lemmas for Date
-- ============================================================

theorem le_def (a b : Date) :
    (a ≤ b) ↔
      (a.year < b.year ∨
       (a.year = b.year ∧ a.month < b.month) ∨
       (a.year = b.year ∧ a.month = b.month ∧ a.day ≤ b.day)) :=
  Iff.rfl

theorem lt_def (a b : Date) :
    (a < b) ↔
      (a.year < b.year ∨
       (a.year = b.year ∧ a.month < b.month) ∨
       (a.year = b.year ∧ a.month = b.month ∧ a.day < b.day)) :=
  Iff.rfl

/-- Reflexivity of `Date` ordering. -/
theorem le_refl (d : Date) : d ≤ d := by
  rw [le_def]
  right; right
  exact ⟨rfl, rfl, Nat.le_refl _⟩

/-- Transitivity of `Date` ordering. -/
theorem le_trans {a b c : Date} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_def] at *
  omega

/-- Antisymmetry of `Date` ordering. -/
theorem le_antisymm {a b : Date} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_def] at hab hba
  cases a; cases b
  simp only [Date.mk.injEq] at *
  omega

/-- Totality of `Date` ordering. -/
theorem le_total (a b : Date) : a ≤ b ∨ b ≤ a := by
  rw [le_def, le_def]
  omega

/-- Irreflexivity of strict `Date` ordering. -/
theorem lt_irrefl (d : Date) : ¬(d < d) := by
  rw [lt_def]
  omega

/-- Transitivity of strict `Date` ordering. -/
theorem lt_trans {a b c : Date} (hab : a < b) (hbc : b < c) : a < c := by
  rw [lt_def] at *
  omega

/-- Strict inequality implies weak inequality on `Date`. -/
theorem le_of_lt {a b : Date} (h : a < b) : a ≤ b := by
  rw [lt_def] at h
  rw [le_def]
  omega

/-- Negation of `a ≤ b` is equivalent to `b < a`. -/
theorem not_le_iff_lt (a b : Date) : ¬(a ≤ b) ↔ b < a := by
  rw [le_def, lt_def]
  omega

/-- Negation of `a < b` is equivalent to `b ≤ a`. -/
theorem not_lt_iff_le (a b : Date) : ¬(a < b) ↔ b ≤ a := by
  rw [lt_def, le_def]
  omega

-- ============================================================
-- §4  Month-length and `addMonths` validity lemmas
-- ============================================================

/-- Every month has between 28 and 31 days. -/
theorem daysInMonth_bounds (year month : Nat) :
    28 ≤ daysInMonth year month ∧ daysInMonth year month ≤ 31 := by
  unfold daysInMonth
  split <;> try omega
  split <;> omega

/-- The month produced by `addMonths` is always in `1..12`. -/
theorem addMonths_month_bounds (d : Date) (months : Nat) :
    1 ≤ (d.addMonths months).month ∧ (d.addMonths months).month ≤ 12 := by
  simp only [addMonths]
  omega

/-- The day produced by `addMonths` never exceeds `daysInMonth` of the target month
    (end-of-month clamping invariant). -/
theorem addMonths_day_le_daysInMonth (d : Date) (months : Nat) :
    (d.addMonths months).day ≤
      daysInMonth (d.addMonths months).year (d.addMonths months).month := by
  simp only [addMonths]
  exact Nat.min_le_right d.day _

/-- If `1 ≤ d.day`, then `d.addMonths months` has a positive day (`1 ≤ day`). -/
theorem addMonths_day_pos (d : Date) (months : Nat) (hday : 1 ≤ d.day) :
    1 ≤ (d.addMonths months).day := by
  simp only [addMonths]
  have hbounds := (daysInMonth_bounds
    ((d.year * 12 + (d.month - 1) + months) / 12)
    ((d.year * 12 + (d.month - 1) + months) % 12 + 1)).1
  exact Nat.le_min.mpr ⟨hday, by omega⟩

/-- `addMonths` always produces a structurally valid calendar date whenever `1 ≤ d.day`. -/
theorem addMonths_isValid (d : Date) (months : Nat) (hday : 1 ≤ d.day) :
    (d.addMonths months).isValid = true := by
  unfold isValid
  have hm := addMonths_month_bounds d months
  have hd1 := addMonths_day_pos d months hday
  have hd2 := addMonths_day_le_daysInMonth d months
  simp [hm.1, hm.2, hd1, hd2]

/-- Adding 0 months to a valid date returns the same date. -/
theorem addMonths_zero (d : Date) (h : d.isValid = true) :
    d.addMonths 0 = d := by
  unfold isValid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hm1, hm2⟩, hd1⟩, hd2⟩
  cases d with
  | mk y m day =>
    simp only [addMonths, Date.mk.injEq] at *
    have hdiv : (y * 12 + (m - 1) + 0) / 12 = y := by omega
    have hmod : (y * 12 + (m - 1) + 0) % 12 + 1 = m := by omega
    refine ⟨hdiv, hmod, ?_⟩
    rw [hdiv, hmod]
    exact Nat.min_eq_left hd2

/-- Advancing a date with `1 ≤ month ≤ 12` by `months > 0` strictly increases the date. -/
theorem lt_addMonths_of_pos (d : Date) (months : Nat)
    (hm1 : 1 ≤ d.month) (hm2 : d.month ≤ 12) (hpos : 0 < months) :
    d < d.addMonths months := by
  rw [lt_def]
  simp only [addMonths]
  omega

/-- Advancing a valid date by any `months : Nat` never moves backwards in time (`d ≤ d.addMonths months`). -/
theorem le_addMonths (d : Date) (months : Nat) (h : d.isValid = true) :
    d ≤ d.addMonths months := by
  by_cases hzero : months = 0
  · subst hzero
    rw [addMonths_zero d h]
    exact le_refl d
  · have hpos : 0 < months := Nat.pos_of_ne_zero hzero
    unfold isValid at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact le_of_lt (lt_addMonths_of_pos d months h.1.1.1 h.1.1.2 hpos)

-- ============================================================
-- §5  Concrete end-of-month clamping lemmas
-- ============================================================

/-- Jan 31 in a non-leap year (2025) + 1 month clamps to Feb 28, 2025. -/
theorem addMonths_jan31_nonleap :
    (Date.mk 2025 1 31).addMonths 1 = Date.mk 2025 2 28 := rfl

/-- Jan 31 in a leap year (2024) + 1 month clamps to Feb 29, 2024. -/
theorem addMonths_jan31_leap :
    (Date.mk 2024 1 31).addMonths 1 = Date.mk 2024 2 29 := rfl

/-- Aug 31, 2025 + 6 months clamps to Feb 28, 2026 (6-month k.p.c. deadline). -/
theorem addMonths_aug31_six_months :
    (Date.mk 2025 8 31).addMonths 6 = Date.mk 2026 2 28 := rfl

/-- Aug 31, 2023 + 6 months clamps to Feb 29, 2024 (leap-year February). -/
theorem addMonths_aug31_leap_six_months :
    (Date.mk 2023 8 31).addMonths 6 = Date.mk 2024 2 29 := rfl

/-- Mar 31, 2025 + 6 months clamps to Sep 30, 2025. -/
theorem addMonths_mar31_six_months :
    (Date.mk 2025 3 31).addMonths 6 = Date.mk 2025 9 30 := rfl

end Date
end LegalLean
