/-
  LegalLean.CaseStudies.PL.CivilProcedure — Polish Civil Procedure (k.p.c.)
  Procedural Admissibility, 6-Month Calendar-Date Deadline, and Rejection.

  Domain:
  Models a procedural admissibility check under the Polish Code of Civil Procedure
  (Kodeks postępowania cywilnego — k.p.c.) before a Sąd Okręgowy (`Authority.sadOkregowy`),
  subject to a 6-month calendar-date filing deadline calculated in accordance with
  Art. 165 § 1 k.p.c. in connection with Art. 112 k.c. (end-of-month clamping).

  Key features demonstrated:
  1. Polish judicial authorities (`Authority.sadOkregowy`, `Authority.sadApelacyjny`,
     `Authority.sadNajwyzszy`, `Authority.trybunalKonstytucyjny`, `Authority.ecthr`).
  2. Calendar-date deadlines (`Date.addMonths 6` with end-of-month clamping).
  3. Epistemic provenance in `EvidenceFor` (`Provenance.verifiedAgainstSource`
     for court-registry / EPO postal proof vs `Provenance.partyAsserted`).
  4. Explicit rejection / inadmissibility outcome (`FormalisationBoundary.rejected` /
     `FormalisationBoundary.inadmissible` and `LegalOutcome.rejected` carrying `¬P`)
     for formal rejection (*odrzucenie pisma / skargi*, e.g. Art. 373 § 1 / Art. 410 § 1 k.p.c.),
     rather than encoding rejection as `FormalisationBoundary.formal False`.
  5. Defeasible restoration of a missed deadline (*przywrócenie terminu*, Art. 168 § 1 k.p.c.),
     where absence of fault (*brak winy strony*) is a `Vague` open-texture determination
     by the Sąd Okręgowy.

  IMPORTANT: All facts, party identifiers, and docket references in this module
  are strictly HYPOTHETICAL (`HYP-PL-SO-001`, `HYP-PL-SO-002`, etc.).
  No real names or case data are used.
-/

import LegalLean.Core
import LegalLean.Defeasible
import LegalLean.Solver
import LegalLean.Time

set_option autoImplicit false

namespace LegalLean.CaseStudies.PL.CivilProcedure

open LegalLean

-- ============================================================
-- §1  Domain types for Polish civil procedure (k.p.c.)
-- ============================================================

/-- Statutory 6-month procedural deadline (in calendar months). -/
def statutoryDeadlineMonths : Nat := 6

/-- A hypothetical procedural filing submitted to a Sąd Okręgowy. -/
structure ProceduralFiling where
  /-- Hypothetical synthetic identifier (e.g. `"HYP-PL-SO-001"`). -/
  id : String
  /-- Date on which the triggering decision/notice was served (data doręczenia). -/
  serviceDate : Date
  /-- Date on which the pleading was filed or posted at a designated operator
      (data wniesienia pisma, Art. 165 § 2 k.p.c.). -/
  filingDate : Date
  /-- Epistemic provenance of the service and filing date evidence
      (e.g. `.verifiedAgainstSource` from EPO / postal registry vs `.partyAsserted`). -/
  dateProvenance : Provenance := .partyAsserted
  /-- Whether the statutory court fee (opłata sądowa) was paid or exempted. -/
  courtFeePaid : Bool
  /-- Whether formal requirements under Art. 126 / Art. 368 k.p.c. were met. -/
  formalRequirementsMet : Bool
  /-- Whether the party filed a motion to restore the missed deadline
      (wniosek o przywrócenie terminu, Art. 168 § 1 k.p.c.). -/
  restorationMotionFiled : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Compute the 6-month calendar deadline from `serviceDate` under
    Art. 165 § 1 k.p.c. in connection with Art. 112 k.c. -/
def computeSixMonthDeadline (f : ProceduralFiling) : Date :=
  f.serviceDate.addMonths statutoryDeadlineMonths

-- ============================================================
-- §2  Formalisable admissibility predicates
-- ============================================================

/-- The filing was submitted on or before the 6-month calendar deadline. -/
def isTimely (f : ProceduralFiling) : Prop :=
  f.filingDate ≤ computeSixMonthDeadline f

instance decIsTimely (f : ProceduralFiling) : Decidable (isTimely f) :=
  inferInstanceAs (Decidable (f.filingDate ≤ computeSixMonthDeadline f))

/-- Formal fiscal and structural prerequisites are satisfied. -/
def meetsFormalPrerequisites (f : ProceduralFiling) : Prop :=
  f.courtFeePaid = true ∧ f.formalRequirementsMet = true

instance decMeetsFormalPrerequisites (f : ProceduralFiling) :
    Decidable (meetsFormalPrerequisites f) :=
  inferInstanceAs (Decidable (f.courtFeePaid = true ∧ f.formalRequirementsMet = true))

/-- Dates are backed by source-verified or officially noticed provenance. -/
def hasVerifiedProvenance (f : ProceduralFiling) : Prop :=
  f.dateProvenance.isVerified = true

instance decHasVerifiedProvenance (f : ProceduralFiling) :
    Decidable (hasVerifiedProvenance f) :=
  inferInstanceAs (Decidable (f.dateProvenance.isVerified = true))

/-- Full formal admissibility proposition: timely, formal prerequisites met,
    and dates verified against the court/postal source record. -/
def AdmissibleInSadOkregowy (f : ProceduralFiling) : Prop :=
  isTimely f ∧ meetsFormalPrerequisites f ∧ hasVerifiedProvenance f

instance decAdmissibleInSadOkregowy (f : ProceduralFiling) :
    Decidable (AdmissibleInSadOkregowy f) :=
  inferInstanceAs (Decidable (isTimely f ∧ meetsFormalPrerequisites f ∧ hasVerifiedProvenance f))

-- ============================================================
-- §3  Open texture: Art. 168 § 1 k.p.c. ("bez swojej winy")
-- ============================================================

/-- Art. 168 § 1 k.p.c.: Whether a party missed the procedural deadline
    "without fault" (*bez swojej winy*), justifying restoration of the time limit
    (*przywrócenie terminu*). -/
axiom MissedDeadlineWithoutFault : ProceduralFiling → Prop

variable (f : ProceduralFiling) in
instance vague_art168_lack_of_fault : Vague (MissedDeadlineWithoutFault f) where
  reason := "Art. 168 § 1 k.p.c.: restoration of a procedural deadline requires " ++
            "showing that the party failed to perform the procedural act 'bez swojej winy' " ++
            "(without fault), measured by an objective standard of diligence"
  authority := Authority.sadOkregowy
  core := "Sudden severe hospitalisation, documented force majeure, or official court " ++
          "misinstruction preventing timely filing"
  penumbra := "Sudden illness not requiring hospitalisation, reliance on a professional " ++
              "representative's clerical error, or postal disruption near the deadline"

/-- Constitutional proportionality review by Trybunał Konstytucyjny (`Authority.trybunalKonstytucyjny`)
    or right-to-a-court review under Art. 6 ECHR (`Authority.ecthr`) for excessive formalism. -/
axiom ExcessiveProceduralFormalism : ProceduralFiling → Prop

variable (f : ProceduralFiling) in
instance disc_echr_art6_access_to_court : Discretionary (ExcessiveProceduralFormalism f) where
  reason := "Art. 45 ust. 1 Konstytucji RP / Art. 6 § 1 ECHR: whether strict rejection " ++
            "constitutes disproportionate restriction on access to a court"
  authority := Authority.ecthr
  scope := "Assessment of proportionality between procedural sanction (odrzucenie) and " ++
           "the principle of legal certainty"
  constraints := [
    "Must respect res iudicata and stability of final judgments",
    "Must consider whether the party acted with due diligence",
    "Reviewed in domestic cassation by Sąd Najwyższy (SN) and internationally by ECtHR"
  ]

-- ============================================================
-- §4  Defeasible rules and defeat graph (k.p.c.)
-- ============================================================

/-- R1: Base admissibility rule before the Sąd Okręgowy. -/
def R1_AdmissibleFiling : LegalRule ProceduralFiling where
  id := "KPC-R1-Admissible"
  description := "A procedural filing submitted within 6 calendar months of service " ++
                 "(Art. 165 § 1 k.p.c. + Art. 112 k.c.), with court fee paid and formal " ++
                 "requirements satisfied, is admissible before the Sąd Okręgowy"
  modality := Deontic.permitted
  priority := ⟨1, "ustawa (k.p.c. — ogólna dopuszczalność pisma)"⟩
  conclusion := fun f => AdmissibleInSadOkregowy f
  defeatedBy := ["KPC-R2-UntimelyRejected"]
  applicable := fun f =>
    f.courtFeePaid && f.formalRequirementsMet && f.dateProvenance.isVerified

/-- R2: Mandatory rejection (*odrzucenie*) of a late filing (Art. 373 § 1 / Art. 410 § 1 k.p.c.). -/
def R2_UntimelyRejected : LegalRule ProceduralFiling where
  id := "KPC-R2-UntimelyRejected"
  description := "Sąd Okręgowy rejects (odrzuca) a procedural filing submitted after " ++
                 "the 6-month calendar deadline has expired"
  modality := Deontic.prohibited
  priority := ⟨2, "ustawa (Art. 373 § 1 / Art. 410 § 1 k.p.c. — odrzucenie spóźnionego pisma)"⟩
  conclusion := fun f => ¬isTimely f
  defeatedBy := ["KPC-R3-RestorationArt168"]
  applicable := fun f => !(Date.withinDeadline f.filingDate (computeSixMonthDeadline f))

/-- R3: Restoration of deadline (*przywrócenie terminu*, Art. 168 § 1 k.p.c.).
    Defeats automatic rejection when a restoration motion is filed, routing the case
    to judicial assessment of lack of fault by the Sąd Okręgowy. -/
def R3_RestorationArt168 : LegalRule ProceduralFiling where
  id := "KPC-R3-RestorationArt168"
  description := "Art. 168 § 1 k.p.c.: if the party files a motion to restore the " ++
                 "missed deadline and demonstrates lack of fault (bez swojej winy), " ++
                 "the Sąd Okręgowy may restore the deadline"
  modality := Deontic.permitted
  priority := ⟨3, "ustawa (Art. 168 § 1 k.p.c. — lex specialis przywrócenie terminu)"⟩
  conclusion := fun f => MissedDeadlineWithoutFault f
  defeatedBy := []
  applicable := fun f => f.restorationMotionFiled

/-- Defeat D1: Untimeliness defeats base admissibility. -/
def defeat_Untimely_Admissible : Defeats where
  defeater := "KPC-R2-UntimelyRejected"
  defeated := "KPC-R1-Admissible"
  reason := "Prekluzja procesowa: expiry of the 6-month statutory time limit mandates " ++
            "rejection (odrzucenie) under k.p.c."
  strict := false

/-- Defeat D2: Motion for restoration (Art. 168 § 1 k.p.c.) defeats automatic rejection. -/
def defeat_Restoration_Untimely : Defeats where
  defeater := "KPC-R3-RestorationArt168"
  defeated := "KPC-R2-UntimelyRejected"
  reason := "lex specialis: Art. 168 § 1 k.p.c. allows restoration of a missed deadline " ++
            "upon proving lack of fault before the Sąd Okręgowy"
  strict := false

/-- All defeat relations in the Polish k.p.c. admissibility model. -/
def allDefeats : List Defeats :=
  [defeat_Untimely_Admissible, defeat_Restoration_Untimely]

-- ============================================================
-- §5  Admissibility evaluation using explicit `rejected` outcomes
-- ============================================================

/-- Evaluate procedural admissibility of a filing before the Sąd Okręgowy,
    returning `LegalOutcome (AdmissibleInSadOkregowy f)`.

    Every rejection branch returns `LegalOutcome.rejected` with a machine-verified
    refutation proof `¬AdmissibleInSadOkregowy f` and `some Authority.sadOkregowy`,
    EXCEPT when a restoration motion under Art. 168 § 1 k.p.c. is pending or when
    date provenance is merely party-asserted (`.partyAsserted`), which return
    `LegalOutcome.boundary` for determination by `Authority.sadOkregowy`. -/
def evaluateFilingOutcome (f : ProceduralFiling) : LegalOutcome (AdmissibleInSadOkregowy f) :=
  if h_fee : !f.courtFeePaid then
    LegalOutcome.rejected
      "Odrzucenie pisma: nieuiszczona opłata sądowa (unpaid court fee)"
      (by
        intro ⟨_, ⟨hpaid, _⟩, _⟩
        simp [hpaid] at h_fee)
      (some Authority.sadOkregowy)
  else if h_form : !f.formalRequirementsMet then
    LegalOutcome.rejected
      "Odrzucenie pisma: nieusunięte braki formalne (unremedied formal defects, Art. 130 k.p.c.)"
      (by
        intro ⟨_, ⟨_, hreq⟩, _⟩
        simp [hreq] at h_form)
      (some Authority.sadOkregowy)
  else if h_time : f.filingDate ≤ computeSixMonthDeadline f then
    if h_prov : f.dateProvenance.isVerified = true then
      have hpaid : f.courtFeePaid = true := by cases h : f.courtFeePaid <;> simp_all
      have hreq  : f.formalRequirementsMet = true := by cases h : f.formalRequirementsMet <;> simp_all
      LegalOutcome.sustained ⟨h_time, ⟨hpaid, hreq⟩, h_prov⟩
    else
      LegalOutcome.boundary
        ("Daty doręczenia i wniesienia pisma są jedynie twierdzeniem strony " ++
         "(Provenance.partyAsserted). Sąd Okręgowy musi zweryfikować EPO / stempel " ++
         "pocztowy w aktach sprawy (Art. 165 § 2 k.p.c.).")
        Authority.sadOkregowy
  else
    if f.restorationMotionFiled then
      LegalOutcome.boundary
        ("Pismo wniesione po upływie 6-miesięcznego terminu (Art. 165 § 1 k.p.c. w zw. z " ++
         "Art. 112 k.c.), lecz złożono wniosek o przywrócenie terminu (Art. 168 § 1 k.p.c.). " ++
         "Sąd Okręgowy musi rozstrzygnąć, czy uchybienie nastąpiło 'bez winy strony'.")
        Authority.sadOkregowy
    else
      LegalOutcome.rejected
        ("Odrzucenie pisma (Art. 373 § 1 / Art. 410 § 1 k.p.c.): przekroczono 6-miesięczny " ++
         "termin kalendarzowy liczony zgodnie z Art. 112 k.c. w zw. z Art. 165 § 1 k.p.c.")
        (by
          intro ⟨htime, _, _⟩
          exact h_time htime)
        (some Authority.sadOkregowy)

/-- Evaluate procedural admissibility directly as a `FormalisationBoundary`,
    using `FormalisationBoundary.rejected` (alias `inadmissible`) instead of
    the legacy `FormalisationBoundary.formal False`. -/
def assessAdmissibility (f : ProceduralFiling)
    : FormalisationBoundary (AdmissibleInSadOkregowy f) :=
  (evaluateFilingOutcome f).toBoundary

/-- Construct source-verified `EvidenceFor ( isTimely f )` when the filing is within
    the 6-month calendar deadline. -/
def mkVerifiedTimelinessEvidence (f : ProceduralFiling) (h : isTimely f)
    : EvidenceFor (isTimely f) :=
  EvidenceFor.verified
    "Elektroniczne Potwierdzenie Odbioru (EPO) oraz stempel pocztowy operatora wyznaczonego (Art. 165 § 2 k.p.c.)"
    (some s!"Akta sprawy {f.id} — karta doręczenia {f.serviceDate} / nadania {f.filingDate}")
    h

-- ============================================================
-- §6  Hypothetical scenarios (strictly synthetic data)
-- ============================================================

/-- Hypothetical Case 1 (`HYP-PL-SO-001`):
    Decision served on August 31, 2025 (`2025-08-31`).
    By Art. 112 k.c. in connection with Art. 165 § 1 k.p.c., the 6-month deadline
    clamps to the last day of February 2026 (`2026-02-28`, non-leap year).
    The pleading is filed on `2026-02-28` with source-verified provenance (`.verifiedAgainstSource`)
    and court fee paid. -/
def hypTimelyEomFiling : ProceduralFiling where
  id := "HYP-PL-SO-001"
  serviceDate := ⟨2025, 8, 31⟩
  filingDate := ⟨2026, 2, 28⟩
  dateProvenance := .verifiedAgainstSource
  courtFeePaid := true
  formalRequirementsMet := true
  restorationMotionFiled := false

/-- Hypothetical Case 2 (`HYP-PL-SO-002`):
    Same service date (`2025-08-31`, 6-month deadline `2026-02-28`),
    but filed one day late on March 1, 2026 (`2026-03-01`) with no motion to
    restore the deadline. Decided by Sąd Okręgowy as `.rejected` (*odrzucenie*). -/
def hypLateFilingNoRestoration : ProceduralFiling where
  id := "HYP-PL-SO-002"
  serviceDate := ⟨2025, 8, 31⟩
  filingDate := ⟨2026, 3, 1⟩
  dateProvenance := .verifiedAgainstSource
  courtFeePaid := true
  formalRequirementsMet := true
  restorationMotionFiled := false

/-- Hypothetical Case 3 (`HYP-PL-SO-003`):
    Same late filing on `2026-03-01`, but accompanied by an Art. 168 § 1 k.p.c.
    motion to restore the deadline (*wniosek o przywrócenie terminu*).
    Outcome shifts from `.rejected` to `.boundary` before `Authority.sadOkregowy`. -/
def hypLateFilingWithRestoration : ProceduralFiling where
  id := "HYP-PL-SO-003"
  serviceDate := ⟨2025, 8, 31⟩
  filingDate := ⟨2026, 3, 1⟩
  dateProvenance := .verifiedAgainstSource
  courtFeePaid := true
  formalRequirementsMet := true
  restorationMotionFiled := true

/-- Hypothetical Case 4 (`HYP-PL-SO-004`):
    Timely dates (`2025-08-31` to `2026-02-28`), but the dates are only
    party-asserted (`Provenance.partyAsserted`, the default) without court registry
    verification. Returns `.boundary` requiring verification by `Authority.sadOkregowy`. -/
def hypUnverifiedProvenanceFiling : ProceduralFiling where
  id := "HYP-PL-SO-004"
  serviceDate := ⟨2025, 8, 31⟩
  filingDate := ⟨2026, 2, 28⟩
  dateProvenance := .partyAsserted
  courtFeePaid := true
  formalRequirementsMet := true
  restorationMotionFiled := false

-- ============================================================
-- §7  Machine-verified theorems (all proved without extra axioms)
-- ============================================================

/-- Theorem PL1: For hypothetical filing `HYP-PL-SO-001` (served 2025-08-31),
    the 6-month statutory deadline under Art. 112 k.c. / Art. 165 § 1 k.p.c.
    is February 28, 2026 (`2026-02-28`) via end-of-month clamping. -/
@[formal_result]
theorem hypTimelyEomFiling_deadline_eq_feb28 :
    computeSixMonthDeadline hypTimelyEomFiling = ⟨2026, 2, 28⟩ :=
  rfl

/-- Theorem PL2: Hypothetical filing `HYP-PL-SO-001` on 2026-02-28 with
    `.verifiedAgainstSource` provenance is formally admissible (`FormalisationBoundary.formal`). -/
@[formal_result]
theorem hypTimelyEomFiling_is_formal :
    ∃ pf : AdmissibleInSadOkregowy hypTimelyEomFiling,
      assessAdmissibility hypTimelyEomFiling = FormalisationBoundary.formal pf := by
  refine ⟨⟨by decide, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Theorem PL3: Hypothetical filing `HYP-PL-SO-002` (filed 2026-03-01, 1 day after
    the clamped 6-month deadline 2026-02-28, with no restoration motion) is
    explicitly rejected (`FormalisationBoundary.rejected`) by `Authority.sadOkregowy`. -/
@[formal_result]
theorem hypLateFilingNoRestoration_is_rejected :
    ∃ reason : String,
      assessAdmissibility hypLateFilingNoRestoration =
        FormalisationBoundary.rejected reason (some Authority.sadOkregowy) := by
  exact ⟨_, rfl⟩

/-- Theorem PL4 (Non-monotonicity / Art. 168 § 1 k.p.c.):
    Filing a restoration motion (`restorationMotionFiled = true`) for the same
    late filing (`HYP-PL-SO-003`) changes the outcome from `FormalisationBoundary.rejected`
    to `FormalisationBoundary.boundary` decided by `Authority.sadOkregowy`. -/
@[formal_result]
theorem restoration_motion_shifts_rejected_to_boundary :
    (∃ r1, assessAdmissibility hypLateFilingNoRestoration =
             FormalisationBoundary.rejected r1 (some Authority.sadOkregowy)) ∧
    (∃ r2, assessAdmissibility hypLateFilingWithRestoration =
             FormalisationBoundary.boundary r2 Authority.sadOkregowy) := by
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Theorem PL5 (Provenance enforcement):
    When a timely filing (`HYP-PL-SO-004`) carries only `Provenance.partyAsserted`
    rather than `Provenance.verifiedAgainstSource`, `assessAdmissibility` refuses to
    emit `FormalisationBoundary.formal` and instead returns `FormalisationBoundary.boundary`
    for `Authority.sadOkregowy`. -/
@[formal_result]
theorem party_asserted_provenance_yields_boundary :
    ∃ reason : String,
      assessAdmissibility hypUnverifiedProvenanceFiling =
        FormalisationBoundary.boundary reason Authority.sadOkregowy := by
  exact ⟨_, rfl⟩

/-- Theorem PL6 (General formal admissibility theorem):
    Any filing that is timely (`filingDate ≤ serviceDate.addMonths 6`), has paid
    the court fee, meets formal requirements, and has verified provenance
    evaluates to `FormalisationBoundary.formal`. -/
@[formal_result]
theorem general_timely_verified_is_formal
    (f : ProceduralFiling)
    (h_fee : f.courtFeePaid = true)
    (h_form : f.formalRequirementsMet = true)
    (h_time : f.filingDate ≤ computeSixMonthDeadline f)
    (h_prov : f.dateProvenance.isVerified = true) :
    ∃ pf : AdmissibleInSadOkregowy f,
      assessAdmissibility f = FormalisationBoundary.formal pf := by
  unfold assessAdmissibility evaluateFilingOutcome
  simp [h_fee, h_form, h_time, h_prov, LegalOutcome.toBoundary]
  exact ⟨h_time, ⟨h_fee, h_form⟩, h_prov⟩

/-- Theorem PL7 (General untimeliness rejection theorem):
    Any filing with paid fee and satisfied formal requirements that misses the
    6-month calendar deadline (`¬(filingDate ≤ serviceDate.addMonths 6)`) and has
    no restoration motion is explicitly `FormalisationBoundary.rejected` by
    `Authority.sadOkregowy`. -/
@[formal_result]
theorem general_late_without_restoration_is_rejected
    (f : ProceduralFiling)
    (h_fee : f.courtFeePaid = true)
    (h_form : f.formalRequirementsMet = true)
    (h_late : ¬(f.filingDate ≤ computeSixMonthDeadline f))
    (h_no_rest : f.restorationMotionFiled = false) :
    ∃ reason : String,
      assessAdmissibility f =
        FormalisationBoundary.rejected reason (some Authority.sadOkregowy) := by
  unfold assessAdmissibility evaluateFilingOutcome
  simp [h_fee, h_form, h_late, h_no_rest, LegalOutcome.toBoundary]

/-- Theorem PL8: The defeat graph for the Polish k.p.c. rules is acyclic. -/
@[formal_result]
theorem defeat_graph_acyclic :
    ∀ d ∈ allDefeats, d.defeater ≠ d.defeated := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl | rfl
  · simp [defeat_Untimely_Admissible]
  · simp [defeat_Restoration_Untimely]

/-- Theorem PL9: All Polish court constructors on `Authority` map to `Jurisdiction.pl`,
    and `Authority.ecthr` maps to `Jurisdiction.councilOfEurope`. -/
@[formal_result]
theorem polish_authorities_have_pl_jurisdiction :
    Authority.sadNajwyzszy.jurisdiction = Jurisdiction.pl ∧
    Authority.trybunalKonstytucyjny.jurisdiction = Jurisdiction.pl ∧
    Authority.naczelnySadAdministracyjny.jurisdiction = Jurisdiction.pl ∧
    Authority.sadApelacyjny.jurisdiction = Jurisdiction.pl ∧
    Authority.sadOkregowy.jurisdiction = Jurisdiction.pl ∧
    Authority.sadRejonowy.jurisdiction = Jurisdiction.pl ∧
    Authority.ecthr.jurisdiction = Jurisdiction.councilOfEurope :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LegalLean.CaseStudies.PL.CivilProcedure
