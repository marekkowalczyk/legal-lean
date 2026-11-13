/-
  LegalLean.Core — Foundation types for verified legal reasoning.

  Architecture: LLMs are heuristic transducers (messy input → structured form);
  Lean 4 is the invariant verifier (checks the logic).

  Key types:
  - `Date`: ISO 8601 calendar date with proper ordering
  - `Authority`: typed enumeration of adjudicatory authorities
  - `Deontic`: permitted / prohibited / obligatory
  - `LegalRule`: a rule with defeasibility metadata
  - `EvidenceFor`: propositions-as-types for legal evidence
  - `FormalisationBoundary`: Hart's open texture as a first-class type

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

import LegalLean.FormalResultAttr

namespace LegalLean

-- ============================================================
-- Date: proper calendar date with structural ordering
-- ============================================================

/-- A calendar date with year, month, and day components.
    ISO 8601 representation: YYYY-MM-DD.
    Ordering is lexicographic over (year, month, day) triples,
    which is total and coincides with chronological order. -/
structure Date where
  year  : Nat
  month : Nat  -- 1–12
  day   : Nat  -- 1–31
  deriving Repr, BEq, DecidableEq

/-- Lexicographic ordering on `Date`, lifting the natural number ordering
    via the triple (year, month, day).  This is a total preorder [reflexive,
    transitive, total] and a partial order [additionally antisymmetric] since
    the components are all `Nat`. -/
instance : LE Date where
  le a b := a.year < b.year ∨
            (a.year = b.year ∧ a.month < b.month) ∨
            (a.year = b.year ∧ a.month = b.month ∧ a.day ≤ b.day)

instance : LT Date where
  lt a b := a.year < b.year ∨
            (a.year = b.year ∧ a.month < b.month) ∨
            (a.year = b.year ∧ a.month = b.month ∧ a.day < b.day)

/-- Decidability of `Date` comparison. Allows `if d1 ≤ d2 then ...` in defs. -/
instance decLeDate (a b : Date) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable
    (a.year < b.year ∨
     (a.year = b.year ∧ a.month < b.month) ∨
     (a.year = b.year ∧ a.month = b.month ∧ a.day ≤ b.day)))

/-- Decidability of strict `Date` comparison (`a < b`). -/
instance decLtDate (a b : Date) : Decidable (a < b) :=
  inferInstanceAs (Decidable
    (a.year < b.year ∨
     (a.year = b.year ∧ a.month < b.month) ∨
     (a.year = b.year ∧ a.month = b.month ∧ a.day < b.day)))

-- ============================================================
-- Jurisdiction & Authority: typed enumeration of adjudicatory bodies
-- ============================================================

/-- Legal jurisdiction of an adjudicatory authority or rule corpus. -/
inductive Jurisdiction where
  /-- United States federal jurisdiction. -/
  | us              : Jurisdiction
  /-- Commonwealth of Australia jurisdiction. -/
  | au              : Jurisdiction
  /-- Republic of Poland (Rzeczpospolita Polska). -/
  | pl              : Jurisdiction
  /-- Council of Europe / European Convention on Human Rights (ECHR). -/
  | councilOfEurope : Jurisdiction
  /-- European Union. -/
  | eu              : Jurisdiction
  /-- Other or user-specified jurisdiction code (e.g. ISO 3166-1 alpha-2). -/
  | other (code : String) : Jurisdiction
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The adjudicatory authorities referenced across the case studies.
    Includes US, Australian, Polish, and European bodies, plus extensible
    constructors (`other`, `withJurisdiction`) so non-US courts and tribunals
    can be named without proxy mappings. -/
inductive Authority where
  /-- Internal Revenue Service (US federal tax authority). -/
  | irs          : Authority
  /-- US Tax Court (federal judicial tribunal for tax disputes). -/
  | taxCourt     : Authority
  /-- IRS and Tax Court jointly (common in IRC §163(h) open texture). -/
  | irsTaxCourt  : Authority
  /-- US Citizenship and Immigration Services. -/
  | uscis        : Authority
  /-- Australian Competition and Consumer Commission. -/
  | accc         : Authority
  /-- Telecommunications Industry Ombudsman (Australia). -/
  | tio          : Authority
  /-- ACCC and TIO jointly (common in TCP Code open texture). -/
  | acccTio      : Authority
  /-- ACCC, TIO, and courts collectively. -/
  | acccTioCourt : Authority
  /-- Provider self-determination, subject to ACCC audit. -/
  | providerAcccc : Authority
  /-- Provider initial determination, reviewable by ACCC. -/
  | providerAcccc2 : Authority
  /-- Sąd Najwyższy (SN) — Supreme Court of Poland. -/
  | sadNajwyzszy : Authority
  /-- Trybunał Konstytucyjny (TK) — Constitutional Tribunal of Poland. -/
  | trybunalKonstytucyjny : Authority
  /-- Naczelny Sąd Administracyjny (NSA) — Supreme Administrative Court of Poland. -/
  | naczelnySadAdministracyjny : Authority
  /-- Sąd apelacyjny — Polish Court of Appeal. -/
  | sadApelacyjny : Authority
  /-- Sąd okręgowy — Polish Regional Court. -/
  | sadOkregowy : Authority
  /-- Sąd rejonowy — Polish District Court. -/
  | sadRejonowy : Authority
  /-- European Court of Human Rights (ECtHR / ETPCz). -/
  | ecthr : Authority
  /-- Extensible constructor for any other named adjudicatory body. -/
  | other (name : String) : Authority
  /-- Extensible constructor pairing an explicit jurisdiction with an authority name. -/
  | withJurisdiction (jurisdiction : Jurisdiction) (name : String) : Authority
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Abbreviation for `Authority.sadNajwyzszy` (Sąd Najwyższy — SN). -/
abbrev Authority.sn : Authority := .sadNajwyzszy

/-- Abbreviation for `Authority.trybunalKonstytucyjny` (Trybunał Konstytucyjny — TK). -/
abbrev Authority.tk : Authority := .trybunalKonstytucyjny

/-- Abbreviation for `Authority.naczelnySadAdministracyjny` (Naczelny Sąd Administracyjny — NSA). -/
abbrev Authority.nsa : Authority := .naczelnySadAdministracyjny

/-- Abbreviation for `Authority.ecthr` (Europejski Trybunał Praw Człowieka — ETPCz). -/
abbrev Authority.etpcz : Authority := .ecthr

/-- Return the legal jurisdiction associated with an `Authority`. -/
def Authority.jurisdiction : Authority → Jurisdiction
  | .irs | .taxCourt | .irsTaxCourt | .uscis => .us
  | .accc | .tio | .acccTio | .acccTioCourt | .providerAcccc | .providerAcccc2 => .au
  | .sadNajwyzszy | .trybunalKonstytucyjny | .naczelnySadAdministracyjny
  | .sadApelacyjny | .sadOkregowy | .sadRejonowy => .pl
  | .ecthr => .councilOfEurope
  | .other name => .other name
  | .withJurisdiction j _ => j

/-- Human-readable display name for an `Authority`. -/
def Authority.displayName : Authority → String
  | .irs                        => "Internal Revenue Service (IRS)"
  | .taxCourt                   => "U.S. Tax Court"
  | .irsTaxCourt                => "IRS / U.S. Tax Court"
  | .uscis                      => "U.S. Citizenship and Immigration Services (USCIS)"
  | .accc                       => "Australian Competition and Consumer Commission (ACCC)"
  | .tio                        => "Telecommunications Industry Ombudsman (TIO)"
  | .acccTio                    => "ACCC / TIO"
  | .acccTioCourt               => "ACCC / TIO / Court"
  | .providerAcccc              => "Provider (subject to ACCC audit)"
  | .providerAcccc2             => "Provider (reviewable by ACCC)"
  | .sadNajwyzszy               => "Sąd Najwyższy (SN)"
  | .trybunalKonstytucyjny      => "Trybunał Konstytucyjny (TK)"
  | .naczelnySadAdministracyjny => "Naczelny Sąd Administracyjny (NSA)"
  | .sadApelacyjny              => "Sąd Apelacyjny"
  | .sadOkregowy                => "Sąd Okręgowy"
  | .sadRejonowy                => "Sąd Rejonowy"
  | .ecthr                      => "European Court of Human Rights (ECtHR)"
  | .other name                 => name
  | .withJurisdiction _ name    => name

-- ============================================================
-- Deontic modalities
-- ============================================================

/-- Deontic modalities: the three fundamental normative positions. -/
inductive Deontic where
  | permitted    : Deontic
  | prohibited   : Deontic
  | obligatory   : Deontic
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A legal rule's priority level for defeat resolution. -/
structure Priority where
  level : Nat
  source : String  -- e.g. "statute", "regulation", "contract", "precedent"
  deriving Repr, BEq

/-- A legal rule with defeasibility metadata.
    Rules can be defeated by higher-priority rules or new evidence.
    This is the core of non-monotonic legal reasoning.

    Note: no `deriving` — contains function-valued field `conclusion`. -/
structure LegalRule (α : Type) where
  id : String
  description : String
  modality : Deontic
  priority : Priority
  /-- The proposition this rule establishes, given evidence of type α. -/
  conclusion : α → Prop
  /-- Conditions under which this rule is defeated. -/
  defeatedBy : List String  -- IDs of rules that can defeat this one
  /-- Guard predicate: whether this rule is applicable to the given facts.
      Defaults to `fun _ => true` (universally applicable) so all existing
      rule definitions compile unchanged.
      Use this to gate temporal or contextual rules — e.g. a post-TCJA
      prohibition is only applicable when `year >= 2018`. -/
  applicable : α → Bool := fun _ => true

/-- Epistemic provenance of legal evidence: distinguishes evidence verified
    against an authoritative primary source or official registry from
    party- or owner-asserted claims. -/
inductive Provenance where
  /-- Verified directly against an authoritative source (statute, official court
      register, certified postal receipt / EPO, notarised deed). -/
  | verifiedAgainstSource : Provenance
  /-- Asserted by a party, applicant, or control owner without independent
      verification against the primary record (default for backward compatibility). -/
  | partyAsserted         : Provenance
  /-- Stipulated or undisputed between the parties (e.g. Art. 229–230 k.p.c.). -/
  | stipulated            : Provenance
  /-- Officially noticed by the court or authority ex officio (Art. 228 k.p.c.). -/
  | officialNotice        : Provenance
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Alias for `Provenance.verifiedAgainstSource`. -/
abbrev Provenance.verified : Provenance := .verifiedAgainstSource

/-- Alias for `Provenance.partyAsserted` (owner-asserted in compliance contexts). -/
abbrev Provenance.ownerAsserted : Provenance := .partyAsserted

/-- Whether a `Provenance` value represents independently verified evidence
    (verified against source or officially noticed ex officio). -/
def Provenance.isVerified : Provenance → Bool
  | .verifiedAgainstSource => true
  | .officialNotice        => true
  | .partyAsserted         => false
  | .stipulated            => false

/-- Evidence for a legal proposition.
    Propositions-as-types: if you can construct an `EvidenceFor P`,
    then P is established (subject to defeasibility).

    Note: no `deriving` — contains Prop-valued field `witness`. -/
structure EvidenceFor (P : Prop) where
  source : String           -- provenance: "statute", "testimony", "document", etc.
  artifact : Option String  -- reference to supporting document/record
  /-- The actual proof witness. -/
  witness : P
  /-- Epistemic verification status of the evidence.
      Defaults to `.partyAsserted` (matching legacy behaviour) so existing
      code keeps compiling without changes. -/
  provenance : Provenance := .partyAsserted

/-- Smart constructor for source-verified evidence (`Provenance.verifiedAgainstSource`). -/
def EvidenceFor.verified {P : Prop} (source : String) (artifact : Option String) (witness : P)
    : EvidenceFor P :=
  { source, artifact, witness, provenance := .verifiedAgainstSource }

/-- Smart constructor for party/owner-asserted evidence (`Provenance.partyAsserted`). -/
def EvidenceFor.asserted {P : Prop} (source : String) (artifact : Option String) (witness : P)
    : EvidenceFor P :=
  { source, artifact, witness, provenance := .partyAsserted }

/-- Check whether `EvidenceFor P` has independent source or official verification. -/
def EvidenceFor.isVerified {P : Prop} (e : EvidenceFor P) : Bool :=
  e.provenance.isVerified

/-- Default `EvidenceFor` construction has `.partyAsserted` provenance. -/
theorem EvidenceFor.default_provenance_eq_partyAsserted {P : Prop}
    (s : String) (a : Option String) (w : P) :
    ({ source := s, artifact := a, witness := w : EvidenceFor P }).provenance = .partyAsserted :=
  rfl

/-- `EvidenceFor.verified` produces verified evidence. -/
theorem EvidenceFor.verified_isVerified {P : Prop}
    (s : String) (a : Option String) (w : P) :
    (EvidenceFor.verified s a w).isVerified = true :=
  rfl

/-- `EvidenceFor.asserted` produces unverified (party-asserted) evidence. -/
theorem EvidenceFor.asserted_not_isVerified {P : Prop}
    (s : String) (a : Option String) (w : P) :
    (EvidenceFor.asserted s a w).isVerified = false :=
  rfl

/-
  FormalisationBoundary — The intellectually novel contribution.

  Hart's "open texture" (The Concept of Law, 1961): legal concepts have a
  core of settled meaning and a penumbra of uncertainty. Prior work (DDL,
  Catala, L4L, LegalRuleML) treats this as an external limitation on
  formalisation. We encode it WITHIN the type system.

  `RequiresHumanDetermination` is a typeclass marking propositions where
  formal verification must yield to human judgment. Subclasses distinguish:
  - `Vague`: the concept has a core/penumbra distinction (e.g. "reasonable")
  - `Discretionary`: an authority has discretion to decide (e.g. USCIS adjudicator)
-/

/-- Typeclass marking propositions that require human determination.
    Any proposition `P` with this instance cannot be fully machine-verified. -/
class RequiresHumanDetermination (P : Prop) where
  reason : String
  /-- Which authority or role must make this determination. -/
  authority : Authority

/-- Vague concepts: core cases are clear, penumbral cases are not.
    Example: "extraordinary ability" in O-1 visa criteria. -/
class Vague (P : Prop) extends RequiresHumanDetermination P where
  /-- Description of the settled core meaning. -/
  core : String
  /-- Description of the penumbral (contested) region. -/
  penumbra : String

/-- Discretionary determinations: an authority has power to decide.
    Example: USCIS adjudicator deciding "comparable evidence" under O-1. -/
class Discretionary (P : Prop) extends RequiresHumanDetermination P where
  /-- The scope of discretion granted. -/
  scope : String
  /-- Constraints on the exercise of discretion (if any). -/
  constraints : List String

/-- The formalisation boundary itself: wraps a proposition with metadata
    about whether it is fully formalisable, rejected/inadmissible, vague, or discretionary. -/
inductive FormalisationBoundary (P : Sort _) where
  /-- Fully formalisable: can be verified by the type checker alone. -/
  | formal (proof : P) : FormalisationBoundary P
  /-- Explicitly rejected or inadmissible on formal/procedural grounds
      (e.g. odrzucenie pozwu / apelacji / skargi), replacing the legacy
      `FormalisationBoundary.formal False` encoding. -/
  | rejected (reason : String) (authority : Option Authority := none) : FormalisationBoundary P
  /-- Requires human determination: annotated with why and which authority. -/
  | boundary (reason : String) (authority : Authority) : FormalisationBoundary P
  /-- Mixed: partially formal, partially human. The `formalPart` is verified;
      the `humanPart` is annotated. -/
  | mixed (formalPart : String) (humanPart : String) : FormalisationBoundary P

/-- Alias for `FormalisationBoundary.rejected` representing procedural inadmissibility
    (e.g. odrzucenie pisma / środka zaskarżenia). -/
abbrev FormalisationBoundary.inadmissible {P : Sort _}
    (reason : String) (authority : Option Authority := none) : FormalisationBoundary P :=
  FormalisationBoundary.rejected reason authority

/-- Proof-carrying outcome for a legal proposition `P : Prop`.
    Unlike `FormalisationBoundary.formal False` (which only type-checks when the
    parameter is `Prop` rather than a specific proposition `P`),
    `LegalOutcome.rejected` carries an explicit refutation `¬P` verified by the
    Lean 4 kernel alongside the rejection reason and optional adjudicating authority. -/
inductive LegalOutcome (P : Prop) where
  /-- Proposition `P` is formally established with proof `proof : P`. -/
  | sustained (proof : P) : LegalOutcome P
  /-- Proposition `P` is formally refuted / rejected / inadmissible with `refutation : ¬P`. -/
  | rejected (reason : String) (refutation : ¬P) (authority : Option Authority := none) : LegalOutcome P
  /-- Open texture or discretion: requires human determination by `authority`. -/
  | boundary (reason : String) (authority : Authority) : LegalOutcome P
  /-- Partially formal, partially human-determined. -/
  | mixed (formalPart : String) (humanPart : String) : LegalOutcome P

/-- Alias for `LegalOutcome.rejected` emphasizing procedural inadmissibility. -/
abbrev LegalOutcome.inadmissible {P : Prop}
    (reason : String) (refutation : ¬P) (authority : Option Authority := none) : LegalOutcome P :=
  LegalOutcome.rejected reason refutation authority

/-- Project a `LegalOutcome P` to `FormalisationBoundary P`. -/
def LegalOutcome.toBoundary {P : Prop} : LegalOutcome P → FormalisationBoundary P
  | .sustained pf      => .formal pf
  | .rejected r _ auth => .rejected r auth
  | .boundary r auth   => .boundary r auth
  | .mixed fp hp       => .mixed fp hp

end LegalLean
