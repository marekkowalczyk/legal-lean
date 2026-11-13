/-
  LegalLean.FormalResultAttr — Tag attribute `@[formal_result]` for declarations
  that must be audited by `lake exe axiomguard`.
-/

import Lean

namespace LegalLean

/-- Tag attribute marking a definition or theorem as a verified `formal` legal result.
    `lake exe axiomguard` verifies that every declaration tagged `@[formal_result]`
    (as well as every declaration constructing or proving `FormalisationBoundary.formal`,
    `FormalisationBoundary.rejected`, `LegalOutcome.sustained`, or `LegalOutcome.rejected`)
    depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). -/
initialize formalResultAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `formal_result
    "Mark a declaration as a verified formal legal result audited by axiomguard."

end LegalLean
