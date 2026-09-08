module

public import Mathlib.Data.Fintype.Defs

/-!
Adapted from `YaelDillies/ForbiddenMatrix` at commit
`a938c04974d145131c446e8d488b834797ab6ed0`, licensed under Apache-2.0.
Modified for the Stanley-Wilf project and namespaced to avoid exporting unqualified shim names.
-/

public section

namespace StanleyWilf.ForbiddenMatrix

variable {α β : Type*} [LinearOrder α] [LinearOrder β] [Fintype α] [DecidableLT α] [DecidableLT β]
  {f : α → β}

/-- Compatibility instance for deciding strict monotonicity on a finite ordered domain. -/
instance : Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))
/-- Compatibility instance for deciding strict antitonicity on a finite ordered domain. -/
instance : Decidable (StrictAnti f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

end StanleyWilf.ForbiddenMatrix
