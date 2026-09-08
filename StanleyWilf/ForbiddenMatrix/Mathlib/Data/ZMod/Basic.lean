module

public import Mathlib.Data.ZMod.Basic

/-!
Adapted from `YaelDillies/ForbiddenMatrix` at commit
`a938c04974d145131c446e8d488b834797ab6ed0`, licensed under Apache-2.0.
Modified for the Stanley-Wilf project and namespaced to avoid exporting an unqualified shim name.
-/

public section

namespace StanleyWilf.ForbiddenMatrix

/-- Compatibility lemma identifying a `Fin n` value with its image under `ZMod.finEquiv`. -/
@[simp, norm_cast] lemma Fin.natCast_val_eq_zmodFinEquiv {n : ℕ} [NeZero n] (a : Fin n) :
    a = ZMod.finEquiv n a := by
  obtain _ | n := n
  · obtain ⟨_, ⟨⟩⟩ := a
  · change (⟨_, _⟩ : ZMod (n + 1)) = ⟨_, _⟩
    congr
    simp
    lia

end StanleyWilf.ForbiddenMatrix
