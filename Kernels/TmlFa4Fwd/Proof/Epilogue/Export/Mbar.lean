-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's mbarrier uses

`epi_mbar_use`: every event of a lane of warp 13 that names an mbarrier and is no initialization is
a parity-0 poll of a ready barrier the lane has not acquired, or the lane's only arrival on a free
barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event} {l : Loc}

/-- **Every mbarrier use of an output lane.** -/
theorem epi_mbar_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 13) (he : X.get (h, k) = some e)
    (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    (∃ (st : Fin 2) (ok : Bool), l = obj L h (208 + 8 * st.val) ∧ e.kind = .wait l 0 ok true .cta ∧
        okPolls l ((X.tr h).take k) = 0) ∨
      ∃ st : Fin 2, l = obj L h (224 + 8 * st.val) ∧ e.kind = .arrive l 0 1 true .cta ∧
        arrivals l ((X.tr h).take k) = 0 := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  have hh := Frame.lt_of_get hX he
  rcases Epilogue.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, -, -, -, hev⟩
  · exact absurd (start_mbar hev hi.2 hm) (fun ⟨c, hc⟩ => hni c hc)
  obtain ⟨-, -, -, -, hL⟩ := (Epilogue.fits hp hX hh hw hσ).2
  rcases epi_site hev hm with ⟨st, hs, hl⟩ | ⟨st, hs, hl⟩
  · obtain ⟨site, rest⟩ := d
    simp only at hs
    subst hs
    obtain ⟨ok, hk⟩ := hev
    refine .inl ⟨st, ok, hl, by rw [hk, hl], ?_⟩
    have h1 := (hL st).1
    simp only [Epilogue.acqd, Nat.lt_irrefl, ↓reduceIte] at h1
    rw [hl, ← h1]
    exact count hσ (.poll st)
  · obtain ⟨site, rest⟩ := d
    simp only at hs
    subst hs
    have hk : e.kind = .arrive (Epilogue.freeLoc L h st) 0 1 true .cta := hev
    refine .inr ⟨st, hl, by rw [hk, hl], ?_⟩
    have h1 := (hL st).2
    rw [hl, show arrivals (Epilogue.freeLoc L h st) ((X.tr h).take k) = n (.freed st) from
      count hσ (.freed st), h1]
    fin_cases st <;> simp [Epilogue.freedAt, Epilogue.frees]

end
end PTX.Kernels.TmlFa4Fwd.Proof
