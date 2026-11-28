-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFSat
public import Lemmas.Flow.TypedSingleG

@[expose] public section

/-! # A guarded branch under the lane invariant, with the tags checked by `tagsSatF`

`SegQT.braS` is `SegQT.bra` (`Lemmas/Flow/TypedSingleG.lean`) for a target whose table serves the
tags of the branch only up to `TagF.sat`. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem SegQT.braS {qt : Nat → EnvF} {R : TState → Prop} {a pc p target : Nat} {uni : Bool}
    {F G : List (Nat × Value)} (pick : Bool)
    (h1 : SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) a F pc G)
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hL : ∀ t x, x ∈ A → x.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsSatF (qt (if pick then target else pc + 1)) (qt pc) = true)
    (hp : ∀ u, At u pc G → QTF qt u → u.regs p = some (.pred pick)) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) a F
      (if pick then target else pc + 1) G := by
  intro t ht hq0
  obtain ⟨u, hr, hu, hQ, hT⟩ := h1 t ht hq0
  obtain ⟨v, hl, hregs, hv⟩ := Havoc.run_bra_regs hc pick hu (hp u hu hQ) (hL u) hA
  have hr' := hr.trans (run_rtg hl)
  refine ⟨v, hr', hv, ?_, fun w hw => hT w ((run_rtg hl).trans hw)⟩
  have hQ' : TypedF (qt pc) u := by simpa [QTF, hu.1] using hQ
  have : TypedF (qt (if pick then target else pc + 1)) v := by
    intro r tg hr''
    rw [hregs]
    exact typedF_of_tagsSat hq hQ' r tg hr''
  simpa [QTF, hv.1] using this

end PTX.Flow.TyG
