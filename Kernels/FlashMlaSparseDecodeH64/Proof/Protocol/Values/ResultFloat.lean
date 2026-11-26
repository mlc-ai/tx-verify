-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaSum
import Lemmas.Tcgen05.ValuesByTcOrder

@[expose] public section

/-! # A done MMA's result is a number

Every `TcMma.Result` of a done MMA reads as a real (`result_float`), by induction along the
tcgen05 order: `mma_result_sum` gives the result as the sum of the products plus the number its
accumulator source's word reads as, and that source is an earlier done MMA's result (the
induction) or a store's word (`hS`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The results of a done MMA read as numbers**: the claim of `result_float` at one event. -/
def RfClaim (L : Launch) (X : Execution) (w : EvId) : Prop :=
  ∀ cell old, X.async.mmaDone w = true → TcMma.Result L Assumptions.all X w cell old →
    ∃ r : ℝ, valFloat .f32 old = .ok r

/-- **One step of the induction on the tcgen05 order**: a done MMA's result reads as a number when
the results of the done MMAs before it do (`ih`), the words stores before it write do (`hS`) and
its operand elements decode (`hE`). -/
theorem result_float_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) (hO : MmaOne L X) (hG : SyncGuarded L kernel X) {w : EvId}
    (hE : MmaElemAt X w)
    (hS : ∀ s e, X.get s = some e → Relation.TransGen (TcMma.TcStep L X) s w →
      ∀ cell old, TcMma.StoreValue L X s cell old → ∃ r : ℝ, OkF old r)
    (ih : ∀ s e, X.get s = some e → Relation.TransGen (TcMma.TcStep L X) s w → RfClaim L X s) :
    RfClaim L X w := by
  intro cell old hd hr
  obtain ⟨-, -, -, -, -, -, -, x, y, prev, -, -, -, -, -, hv, -⟩ :=
    mma_result_sum hp hX hT hO hG hE (cell := cell) (v := old) (fun src old' hdep h => by
      rcases h with ⟨hds, hres⟩ | hst
      · obtain ⟨d, s, a, mk, pc, hsrc⟩ := hres.mmaIssue
        exact ih src _ hsrc hdep cell old' hds hres
      · obtain ⟨a, vals, sh, j, ⟨pc, hsrc⟩, -⟩ := id hst
        obtain ⟨r, -, hr'⟩ := hS src _ hsrc hdep cell old' hst
        exact ⟨r, hr'⟩) hd hr
  exact ⟨_, by rw [hv]; rfl⟩

/-- **A done MMA's result reads as a number**, given that the words stores write do. -/
theorem result_float (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) (hO : MmaOne L X) (hG : SyncGuarded L kernel X) (hE : MmaElements X)
    (hS : ∀ w e, X.get w = some e → ∀ cell old, TcMma.StoreValue L X w cell old →
      ∃ r : ℝ, OkF old r)
    {w : EvId} {e : Event} (he : X.get w = some e) {cell : TcMma.Cell} {old : Value}
    (hd : X.async.mmaDone w = true) (hr : TcMma.Result L Assumptions.all X w cell old) :
    ∃ r : ℝ, valFloat .f32 old = .ok r :=
  PTX.Frame.values_by_tcStep hX hG (RfClaim L X) (fun w _ _ ih => result_float_step hp hX hT hO hG
    (hE w) (fun s e hs _ => hS s e hs) ih) w e he cell old hd hr

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
