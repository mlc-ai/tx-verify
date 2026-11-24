-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Def
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Stores
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The correction lanes' stores are numbers

`StatReads`: a statistics read of a correction lane returns the payload its data machine follows,
once the Tensor Memory loads of its CTA before it returned numbers (the statistics hand-off and the
softmax lanes' statistics stores). With it the correction lanes' stores are numbers (`corrStores`),
and their data reads are those the machine follows once every load returned numbers
(`dataTo_of`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Site StatTo LoadTo)

noncomputable section

/-- **The statistics reads** of the correction lanes return what their data machines follow, once
the loads before did. -/
def StatReads (L : Launch) (X : Execution) : Prop :=
  ∀ {h i : Nat} (s : Site) {e : Event}, h < L.threads → 8 ≤ Prologue.warpIndex L h →
    Prologue.warpIndex L h < 12 → X.get (h, i) = some e → e.pc = s.pc → s.stat = true →
    LoadsBefore L X (h, i) → CorrWarp.ReadPayload s e.kind

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The earlier event `(h, i)` of a lane precedes its event `(h, k)`, unless both are ordinary
accesses: a `tcgen05` event at `k`. -/
theorem tcStep_tc {h i k pc : Nat} {tk : TcKind} (hik : i < k)
    (hk : X.get (h, k) = some ⟨pc, .tc tk⟩) : TcStep L X (h, i) (h, k) := by
  have hlen : k < (X.tr h).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr h)[k]? = _ from hk)).1
  exact .inl (.single (.inl (po_of_not_access (e := (h, i)) (f := (h, k)) rfl hik hlen
    (by simp [hk, Event.acc]))))

/-- The reads of a correction lane before a `tcgen05` event. -/
theorem before_tc (hS : StatReads L X) {h k pc : Nat} {tk : TcKind} (hh : h < L.threads)
    (h8 : 8 ≤ Prologue.warpIndex L h) (h12 : Prologue.warpIndex L h < 12)
    (hk : X.get (h, k) = some ⟨pc, .tc tk⟩) (hL : LoadsBefore L X (h, k)) :
    StatTo X h k ∧ LoadTo X h k := by
  refine ⟨fun i hi s e he hpc hs => hS s hh h8 h12 he hpc hs fun f a vals hl hc hf =>
    hL f a vals hl hc (.tail hf (tcStep_tc hi hk)), fun i hi a vals hl => ?_⟩
  exact hL (h, i) a vals hl rfl (.single (tcStep_tc hi hk))

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The correction lanes' stores are numbers.** -/
theorem corrStores (hS : StatReads L X) : CorrStores L X := by
  intro h i a vals hh h8 h12 ht hL
  obtain ⟨pc, he⟩ := ht
  obtain ⟨h1, h2⟩ := before_tc hS hh h8 h12 he hL
  exact Correction.corr_st_f32 hp hX hFw h8 (by omega) h1 h2 ⟨pc, he⟩

/-- **The data reads of a correction lane**, once every load of the trace returned numbers. -/
theorem dataTo_of (hS : StatReads L X)
    (hL : ∀ {e : EvId} {a : Nat} {vals : List Value}, X.TLd e a vals .s32x32b → F32s vals)
    {h : Nat} (hh : h < L.threads) (h8 : 8 ≤ Prologue.warpIndex L h)
    (h12 : Prologue.warpIndex L h < 12) (K : Nat) : CorrWarp.DataTo p L X h K :=
  Correction.data_to hp hX hFw h8 (by omega)
    (fun _ _ s _ he hpc hs => hS s hh h8 h12 he hpc hs fun _ _ _ hl _ _ => hL hl)
    fun _ _ _ _ hl => hL hl

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
