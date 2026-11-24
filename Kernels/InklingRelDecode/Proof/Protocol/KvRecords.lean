-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvSingle
public import Kernels.InklingRelDecode.Proof.Protocol.MbarReach
public import Kernels.InklingRelDecode.Proof.Protocol.SOHyp
public import Kernels.InklingRelDecode.Proof2.Lib.MbarInit
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvPreload
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-!
# No mbarrier record of the kernel faults

`Safety.Protocol.recordsOk`: no record of any mbarrier object faults. The kernel's mbarriers are
twelve per CTA (`EvD.Bar.loc`), and an object that has a record is one of them
(`uses_of_record` and the placement of `Safety.MbarPlaced`, taken here in its elementary form
`Placed`). Per CTA:

* the six barriers of the KV ring, `kv_ready s` and `kv_empty s`, three slots, are the two
  barriers of a `Kv.Slot` under `Kv.Hyp` (`Ring.Kv.fault_free`: the loader's arrivals and copies
  and the prologue's three `expect_tx` arrivals are `kv_ready` records, the MMA lane's commits
  are `kv_empty` records);
* the six barriers of the S/P/O handshake, `s_ready b`, `p_ready b`, `o_done`, `o_final`, under
  `Mbar.Ctx` (`Mbar.s_faultFree`, `p_faultFree`, `o_faultFree`, `f_faultFree`).

`CtaRecords` is the list of what is assumed for one CTA: the two structures, each a statement
about the events of the roles' machines and the initializations (the development notes, "Protocol
`Mbar`" and "Protocol `Kv`"). `recordsOk_of_ctas` is `Safety.Protocol.recordsOk`'s statement.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mbar
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty)

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A record of an object is of an event that names the object.** -/
theorem uses_of_record (hX : Consistent L K A mem0 X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) : ∃ e, X.UsesMbar e m := by
  cases record_source hX.tma.2.2.1 hr with
  | init hid he ha => exact ⟨_, Execution.UsesMbar.of_init ⟨_, he⟩⟩
  | inval hid he ha => exact ⟨_, Execution.UsesMbar.of_inval ⟨_, he⟩⟩
  | arrive hid he ha => exact ⟨_, .inl ⟨_, _, _, _, _, he⟩⟩
  | wait hid he ha => exact ⟨_, .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩))))⟩
  | increment hid he ha => exact ⟨_, .inr (.inr (.inl ⟨_, _, he⟩))⟩
  | @tensor i pc a sp hid he hm ha =>
    subst hm
    exact ⟨i, Execution.UsesMbar.of_tensor ⟨_, he⟩⟩
  | @arriveOn i pc m' noinc hid he hm hn ha =>
    subst hm
    exact ⟨i, .inr (.inr (.inl ⟨_, _, he⟩))⟩
  | bulk hid he hc hn ha => exact ⟨_, .inr (.inl ⟨_, ⟨_, he⟩, hc⟩)⟩
  | commit hid he ht ha => exact ⟨_, .inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, ht⟩)))⟩
  | @clc i pc sp tg c hid he hm htg ha =>
    subst hm
    exact ⟨i, Execution.UsesMbar.of_clc ⟨_, he⟩ htg⟩

/-- **Mbarrier placement** (`Safety.MbarPlaced`): every mbarrier an instruction names is one of
the kernel's twelve, of a launched CTA. -/
def Placed (L : Launch) (X : Execution) : Prop :=
  ∀ e m, X.UsesMbar e m → ∃ (b : EvD.Bar) (cta : Nat), cta < L.grid ∧ m = b.loc L cta

/-- **What is assumed of one CTA's twelve barriers.** -/
structure CtaRecords (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) (cta : Nat) : Prop where
  /-- The KV ring: slot `s` is a `Kv.Slot` of the CTA's two barriers under `Kv.Hyp`. -/
  kv : ∀ s : Fin 3, ∃ S : Ring.Kv.Slot, S.full = kvReady L cta s ∧ S.empty = kvEmpty L cta s ∧
    Ring.Kv.Hyp L K A X S
  /-- The S/P/O handshake of the CTA (`Ctx`), and that the MMA lane's first commit to `o_final`
  has no earlier one. -/
  so : ∃ cm p0 Soft Mma, Ctx L K A mem0 X cta cm p0 Soft Mma ∧
    ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L cta →
        ((X.tr cm).take i).countP (commitsTo (oFinal L cta)) = 0

/-- **No record of the twelve barriers of a CTA faults.** -/
theorem CtaRecords.faultFree {cta : Nat} (H : CtaRecords L K A mem0 X cta)
    (hX : Consistent L K A mem0 X) (b : EvD.Bar) :
    ∀ r ∈ X.objects (b.loc L cta), r.fault = none := by
  cases b with
  | kvReady s =>
    obtain ⟨S, hf, he, HK⟩ := H.kv s
    intro r hr
    refine Ring.Kv.fault_free hX HK (m := S.full) (.inl rfl) ?_
    rw [hf]
    exact hr
  | kvEmpty s =>
    obtain ⟨S, hf, he, HK⟩ := H.kv s
    intro r hr
    refine Ring.Kv.fault_free hX HK (m := S.empty) (.inr rfl) ?_
    rw [he]
    exact hr
  | sReady b =>
    obtain ⟨cm, p0, Soft, Mma, C, -⟩ := H.so
    exact s_faultFree C b.isLt
  | pReady b =>
    obtain ⟨cm, p0, Soft, Mma, C, -⟩ := H.so
    exact p_faultFree C b.isLt
  | oDone =>
    obtain ⟨cm, p0, Soft, Mma, C, -⟩ := H.so
    exact o_faultFree C
  | oFinal =>
    obtain ⟨cm, p0, Soft, Mma, C, hone⟩ := H.so
    exact f_faultFree hX C.facts hone

/-- **`Safety.Protocol.recordsOk`**: no mbarrier record faults. -/
theorem recordsOk_of_ctas (hX : Consistent L K A mem0 X) (hplaced : Placed L X)
    (H : ∀ cta < L.grid, CtaRecords L K A mem0 X cta) :
    ¬ ∃ m r, r ∈ X.objects m ∧ r.fault.isSome := by
  rintro ⟨m, r, hr, hf⟩
  obtain ⟨e, he⟩ := uses_of_record hX hr
  obtain ⟨b, cta, hc, rfl⟩ := hplaced e m he
  rw [(H cta hc).faultFree hX b r hr] at hf
  exact absurd hf (by simp)

end
end PTX.Kernels.InklingRelDecode.Proof.Mbar
