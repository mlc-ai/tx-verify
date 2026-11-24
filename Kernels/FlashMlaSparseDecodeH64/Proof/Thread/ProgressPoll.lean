-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Lemmas.Snoc.ObjectAppend

@[expose] public section

/-! # Successful polls along the dequantization path -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof MBarrier

noncomputable section

/-- Appending the checked object record of a non-NC event preserves the kernel assumptions. -/
theorem all_wf_snoc_object_of_not_nc {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {ev : Event} {m : Loc} {rec : Record AsyncCopy.Ref}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hnc : ∀ acc bytes, ev.kind ≠ .nc acc bytes)
    (hnew : ev.kind = .exit → ∀ i, i.1 = g →
      TensorStore.Selected Assumptions.storeDrain.storeReadsBeforeExit X i →
      X.AsyncPresent i .readsDone) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.snocObject g ev (fun _ => none) m rec) := by
  intro a ha
  let Z := X.snoc g ev (fun _ => none)
  have hZ := Interface.all_wf_snoc_of_not_nc (g := g) (event := ev) (rf := fun _ => none)
    hX hnc hnew
  have hbase := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hbase
    | exact hZ Assumptions.commitOrder (by simp [Assumptions.all])
    | (change TensorStore.ReadsDrainedBeforeExit _ (Z.appendObject m rec)
       exact TensorStore.ReadsDrainedBeforeExit.of_trace
         (hZ Assumptions.storeDrain (by simp [Assumptions.all]))
         rfl (fun _ => Execution.readsDone_mono (Z.le_appendObject m rec)))
    | simpa only [Execution.snocObject, Assumptions.ncReadOnly, Assumption.ncReadOnly,
        Execution.initialByte, Execution.appendObject, Execution.get] using
        hZ Assumptions.ncReadOnly (by simp [Assumptions.all])

/-- An acquire poll of a ready object extends the trace and records the observation. -/
theorem poll_extension {L : Launch} {mem0 : Mem0} {X : Execution} {g q : Nat}
    {t u : TState} {m : Loc} {k : Bool → TState} {scope : MbarScope} {before : State}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hrel : PTX.Step.Released L X g)
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hτ : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u)
    (hout : out kernel Assumptions.all L g u = .ev (.wait m q k true scope))
    (hstate : stateBefore (X.objects m) (X.objects m).length = some before)
    (hready : before.phase % 2 ≠ q % 2) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  apply PTX.Step.poll_counted_extension hX hg hne hrel _ hrun hτ
    ⟨_, hout, true, rfl, rfl⟩ hstate hready
  intro a ha rec _
  exact all_wf_snoc_object_of_not_nc hX (by simp) (by simp) a ha

/-- The three polls before dequantizer scale and raw reads. -/
inductive DequantWait where
  | query
  | raw
  | pv

def DequantWait.site : DequantWait → Wg2.Site
  | .query => .qUtccp
  | .raw => .rawReady
  | .pv => .svDone

def DequantWait.object (L : Launch) (g : Nat) (d : Wg2.D) (w : DequantWait) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + match w with
    | .query => Wg2.qUtccpOff
    | .raw => Wg2.rawReadyOff d.buf
    | .pv => Wg2.svDoneOff d.buf⟩

def DequantWait.parity (d : Wg2.D) : DequantWait → Nat
  | .query | .raw => d.par
  | .pv => 1 - d.par

/-- The loaded address and parity determine the CTA-scoped poll's actual template. -/
theorem poll_regs_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {p bas pr off q : Nat} (hpre : Pre P L mem0)
    (hb : t.regs bas = some (sb L off)) (hp : t.regs pr = some (b32 q))
    (hlt : off ≤ 222944) (ha : off % 8 = 0) (hq : q < 2) :
    ∃ k, eventTmpl Assumptions.all L g t (.mbarWait p bas 0 (.reg pr) true .cta) =
      .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ q k true .cta := by
  have hm : mbarLoc L g t bas 0 = .ok ⟨.shared, g / L.block, L.sharedBase + off⟩ := by
    apply mbarLoc_b32 hb _ (Wg2.sharedAddr_align hpre ha)
    have := sharedBase_lt hpre
    omega
  have hpar : readBits L g t 32 (.reg pr) = .ok (BitVec.ofNat 64 q) :=
    readBits_b32 hp (by omega)
  have hn : (BitVec.ofNat 64 q).toNat % 2 = q := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : q < 2 ^ 64), Nat.mod_eq_of_lt hq]
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  refine ⟨fun ok => PTX.next (setReg t p (.pred ok)), ?_⟩
  simp only [eventTmpl, tmaTmpl, hm, hpar, bind, Except.bind, pure, Except.pure, ofExec,
    widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte, hn]

private theorem dequant_wait_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg2.D} {w : DequantWait} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = w.site) (ha : Wg2.AtD P L g d t) (hi : Wg2.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g t ins.op =
      .wait (w.object L g d) (w.parity d) k true .cta := by
  cases w with
  | query =>
    have hpc : d.site.pc = 2644 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
    exact poll_regs_template (off := Wg2.qUtccpOff) hpre
      (Wg2.AtD.regAt ha hpc (by decide +kernel))
      (Wg2.AtD.regAt ha hpc (by decide +kernel)) (by decide) (by decide) hi.parLt
  | raw =>
    have hpc : d.site.pc = 2677 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_14)
    exact poll_regs_template (off := Wg2.rawReadyOff d.buf) hpre
      (Wg2.AtD.regAt ha hpc (by decide +kernel))
      (Wg2.AtD.regAt ha hpc (by decide +kernel))
      (by have := hi.bufLt; unfold Wg2.rawReadyOff; omega)
      (by unfold Wg2.rawReadyOff; omega) hi.parLt
  | pv =>
    have hpc : d.site.pc = 2684 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15)
    exact poll_regs_template (off := Wg2.svDoneOff d.buf) (q := 1 - d.par) hpre
      (Wg2.AtD.regAt ha hpc (by decide +kernel))
      (Wg2.AtD.regAt ha hpc (by decide +kernel))
      (by have := hi.bufLt; unfold Wg2.svDoneOff; omega)
      (by unfold Wg2.svDoneOff; omega) (by omega)

/-- A released dequantizer at a ready query, raw or PV poll can take its success branch. -/
theorem dequant_poll_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} {w : DequantWait} {before : State} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d)))
    (hd : d.site = w.site)
    (hstate : stateBefore (X.objects (w.object L g d)) (X.objects (w.object L g d)).length =
      some before)
    (hready : before.phase % 2 ≠ (w.parity d) % 2) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  obtain ⟨k, htmpl⟩ := dequant_wait_template hpre hd ha hi hc
  rw [htmpl] at hout
  exact poll_extension hX hp.1 hne hrel hr hτ hout hstate hready

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
