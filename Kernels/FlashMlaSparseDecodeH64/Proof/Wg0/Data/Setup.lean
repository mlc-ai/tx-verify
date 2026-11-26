-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup
public import Lemmas.Flow.BranchU
public import Tactics.KernelRfl

@[expose] public section

/-! # The data steps of the set-up's two value sources

* `ds_103`: after the `setmaxnreg` (pc 103) the control code loads the scale word with the
  `ld.param` at pc 146 (`seg_ldp`, under `Pre`) into `%r9`; no later set-up instruction writes it,
  so every set-up site holds it (`reach_103`).
* `ds_200`: after the last-store arrival (pc 200) a site on the chain is the loop's first head
  (`bar0`), so the no-block test (pc 207, `%p74`) is false; the moves at pcs 208–210 make the
  scale's pair `%rd254` (`scPair`) and those at pcs 247–249 the statistics' initial words
  (`reach_200`). -/

/-! # The loop's entry without a block

When the thread has no block (`%r15 < 64`, `%p74`, pc 201) the code initializes the statistics
and the zero-maximum predicate (`%p138 = true`, pc 204) and jumps from pc 207 to the epilogue's
masked moves (pc 1150). The facts at the epilogue's first barrier are those of
the first run on the initial statistics (`f_exit`): the maximum is `-inf`, so the predicate holds
and the masked sum and maximum are `0` and `-inf`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- After the last-store arrival (pc 200) without a block: the epilogue's first barrier. -/
theorem reach_200e (c : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 c.l0 c.l1) 64 = true) :
    Reach kernel Assumptions.all L g 201
      ((467, .bits 32 x) :: (2880, sk) :: Control.vF P L g w 200 c)
      (f_exit (lookupD (f_car x mI lI mxI sk))) := by
  refine SegU.reach_then (q := 207)
    (G := [(74, .pred true), (138, .pred true), (2950, mI), (2955, lI), (467, .bits 32 x),
      (2880, sk)]) ?_ ?_
  · have h : SegU kernel Assumptions.all L g 201
        ((467, .bits 32 x) :: (2880, sk) :: Control.vF P L g w 200 c) 207
        [(74, .pred (scmpi .lt .s (Control.r15 c.l0 c.l1) 64)), (138, .pred true),
          (2950, mI), (2955, lI), (467, .bits 32 x), (2880, sk)] := by
      dsimp only [Control.vF, mI, lI]; ctl_seg
    rwa [h74] at h
  refine SegU.reach_then (SegU.branch true Flow.code_207 bra_rule (w0SegFree 207)) ?_
  have hE : f_exit (lookupD (f_car x mI lI mxI sk)) =
      [(138, .pred true), (481, w32 4286578688), (1727, w32 0), (2880, sk)] := by
    kernel_rfl
  rw [hE]
  refine SegU.reach_then (q := 1154) (G := [(138, .pred true), (481, w32 4286578688),
    (1727, w32 0), (2880, sk)]) ?_ ?_
  · ctl_seg
  · exact reach_frameSet rulesFrame (S := []) (by kernel_rfl) (fun _ _ => w0SegFree _)
      (by kernel_rfl) fun _ h => h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m0 : Mem0}

/-- After the `setmaxnreg` (pc 103): the scale word from the `ld.param` at pc 146. -/
theorem reach_103 (hp : Pre P L m0) (c : Control.D) :
    Reach kernel Assumptions.all L g 104 (Control.vF P L g w 103 c) (f_set (scX L) mxI) :=
  SegU.reach_then (Control.stageSeg hp c)
    (SegU.reach_then (SegU.of_seg (seg_ldp (off := 28) (x := scaleBits L) (n := 4) hp
      Flow.code_146 (by decide) (by decide) (by decide) (by simp [p0fields])
      (mem_factsFrom_eq (by decide +kernel) rfl) (Control.fresh_live (by decide +kernel))))
    (reach_frameSet rulesFrame (S :=
        [147, 148, 149, 150, 151, 152, 153, 154, 155, 158, 159, 160,
        161, 162, 163, 164, 165, 166, 167, 170, 171, 172, 173, 174,
        175, 176, 177, 178, 179, 180, 183, 184, 185, 186, 187, 188,
        189, 190, 191, 192, 193, 194, 195, 196, 197, 1836, 1837,
        1838, 1839]) (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl)
      fun _ h => ⟨h.1, holds_mem h.2 (mem_factsFrom_eq (by decide +kernel) rfl), trivial⟩))

/-- After the last-store arrival (pc 200), on the way to the loop: the scale's pair and the
statistics' initial words. -/
theorem reach_200 (c : Control.D) (x : BitVec 64) (sk : Value)
    (h74 : scmpi .lt .s (Control.r15 c.l0 c.l1) 64 = false) :
    Reach kernel Assumptions.all L g 201
      ((467, .bits 32 x) :: (2880, sk) :: Control.vF P L g w 200 c) (f_car x mI lI mxI sk) := by
  refine SegU.reach_then (q := 207)
    (G := [(74, .pred false), (467, .bits 32 x), (2880, sk)]) ?_ ?_
  · have h : SegU kernel Assumptions.all L g 201
        ((467, .bits 32 x) :: (2880, sk) :: Control.vF P L g w 200 c) 207
        [(74, .pred (scmpi .lt .s (Control.r15 c.l0 c.l1) 64)), (467, .bits 32 x),
          (2880, sk)] := by
      dsimp only [Control.vF]; ctl_seg
    rwa [h74] at h
  · refine SegU.reach_then (SegU.branch false Flow.code_207 bra_rule (w0SegFree 207)) ?_
    refine SegU.reach_then (q := 256) (G := f_car x mI lI mxI sk)
      (by dsimp only [f_car, mI, lI, mxI]; ctl_seg) ?_
    exact reach_frameSet rulesFrame (S := []) (by kernel_rfl) (fun _ _ => w0SegFree _)
      (by kernel_rfl) fun _ h => h

/-- A one-element site's start state after its event, from the control facts. -/
theorem at_ctl {d : D} {s : Site} {t : TState} (hs : d.c.site = s)
    (hat : (code P L g w).AtD d t) (hi : (code P L g w).inv d) (he : Control.elems s = 1) :
    At (PTX.next t) (s.pc + 1) (Control.vF P L g w s.pc d.c ++ dF L d) := by
  obtain ⟨hpc, hsb, ha, hf, hF⟩ := hat
  have h0 := el0 hs hi he
  refine ⟨?_, hsb.trans h0, ha.trans (by simp [Control.D.acc, h0]), hf, ?_⟩
  · show t.pc + 1 = _; rw [hpc, pc_eq hs]
  · show Holds t.regs (factsFrom (Control.ctlLive s.pc) _ ++ _); rw [← hs]; exact hF

/-- **The `setmaxnreg`** (pc 103), the chain's first site. -/
theorem ds_103 (hp : Pre P L m0) : ∀ d : D, d.c.site = .smr →
    DataStep (code P L g w) (dF L) d := by
  intro d hs
  refine DataStep.next (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact Flow.code_103)
    (fun _ _ _ hf => Control.fires_smr_next hf) ?_
  intro hi e d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  have hrec : wF (scX L) .sink (record d.c e d.b) = f_set (scX L) mxI := by
    unfold record wF wcls wFc; rw [hs]
  refine fin_reach (s' := .sink) (by rw [hs]; nofun)
    (fun h => cls_mem (by unfold succOk at h; rw [hs] at h; exact h) (by decide))
    (fun _ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := at_ctl hs hat hi rfl
      exact ⟨h1, h2, h3, h4, ((holds_append _ _ _).mp h5).1⟩)
    (fun _ _ => by rw [hrec]; exact reach_103 hp d.c)

/-- **The last-store arrival** (pc 200): on the chain, the loop's first head, or the
epilogue's first barrier when the thread has no block. -/
theorem ds_200 : ∀ d : D, d.c.site = .arrL → DataStep (code P L g w) (dF L) d := by
  intro d hs
  refine DataStep.next (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact Flow.code_200)
    ?_ ?_
  · intro _ _ _ hf; exact Code.fires_arrive_next hf
  intro hi e d' t hn hat
  obtain ⟨c', hc', rfl⟩ := next_ctl hn
  have hdF : (isStart d.c.site || d.ok) = true → Holds t.regs (f_set (scX L) d.b.sk) := fun h1 => by
    obtain ⟨-, -, -, -, hF⟩ := id hat
    have hd := ((holds_append _ _ _).mp hF).2
    have hok : d.ok = true := by rw [hs] at h1; simpa [isStart] using h1
    unfold dF at hd; rw [hok, hs] at hd; exact hd
  have hu : (isStart d.c.site || d.ok) = true → At (PTX.next t) (Site.arrL.pc + 1)
      ((467, .bits 32 (scX L)) :: (2880, d.b.sk) :: Control.vF P L g w 200 d.c) := fun h1 => by
    obtain ⟨h1', h2, h3, h4, h5⟩ := at_ctl hs hat hi rfl
    exact ⟨h1', h2, h3, h4, (hdF h1).1, (hdF h1).2.1, ((holds_append _ _ _).mp h5).1⟩
  have hc : c' = Control.loopEntry d.c := by
    simp only [Control.succ, hs, Option.some.injEq] at hc'; exact hc'.symm
  have hrec : record d.c e d.b = { d.b with m := mI, l := lI, mx := mxI } := by
    unfold record; rw [hs]
  cases h74 : scmpi .lt .s (Control.r15 d.c.l0 d.c.l1) 64
  · refine fin_reach (s' := .bar0) (by rw [hs]; nofun)
      (fun _ => congrArg wcls (by rw [hc]; simp [Control.loopEntry, h74])) hu (fun _ _ => ?_)
    rw [hrec]
    exact reach_200 d.c (scX L) d.b.sk h74
  · refine fin_reach (s' := .ebar0) (by rw [hs]; nofun)
      (fun _ => congrArg wcls (by rw [hc]; simp [Control.loopEntry, h74])) hu (fun _ _ => ?_)
    rw [hrec]
    exact reach_200e d.c (scX L) d.b.sk h74

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
