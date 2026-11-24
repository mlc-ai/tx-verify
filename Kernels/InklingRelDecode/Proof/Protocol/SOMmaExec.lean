-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaRun

@[expose] public section

/-!
# The MMA warp's handshake events on an execution

The run theorems of `SOMmaRun` read on an execution `X`: the worker thread `g` is followed by
`WComp.code L g Q`, `wAt Q L X g k` is its abstract state before its `k`-th event, and its events
are a run of the machine (`Ring.trace_of`). A statement is relative to an anchor event `k₀` at
which the thread is at the state `d₀` that starts the loop and a later event `k` at the state `d`
(`hin`: the states between are the MMA role's, with `Mma.Inv`).

* `mma_pwait_exec`: a successful poll of `p_ready b` at event `k` is at the `pWait` site of an
  iteration `i` with `i - 1 = blockB b n`, `n` the thread's earlier successful polls of that
  barrier, and its parity is `fullParity (i - 1)`, which is `n % 2` (the parity field of the
  barrier's thread-layer facts, as `Ring.mma_poll_exec` for `kv_ready`).
* `mma_qkcommit_exec`: a commit to `s_ready b` at event `k` is at the `qkCommit` site of iteration
  `i`, with `i = blockB b n`, `n` the thread's earlier commits to the barrier; the elected lane's
  `n`-th commit to `s_ready b` is the QK commit of block `2 n + b`.
* `mma_ocommit_exec`: a commit to `o_done` at `k` is at the `pvCommit2` site of iteration `i` and
  `i - 1` is the number of the thread's earlier commits to it: the `n`-th commit is for block `n`.
* `mma_fcommit_exec`: a commit to `o_final` at `k` is at the `finCommit` site and is the thread's
  first commit to it.

`ElectLead` (every election of the thread returned its lane) is the premise of the three commit
statements, as for the PV commit to `kv_empty` (`Ring.mma_commit_exec`); the polls are of every
lane and take no such premise. `hin` and the fresh counts are the role-table protocol of
`Ring.lean`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW LeadRun MmRun wAt trace_of run_from run_states
  fired_some not_ends_take countP_take_split)
open PTX.Kernels.InklingRelDecode.Proof.EvW (MmShape mma_shape sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}
  {X : Execution}

/-! ### On a run -/

section
variable (hpre : Pre Q L mem0) (hg : g < L.threads) {P : Loader.Pro} {d0 : Mma.D} {es : List Event}
    (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es) (hE : ∀ e ∈ es, MmRun L g e)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc) {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P)))
include hpre hg hT hE hin hd

/-- **The QK commit, with its place in the double buffer.** At the `qkCommit` site, in a run
from the start of the loop with no earlier QK commit (`qkDone d₀ = 0`) whose elections returned the
thread's lane, the event is the commit to `s_ready (i % 2)` and block `i` is the `n`-th one of its
buffer, `n` the commits to that barrier made before. -/
theorem mma_qkcommit (h0 : Mm.qkDone d0 = 0) (hw : d.site = .qkCommit)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) :
    e = ⟨Mma.Site.qkCommit.pc, .tc (.commit (EvW.commitSpec (g / L.block)
        (sReady L (g / L.block) (d.i % 2))))⟩ ∧
      d.i = blockB (d.i % 2)
        (es.countP (commitsTo (sReady L (g / L.block) (d.i % 2)))) := by
  have hsh := mma_shape hpre hg hF
  have hcount := mma_sCommits hpre hg hT hE hin hd (b := d.i % 2) (by omega)
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only at hw
  subst hw
  simp only [MmShape] at hsh
  have hpd : Mm.qkDone ⟨.qkCommit, i, n, tm, pro⟩ = i := by simp [Mm.qkDone]
  rw [hpd, h0, below2_zero, below2_of_buf (by omega) rfl] at hcount
  refine ⟨hsh, ?_⟩
  unfold blockB
  omega

/-- **The second PV commit.** At `pvCommit2`, in a run from the start of the loop with no earlier
one (`oDoneC d₀ = 0`) whose elections returned the thread's lane, the event is the commit to
`o_done`, and block `i - 1` of the PV half is the number of commits to it made before. -/
theorem mma_ocommit (h0 : Mm.oDoneC d0 = 0) (hw : d.site = .pvCommit2)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) :
    e = ⟨Mma.Site.pvCommit2.pc, .tc (.commit (EvW.commitSpec (g / L.block)
        (oDone L (g / L.block))))⟩ ∧
      d.i - 1 = es.countP (commitsTo (oDone L (g / L.block))) := by
  have hsh := mma_shape hpre hg hF
  have hcount := mma_oCommits hpre hg hT hE hin hd
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only at hw
  subst hw
  simp only [MmShape] at hsh
  have hpd : Mm.oDoneC ⟨.pvCommit2, i, n, tm, pro⟩ = i - 1 := by simp [Mm.oDoneC]
  rw [hpd, h0] at hcount
  refine ⟨hsh, ?_⟩
  dsimp only
  omega

end

/-! ### On an execution -/

variable (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k) {d0 d : Mma.D}
    {P : Loader.Pro} (h0 : wAt Q L X g k0 = some (some (.mma d0 P)))
    (hd : wAt Q L X g k = some (some (.mma d P)))
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc)
include hpre hw hg hX hk h0 hd hin

/-- The data of an anchored MMA run on an execution: the events from `k₀` to `k` are a run from
`d₀` to `d`, keeping the role's invariant. -/
theorem mma_exec_run :
    (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) (((X.tr g).drop k0).take (k - k0)) ∧
      (WComp.code L g Q).toMachine.after (some (.mma d0 P))
        (((X.tr g).drop k0).take (k - k0)) = some (some (.mma d P)) ∧
      ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
        (WComp.code L g Q).toMachine.after (some (.mma d0 P))
          ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.mma d' P)) ∧
        Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc := by
  have hrun := run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := run_states hk h0 hd
  refine ⟨hrun, hend, ?_⟩
  intro j hj
  have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
  obtain ⟨d', h1, h2, h3⟩ := hin (k0 + j) (by omega) (by omega)
  exact ⟨d', (hmid j hj').trans h1, h2, h3⟩

omit hpre hw hg hX hk h0 hd hin in
/-- The events of the anchored run are events before `k`, none of which ends the thread, and
each election returned the thread's lane when the thread's elections before `k` did. -/
theorem mma_exec_lead (hg : g < L.threads) (hX : Consistent L kernel WComp.asms mem0 X)
    {k0 k : Nat} (hk : k0 ≤ k) (hklt : k < (X.tr g).length)
    (hlead : ElectLead L g ((X.tr g).take k)) (hbc : Mma.BcastRun ((X.tr g).take k)) :
    ∀ e ∈ ((X.tr g).drop k0).take (k - k0), MmRun L g e := by
  have hsub : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), e ∈ (X.tr g).take k := by
    intro e he'
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [List.take_add]
    rw [Nat.add_sub_cancel_left] at he'
    exact List.mem_append_right _ he'
  exact fun e he' => ⟨⟨not_ends_take hg hX hklt e (hsub e he'), hlead e (hsub e he')⟩,
    hbc e (hsub e he')⟩

/-- **The QK commit to `s_ready b`, on an execution.** -/
theorem mma_qkcommit_exec (h0p : Mm.qkDone d0 = 0) {b : Nat} (hb : b < 2)
    (hlead : ElectLead L g ((X.tr g).take k)) (hbc : Mma.BcastRun ((X.tr g).take k))
    (hfresh : ((X.tr g).take k0).countP (commitsTo (sReady L (g / L.block) b)) = 0) {pc : Nat}
    {sp : TcCommit.Spec} (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hsp : sp.mbar = sReady L (g / L.block) b) :
    d.site = .qkCommit ∧ d.i % 2 = b ∧
      d.i = blockB b (((X.tr g).take k).countP (commitsTo (sReady L (g / L.block) b))) := by
  have hT := trace_of hpre hw hg hX
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : ¬ Ends (⟨pc, .tc (.commit sp)⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hcm := mm_commitsTo_s hpre hg hF hb
  rw [commitsTo_of_kind (sp := sp) rfl] at hcm
  simp only [hsp, decide_true] at hcm
  have hsite : d.site = .qkCommit ∧ d.i % 2 = b := by
    have := hcm.symm
    simp only [decide_eq_true_eq] at this
    exact this
  obtain ⟨hsw, hs2⟩ := hsite
  obtain ⟨hrun, hend, hin'⟩ := mma_exec_run hpre hw hg hX hk h0 hd hin
  obtain ⟨-, hblk⟩ := mma_qkcommit hpre hg hrun (mma_exec_lead hg hX hk hklt hlead hbc)
    hin' hend h0p
    hsw hF
  have hsplit := countP_take_split (commitsTo (sReady L (g / L.block) b)) (X.tr g) hk
  rw [hs2] at hblk
  refine ⟨hsw, hs2, ?_⟩
  rw [hsplit, hfresh, Nat.zero_add]
  exact hblk

/-- **The second PV commit, to `o_done`, on an execution.** -/
theorem mma_ocommit_exec (h0p : Mm.oDoneC d0 = 0) (hlead : ElectLead L g ((X.tr g).take k))
    (hbc : Mma.BcastRun ((X.tr g).take k))
    (hfresh : ((X.tr g).take k0).countP (commitsTo (oDone L (g / L.block))) = 0) {pc : Nat}
    {sp : TcCommit.Spec} (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hsp : sp.mbar = oDone L (g / L.block)) :
    d.site = .pvCommit2 ∧
      d.i - 1 = ((X.tr g).take k).countP (commitsTo (oDone L (g / L.block))) := by
  have hT := trace_of hpre hw hg hX
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : ¬ Ends (⟨pc, .tc (.commit sp)⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hcm := mm_commitsTo_o hpre hg hF
  rw [commitsTo_of_kind (sp := sp) rfl] at hcm
  simp only [hsp, decide_true] at hcm
  have hsw : d.site = .pvCommit2 := by simpa using hcm.symm
  obtain ⟨hrun, hend, hin'⟩ := mma_exec_run hpre hw hg hX hk h0 hd hin
  obtain ⟨-, hblk⟩ := mma_ocommit hpre hg hrun (mma_exec_lead hg hX hk hklt hlead hbc)
    hin' hend h0p
    hsw hF
  have hsplit := countP_take_split (commitsTo (oDone L (g / L.block))) (X.tr g) hk
  refine ⟨hsw, ?_⟩
  rw [hsplit, hfresh, Nat.zero_add]
  exact hblk

end
end PTX.Kernels.InklingRelDecode.Proof.SO
