-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOHandoff
public import Kernels.InklingRelDecode.Proof.Protocol.SOParity
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmOdone

@[expose] public section

/-!
# The `o_done` phase by the parity alternation (obligation 5)

The fixed kernel polls `o_done` in every iteration `i ≥ 1` (`SOSmOdone`): a softmax thread's
successful polls of it are one per iteration from the second, with the parity `(i + 1) % 2` of
the poll of iteration `i`, which is that of the thread's earlier successful polls, `i - 1` of them.
So `o_done` is polled like `s_ready` and `o_final`: its polls alternate, and the generic commit
object (`MbarRing.Notify.Obj`, `commitObj` of `SOHyp`) applies with offset 0. No commit-order
assumption is used: the phase bound is not obtained from the order in which the MMA lane's
commits notify, but from the alternation (each phase of the barrier holds one notification and the
thread's `j`-th poll observes phase `j`).

* `sm_owait_count`: on an execution, a softmax thread's successful poll of `o_done` is at the site
  `waitO` of an iteration `i ≥ 1`, its parity is `oDoneParity i`, and the thread has `i - 1`
  earlier successful polls of it, so the parity is the one of the earlier polls
  (`Facts`-level `parity` field).
* `o_parity_of_runs`: the parity field for the barrier, from the roles' runs, in the form of
  `SOParity.s_parity_of_runs`.
* `oObj`: `o_done` is a commit object of the MMA lane.
* `o_observes`: the poll of iteration `i` observes the notification of the `o_done` commit with
  `i - 1` earlier commits, which is the PV commit of block `i - 1` (`mma_ocommit_exec`), given the
  reuse premise `Notify.Reach` of the barrier (the commit of use `t` follows the thread's polls
  for the uses before `t`, the premise `s_observes` takes for `s_ready`).
* `o_doneBefore`: every MMA of the MMA lane issued before that commit (the PV MMAs of the blocks
  up to `i - 1`, with the QK MMAs before them) is done before every later event of the polling
  thread, in particular its `tcgen05.ld` of `O` and the rescale store. The rescale store is before
  the next PV MMA by `p_store_before_read`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow AsyncCopy TcMma
open PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (countP_take_split)
open PTX.Kernels.InklingRelDecode.Proof.EvW (oDone)

noncomputable section
set_option maxRecDepth 100000

/-! ### The thread's polls on an execution -/

/-! ### The object and its observations -/

variable {L : Launch} {X : Execution} {c cm p0 : Nat} {K : Kernel} {A : List Assumption}
  {mem0 : Mem0}

theorem CommitBar.oDone : CommitBar L c (oDone L c) := .inr (.inl rfl)

variable (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0)
    (hpar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait (oDone L c) p true acq sc⟩ →
        p % 2 = (okPolls (oDone L c) ((X.tr g).take k) + 0) % 2)
include hX F hpar

/-- **`o_done` is a commit object of `cm`**, with the thread's polls alternating (offset 0). -/
theorem oObj :
    MbarRing.Notify.Obj X (oDone L c) cm (oDone L c) 0 :=
  commitObj hX F CommitBar.oDone hpar

/-- **The poll of `o_done` with `u` earlier successful polls observes the notification of the
commit with `u` earlier `o_done` commits**, given the reuse premise of the polling thread
(`Notify.Reach`: the commit of use `t` follows the thread's polls for the uses before `t`). The
poll of iteration `i` has `i - 1` earlier polls (`sm_owait_count`), so it observes the commit with
`i - 1` earlier commits, the PV commit of block `i - 1` (`mma_ocommit_exec`). -/
theorem o_observes {h j pc p u : Nat} {acq : Bool} {sc : MbarScope}
    (hR : MbarRing.Notify.Reach L K A X (oDone L c) cm (oDone L c) 0 h)
    (he : X.get (h, j) = some ⟨pc, .wait (oDone L c) p true acq sc⟩)
    (hq : okPolls (oDone L c) ((X.tr h).take j) = u) :
    ∃ i pc' sp rank, X.get (cm, i) = some ⟨pc', .tc (.commit sp)⟩ ∧ sp.mbar = oDone L c ∧
      TcCommit.target sp rank = some (oDone L c) ∧
      ((X.tr cm).take i).countP (commitsTo (oDone L c)) = u ∧
      rank ∈ X.tcNotified (cm, i) ∧
      WaitObserves X (.async (cm, i) (.tcNotify rank)) (h, j) (oDone L c) acq sc :=
  (oObj hX F hpar).observes hX hR he (by omega)

/-- **PV accumulate before the O rescale** (obligation 5). Every MMA `x` of the MMA lane issued
before the commit the poll observes (at most `u` earlier `o_done` commits: the PV MMAs of the
blocks up to `u`, and the QK MMAs before them) is done before every later event `f` of the polling
thread: the commit tracks all earlier MMAs of its thread, and the poll (an acquire at CTA scope of
a thread of the CTA) observes it. With `u = i - 1` for the poll of iteration `i`
(`sm_owait_count`), the PV MMAs of block `i - 1` are done before the `tcgen05.ld` of the `O` tile
of iteration `i` and the rescale store. -/
theorem o_doneBefore (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    {h j pc p u f : Nat} {sc : MbarScope} (hcta : SameCta L cm h)
    (hR : MbarRing.Notify.Reach L K A X (oDone L c) cm (oDone L c) 0 h)
    (he : X.get (h, j) = some ⟨pc, .wait (oDone L c) p true true sc⟩)
    (hq : okPolls (oDone L c) ((X.tr h).take j) = u) {x : EvId} (hx : IsMma X x)
    (hxc : x.1 / L.block = c) (hu : ((X.tr cm).take x.2).countP (commitsTo (oDone L c)) ≤ u)
    (hjf : j < f) (hf : f < (X.tr h).length) : DoneBefore L X x (h, f) := by
  obtain ⟨i, pcx, sp, rank, hget, hmbar, htgt, hcnt, hrank, hobs⟩ :=
    o_observes hX F hpar hR he hq
  have hthr : x.1 = cm := hone hx hxc
  have hlt : x.2 < i := by
    obtain ⟨_, _, _, _, _, hxp⟩ := hx.get
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := countP_take_succ (p := commitsTo (oDone L c)) hget
        (by simp [commitsTo, hmbar])
      have h2 := countP_take_mono (commitsTo (oDone L c)) (X.tr cm)
        (show i + 1 ≤ x.2 by omega)
      omega
    · have hxi : (cm, i) = x := Prod.ext hthr.symm heq
      rw [← hxi] at hxp
      rw [hxp] at hget
      cases hget
  refine .inl ⟨(h, j), sc, ⟨.async (cm, i) (.tcNotify rank), oDone L c,
    ⟨(cm, i), sp, rank, rfl, ⟨hthr.symm ▸ rfl, hlt, .inl hx, sp, pcx, hget⟩, ⟨pcx, hget⟩, htgt,
      hrank⟩, hobs⟩, ?_, baseCausality_src he rfl rfl hjf hf⟩
  rw [hthr]
  exact MbarRing.Unit.Gate.scopesMeet hcta _ _

end
end PTX.Kernels.InklingRelDecode.Proof.SO
