-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.RefT
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Time
public import Lemmas.Tmem.PairProtocol
public import Lemmas.Kernel.FullVote

@[expose] public section

/-! # The startup's warp-collective `tcgen05` events

The startup's collective events are its paired Tensor Memory operations (warp 0's allocation and
relinquishment), so the ledger's count of those (`RefT`) counts its collectives (`ev_tc`); they
are fired at the allocation and relinquishment sites (`ev_tmem`, times 92 and 98), and a state
with fewer of them is no later (`time_refT`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Flow.Arith32

/-- **A startup event is collective exactly when it is a paired Tensor Memory operation**, and
it is no vote. -/
theorem ev_tc {L : Launch} {g : Nat} {d : D} {e : Event} (hx : ∀ r, d.site ≠ .enter r)
    (hev : Ev L g d e) :
    isTcColl e = Tmem.Pair.isTmemOp e ∧ Flow.voteWith (2 ^ 32 - 1) e = false := by
  obtain ⟨site, x1, x2⟩ := d
  obtain ⟨pc, kd⟩ := e
  cases site
  case enter r => exact absurd rfl (hx r)
  case sh j =>
    fin_cases j <;> obtain ⟨_, _, h⟩ := hev <;> simp only at h <;> subst h <;> exact ⟨rfl, rfl⟩
  case elect j => obtain ⟨_, _, -, h⟩ := hev; simp only at h; subst h; exact ⟨rfl, rfl⟩
  case ld =>
    rcases hev with ⟨_, _, h, -⟩ | ⟨f, h⟩ <;> simp only at h <;> subst h <;> exact ⟨rfl, rfl⟩
  case allocSt => obtain ⟨_, -, h⟩ := hev; simp only at h; subst h; exact ⟨rfl, rfl⟩
  all_goals simp only [Ev] at hev; subst hev
  all_goals exact ⟨rfl, rfl⟩

/-- **The paired operations are fired at the allocation and the relinquishment.** -/
theorem ev_tmem {L : Launch} {g : Nat} {d : D} {e : Event} (hx : ∀ r, d.site ≠ .enter r)
    (hev : Ev L g d e) :
    Tmem.Pair.isTmemOp e = (decide (d.site = .alloc) || decide (d.site = .relinq)) := by
  obtain ⟨site, x1, x2⟩ := d
  obtain ⟨pc, kd⟩ := e
  cases site
  case enter r => exact absurd rfl (hx r)
  case sh j => fin_cases j <;> obtain ⟨_, _, h⟩ := hev <;> simp only at h <;> subst h <;> rfl
  case elect j => obtain ⟨_, _, -, h⟩ := hev; simp only at h; subst h; rfl
  case ld => rcases hev with ⟨_, _, h, -⟩ | ⟨f, h⟩ <;> simp only at h <;> subst h <;> rfl
  case allocSt => obtain ⟨_, -, h⟩ := hev; simp only at h; subst h; rfl
  all_goals simp only [Ev] at hev; subst hev
  all_goals rfl

/-- **A startup state with no paired operation is no later than the allocation**, strictly off
it; with at most one, no later than the relinquishment, strictly off it. -/
theorem time_refT {d : D} {t : Nat} (hT : RefT d t) (hx : ∀ r, d.site ≠ .enter r)
    (hw : d.site = .bar → scmpi .ne .b d.x2 0 = false) :
    (t = 0 → time d + (if d.site = .alloc then 0 else 1) ≤ 92) ∧
      (t ≤ 1 → time d + (if d.site = .relinq then 0 else 1) ≤ 98) := by
  obtain ⟨site, x1, x2⟩ := d
  cases site
  case enter r => exact absurd rfl (hx r)
  case init n =>
    simp only [RefT] at hT
    fin_cases n <;> simp [time, Site.pc, initPc, hT.1]
  all_goals simp_all [RefT, time, Site.pc]
  all_goals (rename_i j; fin_cases j <;> simp)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
