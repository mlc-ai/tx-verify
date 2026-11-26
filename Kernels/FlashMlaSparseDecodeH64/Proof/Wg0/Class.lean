-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Poll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Warpgroup 0's events by pc class

An event of a state of the role (no undefined behaviour, at a pc of the role's code, so not the
exit), the lane's successful polls before it being `es`, is a poll at one of the three wait sites
on its named object (`Objs.lean`) with its parity: at pc 264 the valid-mask slot
`coordReady (slot4 (polls4 … coordReady es))`, at pc 272 the score slot
`qkDone (slot2 (polls2 … qkDone es))`, each with the parity of its own successful polls; at pc
1184 the last block's `svDone (slot2 (b - 1))` with parity `(b - 1) / 2 % 2`, `b` the blocks
(`polls2 … qkDone es`); or neither a poll nor an exit (`ev_class`). The counts come from the
reference invariant (`ready_cnt`, `qk_cnt`). The code at a wait site is an acquiring poll
(`wait_op`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {e : Event}

/-- The pc classes of the role's events, `es` the lane's events before. -/
def PcClass (L : Launch) (g : Nat) (es : List Event) (e : Event) : Prop :=
  (e.pc = 264 ∧ Wait e (loc L g (.coordReady (slot4 (polls4 L g .coordReady es))))
      (okPolls (loc L g (.coordReady (slot4 (polls4 L g .coordReady es)))) es % 2)) ∨
    (e.pc = 272 ∧ Wait e (loc L g (.qkDone (slot2 (polls2 L g .qkDone es))))
      (okPolls (loc L g (.qkDone (slot2 (polls2 L g .qkDone es)))) es % 2)) ∨
    (e.pc = 1184 ∧ Wait e (loc L g (.svDone (slot2 (polls2 L g .qkDone es - 1))))
      ((polls2 L g .qkDone es - 1) / 2 % 2)) ∨
    ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit)

/-- A slot's use at a later place is not counted yet. -/
theorem use_lt {S j r i k : Nat} (h : i < k) : use S j r i k = ringUses S j r := by
  simp [use, ind, Nat.not_le.2 h]

/-- An event that neither polls nor exits is in the last class. -/
theorem pcClass_other {es : List Event} {pc : Nat} {kd k' : Kind} (h : kd = k')
    (h1 : ∀ l q ok a sc, k' ≠ .wait l q ok a sc := by simp) (h2 : k' ≠ .exit := by simp) :
    PcClass L g es ⟨pc, kd⟩ :=
  .inr (.inr (.inr ⟨h ▸ h1, h ▸ h2⟩))

section
variable (hp : Pre P L m)
include hp

/-- **The valid-mask ring's counts at its poll** in block `r`. -/
theorem ready_cnt {es : List Event} {r : Nat}
    (h : ∀ l, okPolls l es = acqCnt (objs L g) r 0 none l) :
    polls4 L g .coordReady es = r ∧ okPolls (loc L g (.coordReady (slot4 r))) es = r / 4 := by
  refine ⟨?_, ?_⟩
  · unfold polls4
    rw [h, h, h, h, acq_ready hp _ _ 0, acq_ready hp _ _ 1, acq_ready hp _ _ 2,
      acq_ready hp _ _ 3]
    simp [use, ind, ringUses]
    omega
  · rw [h, acq_ready hp]
    simp [use, ind, ringUses, slot4]
    omega

/-- **The score ring's counts before its poll** in block `r` (or after the loop, `r` blocks). -/
theorem qk_cnt {es : List Event} {r i : Nat} (hi : i < 2)
    (h : ∀ l, okPolls l es = acqCnt (objs L g) r i none l) :
    polls2 L g .qkDone es = r ∧ okPolls (loc L g (.qkDone (slot2 r))) es = r / 2 := by
  refine ⟨?_, ?_⟩
  · unfold polls2
    rw [h, h, acq_qk hp _ _ 0, acq_qk hp _ _ 1, use_lt hi, use_lt hi]
    simp [ringUses]
    omega
  · rw [h, acq_qk hp, use_lt hi]
    simp [ringUses, slot2]
    omega

/-- **The event of a warpgroup-0 state by its pc class**, `es` the lane's events before, whose
successful polls are the state's counts. -/
theorem ev_class {w : BitVec 64} {d : D} {n : Cnt → Nat} {es : List Event} (hR : Ref P L g d n)
    (hu : n .ub = 0) (hP : ∀ l, okPolls l es = n (.acq l)) (hev : Ev P L g w d e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc0 : e.pc < 1842) : PcClass L g es e := by
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨hc, -⟩ := hR hu
  cases hs : d.site.mb
  · refine .inr (.inr (.inr ⟨fun l q ok a sc h => evK_noMbarOf hs hub hk (l := l) ?_,
      fun h => ?_⟩))
    · obtain ⟨pc, kd⟩ := e
      simp only at h
      subst h
      rfl
    · rw [hpc, evK_exit hk h] at hpc0
      exact absurd hpc0 (by decide)
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub hs ⊢
  subst hpc
  cases site <;> simp only [Site.mb, Bool.false_eq_true] at hs <;>
    simp only [EvK, ArrEv, PollEv] at hk <;>
    simp only [RefCore, RefAt, Site.reg, Site.idx, Control.D.words] at hc
  case arrL | arrV | arrS =>
    rcases hk with hk | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  case wv =>
    obtain ⟨r, ⟨-, -, -, -, -, hvs, hpv, -⟩, hn, -⟩ := hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · simp only at hvs hpv hn
      subst hvs hpv
      obtain ⟨h4, h1⟩ := ready_cnt hp fun l => (hP l).trans (hn l)
      refine .inl ⟨rfl, ok, hk.trans ?_⟩
      rw [h4, h1, parW_W (Nat.mod_lt _ (by decide)), ← vReady_loc hp (slot4 r)]
      rfl
    · exact absurd hk (hub f)
  case wq =>
    obtain ⟨r, ⟨-, -, -, -, -, -, -, hsl, hps⟩, hn, -⟩ := hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · simp only at hsl hps hn
      subst hsl hps
      obtain ⟨h2, h1⟩ := qk_cnt hp (by decide) fun l => (hP l).trans (hn l)
      refine .inr (.inl ⟨rfl, ok, hk.trans ?_⟩)
      rw [h2, h1, parW_W (Nat.mod_lt _ (by decide)), ← qk_loc hp (slot2 r)]
      rfl
    · exact absurd hk (hub f)
  case wsv =>
    obtain ⟨⟨hsl, hps⟩, hn, -⟩ := hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hsl hps hn
      subst hsl hps
      obtain ⟨h2, -⟩ := qk_cnt hp (by decide) fun l => (hP l).trans (hn l)
      refine .inr (.inr (.inl ⟨rfl, ok, hk.trans ?_⟩))
      rw [h2, parW_W (Nat.mod_lt _ (by decide)), ← sv_loc hp (slot2 _)]
      rfl
    · exact absurd hk (hub f)
end

/-- **The code at a wait site is an acquiring poll.** -/
theorem wait_op {d : D} (hw : d.site = .wv ∨ d.site = .wq ∨ d.site = .wsv) :
    ∀ ins, kernel.code[d.site.pc]? = some ins → Sched.waitOp ins.op = true := by
  intro ins hc
  rcases hw with h | h | h <;> rw [h] at hc <;> simp only [Site.pc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
