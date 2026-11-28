-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefBar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time

@[expose] public section

/-! # Warpgroup 0's warp-collective `tcgen05` events and votes by state

The role's collective events (`isTcColl`: the Tensor Memory loads, stores, their waits and the
deallocation) are at the collective sites (`Site.isTc`, `evK_tc`). Their number before a state
is not a function of the state alone: block `r`'s rescale arm (sixteen collectives) runs when the
block is not the first and the block's vote is true. With `H r` the arms of the blocks below `r`,
the number is `tcOrd w d H`: three per block (the score loads and their wait), sixteen per arm,
and the block's own (`locL`, by the site's order; past the arm by the decision `armV`), then
eight in the epilogue (`locE`) and the deallocation of warp 0. The votes before a state are
`vOrd d`, one per block.

* `succ_tc`: a step off the block's end adds one at a collective site and one vote at the vote
  site, keeps the vote word off the vote site (`VtOk`) and the arm's decision (`ArmOk`);
* `arrS_tc`: the block's end moves to the next block or the epilogue with the same numbers, when
  `H` adds the block's arm. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The sites of the collective events. -/
def Site.isTc : Site → Bool
  | .sld _ _ | .sldw | .rld _ | .rldw _ | .rst _ | .rstw _ | .old _ | .oldw _ | .dealloc => true
  | _ => false

/-- The sites of the rescale arm. -/
def Site.isArm : Site → Bool
  | .rsf | .rld _ | .rldw _ | .rst _ | .rstw _ | .rsfb => true
  | _ => false

/-- The block's arm runs (`afterOst`): the block is not the first and its vote is true. -/
def armV (d : D) : Bool := !(scmpi .eq .b d.bi 1 || !d.vt)

/-- A block's collectives before order `o`: the score loads and wait (orders 4–6), and the arm's
(orders 56–71) if it runs. -/
def locL (o : Nat) (v : Bool) : Nat := min (o - 4) 3 + if v then min (o - 56) 16 else 0

/-- The epilogue's collectives before order `o`: chunk `c`'s load and wait at `7 + 38 c`,
`8 + 38 c`. -/
def locE (o : Nat) : Nat := min 4 ((o + 30) / 38) + min 4 ((o + 29) / 38)

/-- **The collective events before a state** of warp word `w`, with `H r` arms below block `r`. -/
def tcOrd (w : BitVec 64) (d : D) (H : Nat → Nat) : Nat :=
  match d.site with
  | .ebar => 3 * rounds d.l0 d.l1 + 16 * H (rounds d.l0 d.l1) + 8
  | .dealloc => 3 * rounds d.l0 d.l1 + 16 * H (rounds d.l0 d.l1) + 8 -
      (if scmpi .ne .b w 0 then 1 else 0)
  | .exit => 3 * rounds d.l0 d.l1 + 16 * H (rounds d.l0 d.l1) + 8 +
      (if scmpi .ne .b w 0 then 0 else 1)
  | s => match s.reg with
    | .setup => 0
    | .loop => 3 * (d.bi.toNat - 1) + 16 * H (d.bi.toNat - 1) + locL (s.ord + elOff d) (armV d)
    | _ => 3 * rounds d.l0 d.l1 + 16 * H (rounds d.l0 d.l1) + locE (s.ord + elOff d)

/-- **The votes before a state**: one per block. -/
def vOrd (d : D) : Nat :=
  match d.site.reg with
  | .setup => 0
  | .loop => d.bi.toNat - 1 + (if 38 < d.site.ord then 1 else 0)
  | _ => rounds d.l0 d.l1

/-- Past the block's vote the vote word is `V` of the block. -/
def VtOk (d : D) (V : Nat → Bool) : Prop :=
  d.site.reg = .loop → 38 < d.site.ord → d.vt = V (d.bi.toNat - 1)

/-- In the arm the arm runs. -/
def ArmOk (d : D) : Prop := d.site.isArm = true → armV d = true

/-- The result of a mode vote (`false` for any other event). -/
def vres (e : Event) : Bool :=
  match e.kind with
  | .voteMode _ _ _ r => r
  | _ => false

/-- **The votes along a step**: one more at the vote site; the vote word is kept off the vote site
and is the vote's result after it; the arm's decision holds in the arm. -/
def VoteStep (V : Nat → Bool) (d d' : D) (e : Event) : Prop :=
  vOrd d' = vOrd d + (if d.site = .vote then 1 else 0) ∧
    (d.site ≠ .vote → VtOk d V → VtOk d' V) ∧
    (d.site = .vote → d'.vt = vres e ∧ d'.bi = d.bi ∧ d'.site = .ost 0) ∧ ArmOk d'

/-- **A collective event is fired exactly at a collective site.** -/
theorem evK_tc {d : D} {e : Event} (hu : ∀ f, e.kind ≠ .ub f) (hev : EvK P L g w d e) :
    isTcColl e = d.site.isTc := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  have hu' : ∀ f, kd ≠ .ub f := hu
  cases hc : isTcColl ⟨pc, kd⟩
  · cases s <;> simp only [Site.isTc] <;> simp only [EvK, TcLdEv, TcStEv] at hev
    all_goals obtain ⟨_, rfl⟩ | ⟨f, rfl⟩ := hev
    all_goals first | exact absurd rfl (hu' _) | simp [isTcColl] at hc
  · obtain ⟨a, rfl⟩ := isTcColl_kind hc
    cases s <;> simp only [Site.isTc] <;>
      simp [EvK, NcEv, ArrEv, PollEv, RdAt, WrAt, GWrAt, GenWrAt] at hev <;>
      subst hev <;> simp [isTcColl] at hc

set_option hygiene false in
/-- Open a step of the control machine off the block's end from a site of region `hr`: every
site of the region, every branch. -/
macro "w0_succ" : tactic => `(tactic| (
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  revert hs hr
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals intro hs' hr'
  all_goals first
    | exact absurd rfl hs'
    | exact absurd hr' (by decide)
    | skip
  all_goals
    simp only [succ, dataRd, tcLoad, ncWord, poll, elemNext, afterSmr, afterSink, hb,
      Bool.false_eq_true, ↓reduceIte, afterA, finish, afterOst, nextChunk, afterObar, afterEld,
      loopEntry, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
      List.getD_cons_succ, Fin.zero_eta, Fin.mk_one] at hn
    repeat' split at hn
    all_goals (simp only [Option.some.injEq, reduceCtorEq] at hn) <;> subst hn))

set_option hygiene false in
/-- Close the vote goals of a step. -/
macro "w0_vote" : tactic => `(tactic| (
  all_goals refine ⟨?_, fun hv hV => ?_, fun hv => ?_, fun hA => ?_⟩
  all_goals first
    | (simp only [vOrd, VtOk, ArmOk, Site.reg, Site.ord, Site.isArm, reduceCtorEq, ite_false,
        Nat.add_zero, Bool.false_eq_true, false_implies, ne_eq, not_true_eq_false] at *; done)
    | (simp_all [vOrd, VtOk, vres, ArmOk, armV, Site.reg, Site.ord, Site.isArm, rounds,
        i32_one_toNat, w0Wv, w0Wq, w0ArrV, w0ArrL, w0Wsv, w0ArrS] <;> (try split_ifs at *) <;>
        first | omega | (cases hq : scmpi .eq .b bi 1 <;> cases vt <;> simp_all))))

set_option hygiene false in
/-- Close a numeric goal of a step. -/
macro "w0_num" : tactic => `(tactic| (
  all_goals simp_all [tcOrd, Site.reg, Site.ord, Site.isTc, Site.isArm, ArmOk, elOff,
    locL, locE, armV, chunkBase, rounds, i32_one_toNat, w0Wv, w0Wq, w0ArrV, w0ArrL, w0Wsv,
    w0ArrS] <;> (try split_ifs at *) <;>
    first | omega | (cases hq : scmpi .eq .b bi 1 <;> cases vt <;> simp_all)))

section
variable {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
  (hs : d.site ≠ .arrS) (hn : succ P L g w d e = some (some d')) {H : Nat → Nat}
  (ha : ArmOk d)
include hb hs hn ha

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_setup
    (hr : d.site.reg = .setup)
    {H : Nat → Nat} (hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_setup
    (hr : d.site.reg = .setup) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_tcOrd_fin
    (hr : d.site.reg = .fin)
    {H : Nat → Nat} (_hH : H 0 = 0) :
    tcOrd w d' H = tcOrd w d H + if d.site.isTc then 1 else 0 := by
  w0_succ
  w0_num

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem succ_vote_fin
    (hr : d.site.reg = .fin) (V : Nat → Bool) :
    VoteStep V d d' e := by
  w0_succ
  w0_vote

end

/-- **The block's end** (block `r`) moves to block `r + 1` or the epilogue with the same numbers,
when `H` adds block `r`'s arm. -/
theorem arrS_tc {d d' : D} {n : Cnt → Nat} {e : Event} (hs : d.site = .arrS)
    (hJ : RefCore L g d n) (hn : succ P L g w d e = some (some d')) {H : Nat → Nat} {v : Bool}
    (hav : armV d = v) (hH : H (d.bi.toNat - 1 + 1) = H (d.bi.toNat - 1) + if v then 1 else 0) :
    tcOrd w d' H = tcOrd w d H ∧ vOrd d' = vOrd d ∧ (∀ V, VtOk d' V) ∧ ArmOk d' := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hs
  subst hs
  simp only [RefCore, Site.reg, Site.idx, Control.D.words, RefAt] at hJ
  obtain ⟨r, hl, -⟩ := hJ
  obtain ⟨-, hR, hrR, hbi, hcnt, -⟩ := hl
  dsimp only at hR hrR hbi hcnt
  subst hbi hcnt
  obtain ⟨he, hc, hn1⟩ := cnt_next hrR hR
  have hr1 : (W (r + 1)).toNat = r + 1 := toNat_W (by omega)
  simp only [hr1, Nat.add_sub_cancel] at hH
  simp only [armV] at hav
  simp only [succ] at hn
  have hv : ∀ x : Bool, locL 74 x = 3 + if x then 16 else 0 := fun x => by
    cases x <;> simp [locL]
  by_cases hlast : r + 1 = rounds l0 l1
  · simp only [advance, he, decide_eq_true hlast, ↓reduceIte, hc, hn1] at hn
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hn
    obtain rfl := some_some_eq hn
    simp only [tcOrd, vOrd, VtOk, ArmOk, Site.reg, Site.ord, Site.isArm, elOff, hr1, ← hlast,
      w0ArrS, locE, hv, hH, armV, hav]
    refine ⟨?_, by simp, by simp, by simp⟩
    cases v <;> simp <;> omega
  · simp only [advance, he, hlast, decide_false, Bool.false_eq_true, ↓reduceIte, hc, hn1, ne_eq,
      not_false_eq_true, decide_true, bi_next (by omega : r < 2 ^ 26)] at hn
    obtain rfl := some_some_eq hn
    have hr2 : (W (r + 1 + 1)).toNat = r + 1 + 1 := toNat_W (by omega)
    simp only [tcOrd, vOrd, VtOk, ArmOk, Site.reg, Site.ord, Site.isArm, elOff, hr1, hr2,
      w0ArrS, locL, hH, armV, hav, Nat.add_sub_cancel]
    refine ⟨?_, by simp, by simp, by simp⟩
    cases v <;> simp <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
