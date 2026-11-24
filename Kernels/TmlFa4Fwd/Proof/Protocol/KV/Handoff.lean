-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Bound
public import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
public import Lemmas.Protocol.NoIncUnits
public import Lemmas.Protocol.UnitNotify
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
import Kernels.TmlFa4Fwd.Proof.Lib.PollSpin
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Tmem
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.EmptyPoll
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
public import Kernels.TmlFa4Fwd.Proof.Protocol.P.Obj
import Lemmas.Protocol.MultiObs
import Lemmas.Protocol.ReachJoint
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The K/V ring's slots as rings of kinds

Slot `s` of the K/V ring of a CTA: the full barrier `32 + 8 s` (count 64, an arrive-on of each of
the 64 loader lanes per use) and the empty barrier `56 + 8 s` (count 1, a commit of the one lane of
warp 12 that commits). A loader lane's arrive-on of use `t` follows `t + 1` polls of the empty
barrier, through a row copy it tracks (`ld_async_arr`); the commit of use `t` follows `t + 1` polls
of the full barrier (`mma_kv_commit`). So the slot is a `MbarRing.KRing` (`kvRing`), whose hand-offs
in both directions are `kvHandoff`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Frame (MbarOf)
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The full and the empty barrier of slot `s`. -/
abbrev kvF (L : Launch) (g : Nat) (s : Fin 3) : Loc := obj L g (32 + 8 * s.val)
abbrev kvE (L : Launch) (g : Nat) (s : Fin 3) : Loc := obj L g (56 + 8 * s.val)

open Classical in
/-- The lane of warp 12 that commits to the barrier at offset `o` of lane `g`'s CTA (when none
does, the one that issues the CTA's MMAs, and the warp's first lane when none does). -/
def commitLane (L : Launch) (X : Execution) (g o : Nat) : Nat :=
  if h : ∃ c i pc sp r, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ ∧
      TcCommit.target sp r = some (obj L g o) then Classical.choose h
  else if h : ∃ c i d s acc mask, X.MmaIssue (c, i) d s acc mask ∧ MmaIn L g c then
    Classical.choose h
  else g / L.block * L.block + 384

/-- A row copy of loader lane `a` after `t + 1` polls of the empty barrier, before its arrive-on
`t`. -/
def KvCopy (L : Launch) (X : Execution) (g : Nat) (s : Fin 3) (a : Fin 64) (t j : Nat) : Prop :=
  j < (NoInc.op X (kvF L g s) (ldProd L g) a t).2 ∧
    (∃ pc sp, X.get (ldProd L g a, j) = some ⟨pc, .copy sp⟩ ∧ sp.completion = .asyncGroup) ∧
    t + 1 ≤ okPolls (kvE L g s) ((X.tr (ldProd L g a)).take j)

open Classical in
/-- That copy's event. -/
def kvOp (L : Launch) (X : Execution) (g : Nat) (s : Fin 3) (a : Fin 64) (t : Nat) : EvId :=
  (ldProd L g a, if h : ∃ j, KvCopy L X g s a t j then Classical.choose h else 0)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

theorem commitLane_eq {o c i pc : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (he : X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp r = some (obj L g o)) : c = commitLane L X g o := by
  have hex : ∃ c i pc sp r, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ ∧
      TcCommit.target sp r = some (obj L g o) := ⟨c, i, pc, sp, r, he, ht⟩
  unfold commitLane
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨i', pc', sp', r', he', ht'⟩ := Classical.choose_spec hex
  exact mma_commit_lane hp hX hFw he ht he' ht'

theorem commitLane_in (hg : g < L.threads) (o : Nat) : MmaIn L g (commitLane L X g o) := by
  by_cases hex : ∃ c i pc sp r, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ ∧
      TcCommit.target sp r = some (obj L g o)
  · obtain ⟨c, i, pc, sp, r, he, ht⟩ := hex
    rw [← commitLane_eq hp hX hFw he ht]
    obtain ⟨h1, h2, h3, -⟩ := mma_commit_of hp hX hFw he ht
    exact ⟨h1, h2, h3⟩
  by_cases hmm : ∃ c i d s acc mask, X.MmaIssue (c, i) d s acc mask ∧ MmaIn L g c
  · have he : commitLane L X g o = Classical.choose hmm := by
      unfold commitLane
      rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_left_of_eq_true (eq_true hmm)]
    rw [he]
    obtain ⟨_, _, _, _, _, -, h⟩ := Classical.choose_spec hmm
    exact h
  · have he : commitLane L X g o = g / L.block * L.block + 384 := by
      unfold commitLane
      rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hmm)]
    have hb := hp.block
    have hc : (g / L.block * L.block + 384) / L.block = g / L.block := by rw [hb]; omega
    rw [he]
    refine ⟨thread_lt_of_cta hg hc, hc, ?_⟩
    simp only [Prologue.warpIndex, hb]
    omega

/-- **The lane that issues the CTA's MMAs is the one that commits.** -/
theorem commitLane_mma {o : Nat} {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d sp acc mask) (hin : MmaIn L g i.1) :
    i.1 = commitLane L X g o := by
  by_cases hex : ∃ c i pc sp r, X.get (c, i) = some ⟨pc, .tc (.commit sp)⟩ ∧
      TcCommit.target sp r = some (obj L g o)
  · obtain ⟨c, i', pc, sp', r, he, ht⟩ := hex
    rw [← commitLane_eq hp hX hFw he ht]
    obtain ⟨-, h2, h3, -⟩ := mma_commit_of hp hX hFw he ht
    exact Mma.mma_commit_lane hp hX hin.2.2 h3 (hin.2.1.trans h2.symm) (k := i.2) hi ⟨pc, he⟩
  · have hmm : ∃ c i d s acc mask, X.MmaIssue (c, i) d s acc mask ∧ MmaIn L g c :=
      ⟨i.1, i.2, d, sp, acc, mask, hi, hin⟩
    have he : commitLane L X g o = Classical.choose hmm := by
      unfold commitLane
      rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_left_of_eq_true (eq_true hmm)]
    rw [he]
    obtain ⟨i', d', s', acc', mask', hi', hin'⟩ := Classical.choose_spec hmm
    exact Mma.mma_lane hp hX hin.2.2 hin'.2.2 (hin.2.1.trans hin'.2.1.symm) (k := i.2) hi hi'

/-- **The empty barrier of slot `s` is a commit object** of one lane, polled with offset 1. -/
theorem kvNotify (g : Nat) (s : Fin 3) :
    Notify.Obj X (kvE L g s) (commitLane L X g (56 + 8 * s.val)) (kvE L g s) 1 := by
  have hs := s.isLt
  have hoE : EmptyOff (56 + 8 * s.val) := by unfold EmptyOff; omega
  obtain ⟨q, hq, hcn⟩ := empty_init hoE
  have hinit : PairTmaRing.InitFirst X (kvE L g s) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hcn] at this
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e) (hm : MbarOf e (kvE L g s))
      (hni : ∀ c, e.kind ≠ .mbInit (kvE L g s) c) =>
    empty_use hp hX hFw hoE he hm hni
  refine Notify.Obj.of_commits hX hinit (fun {h i pc tx cnt rel sc} he => ?_)
    (fun {i pc a sp} he hm => ?_) (fun {i pc s} he hm => ?_) (fun {i pc m' noinc} he hm => ?_)
    (fun {i pc sp tg} he => no_clc hp hX hFw i.1 i.2 pc sp tg he)
    (fun {i pc m'} he => no_inval hp hX hFw i m' ⟨pc, he⟩)
    (fun {i pc sp r} he ht => ⟨commitLane_eq hp hX hFw (c := i.1) (i := i.2) he ht,
      (mma_commit_of hp hX hFw (h := i.1) (k := i.2) he ht).2.2.2.1⟩)
    (fun {h k pc par acq sc} he => ?_) le_rfl
  · rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · rcases hU he hm (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · subst hm
    rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  · obtain ⟨hc, hu⟩ := bar_use (o := 56 + 8 * s.val) hp hX hFw he rfl (fun _ h => by cases h)
    cases hu with
    | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
    | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
    | epiPoll _ _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho => omega
    | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
    | ldPoll par' ok hw _ hk =>
      simp only [kvE] at he ⊢
      rw [← obj_cta hc] at he ⊢
      exact ld_empty_par hp hX hFw hoE hw (Frame.lt_of_get hX he) he

/-- A counted arrive-on's copy. -/
theorem kvOp_spec {s : Fin 3} {a : Fin 64} {t pc : Nat}
    (he : X.get (NoInc.op X (kvF L g s) (ldProd L g) a t) =
      some ⟨pc, .asyncArrive (kvF L g s) true⟩)
    (hcnt : ((X.tr (ldProd L g a)).take (NoInc.op X (kvF L g s) (ldProd L g) a t).2).countP
      (arriveOnTo (kvF L g s)) = t) :
    ∃ j, kvOp L X g s a t = (ldProd L g a, j) ∧ KvCopy L X g s a t j := by
  have hb := hp.block
  have ha := a.isLt
  have hcy : ldProd L g a / L.block = g / L.block := by simp only [ldProd, hb]; omega
  have hwy : Prologue.warpIndex L (ldProd L g a) = 14 ∨
      Prologue.warpIndex L (ldProd L g a) = 15 := by
    simp only [Prologue.warpIndex, ldProd, hb]
    have : (g / 512 * 512 + 448 + a.val) % 512 = 448 + a.val := by omega
    rw [this]; omega
  have he' : X.get (ldProd L g a, (NoInc.op X (kvF L g s) (ldProd L g) a t).2) =
      some ⟨pc, .asyncArrive (obj L (ldProd L g a) (32 + 8 * s.val)) true⟩ := by
    rw [obj_cta hcy]; exact he
  obtain ⟨-, j, pcj, sp, hj, hget, hgrp, hpoll⟩ := ld_async_arr hp hX hFw hwy s he'
  rw [obj_cta hcy, obj_cta hcy, hcnt] at hpoll
  have hex : ∃ j, KvCopy L X g s a t j := ⟨j, hj, ⟨pcj, sp, hget, hgrp⟩, hpoll⟩
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  simp only [kvOp]
  rw [dite_eq_left_of_eq_true (eq_true hex)]

/-- **Slot `s` of the K/V ring as a ring of kinds.** -/
def kvRing (g : Nat) (hg : g < L.threads) (s : Fin 3) : KRing L kernel X 64 1 64 :=
  have hs := s.isLt
  have hoF : KvOff (32 + 8 * s.val) := by unfold KvOff; omega
  have o : NoIncObject X (kvF L g s) 64 := kvObj hp hX hFw hoF g
  have hsrc := kv_src (g := g) hp hX hFw hoF
  have N := kvNotify hp hX hFw g s
  have hc := commitLane_in hp hX hFw hg (56 + 8 * s.val)
  have hparF : ∀ {h k pc par : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (kvF L g s) par true acq sc⟩ →
      par % 2 = (okPolls (kvF L g s) ((X.tr h).take k) + 0) % 2 := by
    intro h k pc par acq sc he
    obtain ⟨-, hu⟩ := bar_use (o := 32 + 8 * s.val) hp hX hFw he rfl (fun _ h => by cases h)
    cases hu with
    | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
    | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
    | epiPoll _ _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho => omega
    | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
    | mmaPoll _ _ _ hk =>
      simp only [Kind.wait.injEq] at hk
      simp only [kvF]
      omega
  { F := kvF L g s
    E := kvE L g s
    prod := ldProd L g
    cons := fun _ => commitLane L X g (56 + 8 * s.val)
    ownF := id
    opF := kvOp L X g s
    itF := NoInc.it X (kvF L g s) (ldProd L g)
    cm := fun _ t => (commitLane L X g (56 + 8 * s.val),
      Notify.cm X (commitLane L X g (56 + 8 * s.val)) (kvE L g s) t)
    note := fun _ t => Notify.it X (kvE L g s) (commitLane L X g (56 + 8 * s.val)) (kvE L g s) t
    SF := NoInc.S X (kvF L g s) (ldProd L g)
    SE := Notify.S X (kvE L g s) (commitLane L X g (56 + 8 * s.val)) (kvE L g s)
    cover := fun a => ⟨a, rfl⟩
    cF := NoInc.counted o
    cE :=
      { record := fun x hx => by
          obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := N.S_rec hx
          exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
        init := ⟨1, N.init⟩
        noInval := N.noInval }
    spins := poll_spin hX
    parF := fun _ _ _ _ _ _ he => hparF he
    parE := fun _ _ _ _ _ _ he => N.parity he
    fullF := fun _ j hj => NoInc.card_phase hX o hsrc (δ := 0) (Nat.zero_le _)
      (MbarRing.Poll.alternates hX ((NoInc.counted (prod := ldProd L g) o).pclean hX)
        fun _ _ _ _ _ he => hparF he) (Nat.zero_le _) hj
    fullE := fun a n hn hj => N.card_phase hX (h := ldProd L g a) hn hj
    polF := fun x hx => by
      obtain ⟨-, ⟨pc, he⟩, hcnt, -⟩ := NoInc.S_rec o hx
      obtain ⟨j, hj, -, ⟨pcj, sp, hget, -⟩, hpoll⟩ := kvOp_spec hp hX hFw he hcnt
      exact ⟨j, hj, len_of_get hget, hpoll⟩
    polE := fun y hy => by
      obtain ⟨-, pc, sp, hget, hb, -, hcnt⟩ := N.S_rec hy
      refine ⟨_, rfl, len_of_get hget, ?_⟩
      have hob := fun o => obj_cta (L := L) hc.2.1 o
      have hb' : sp.mbar = obj L (commitLane L X g (56 + 8 * s.val)) (56 + 8 * s.val) := by
        rw [hob]; exact hb
      have h1 := mma_kv_commit hp hX hFw s hc.2.2 hget hb'
      simp only [kvE, kvF] at hcnt ⊢
      rw [hob, hob] at h1
      rw [hcnt] at h1
      exact h1
    issueF := fun x hx => by
      obtain ⟨-, ⟨pc, he⟩, hcnt, harr⟩ := NoInc.S_rec o hx
      obtain ⟨j, hj, hjl, ⟨pcj, sp, hget, hgrp⟩, -⟩ := kvOp_spec hp hX hFw he hcnt
      have ht : TracksCpAsync X (ldProd L g x.1, j)
          (NoInc.op X (kvF L g s) (ldProd L g) x.1 x.2) :=
        ⟨rfl, hjl, ⟨sp, ⟨_, hget⟩, hgrp⟩, _, true, ⟨_, he⟩⟩
      have hw : X.AsyncPresent (ldProd L g x.1, j) (.write .copy) :=
        (hX.tma.2.2.2 _ harr).2 _ ht
      rw [hj]
      exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := kernel)
        (p := .write .copy) ⟨_, hget⟩ hw (fun _ h => by cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hw)).tail
        (DepStep.stage (c := (NoInc.it X (kvF L g s) (ldProd L g) x.1 x.2, false))
          (.inr ⟨rfl, rfl, ht, hw, harr⟩))).to_reflTransGen
    issueE := fun y hy => by
      obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hget, -⟩ := N.S_rec hy
      obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
      exact .single (Reach.commit_notify hget hr) }

/-- **The K/V hand-offs** of slot `s`, with the lane `c` of warp 12 that commits its release: `c`'s
poll of the full barrier with `u` earlier ones observes every loader lane's arrive-on with `u`
earlier ones, so finishes the copies it tracks; a loader lane's poll of the empty barrier with
`u + 1` earlier ones observes the notification of `c`'s commit with `u` earlier ones, so the
completion of the MMAs it tracks: a slot's next copies follow every read of it. -/
theorem kvHandoff (g : Nat) (hg : g < L.threads) (s : Fin 3) : ∃ c, MmaIn L g c ∧
    (∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (kvE L g s) →
        i.1 = c) ∧
    (∀ {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d sp acc mask → MmaIn L g i.1 → i.1 = c) ∧
    (∀ {j pc par u : Nat} {acq : Bool} {sc : MbarScope},
      X.get (c, j) = some ⟨pc, .wait (kvF L g s) par true acq sc⟩ →
      okPolls (kvF L g s) ((X.tr c).take j) = u → ∀ a : Fin 64,
        ∃ i pci, X.get (ldProd L g a, i) = some ⟨pci, .asyncArrive (kvF L g s) true⟩ ∧
          ((X.tr (ldProd L g a)).take i).countP (arriveOnTo (kvF L g s)) = u ∧
          X.async.arrived (ldProd L g a, i) = true ∧
          WaitObserves X (.async (ldProd L g a, i) .arriveOn) (c, j) (kvF L g s) acq sc) ∧
    ∀ {y j pc par u : Nat} {acq : Bool} {sc : MbarScope}, LdLane L g y →
      X.get (y, j) = some ⟨pc, .wait (kvE L g s) par true acq sc⟩ →
      okPolls (kvE L g s) ((X.tr y).take j) = u + 1 →
        ∃ i pci sp rank, X.get (c, i) = some ⟨pci, .tc (.commit sp)⟩ ∧ sp.mbar = kvE L g s ∧
          ((X.tr c).take i).countP (commitsTo (kvE L g s)) = u ∧
          u + 1 ≤ okPolls (kvF L g s) ((X.tr c).take i) ∧
          WaitObserves X (.async (c, i) (.tcNotify rank)) (y, j) (kvE L g s) acq sc ∧
          ∀ rd, TracksMma X rd (c, i) → AsyncObserved X rd .mmaDone (y, j) acq sc := by
  have hs := s.isLt
  have hoF : KvOff (32 + 8 * s.val) := by unfold KvOff; omega
  have o : NoIncObject X (kvF L g s) 64 := kvObj hp hX hFw hoF g
  have N := kvNotify hp hX hFw g s
  have hc := commitLane_in hp hX hFw hg (56 + 8 * s.val)
  refine ⟨commitLane L X g (56 + 8 * s.val), hc,
    fun {i pc sp r} he ht => commitLane_eq hp hX hFw (c := i.1) (i := i.2) he ht,
    fun hi hin => commitLane_mma hp hX hFw hi hin, ?_, ?_⟩
  · intro j pc par u acq sc he hu a
    have hlt : u < okPolls (kvF L g s) (X.tr (commitLane L X g (56 + 8 * s.val))) := by
      rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
    obtain ⟨hS, hub⟩ := (kvRing hp hX hFw g hg s).full_observes hX (b := 0) hlt a
    obtain ⟨-, ⟨pci, hget⟩, hcnt, harr⟩ := NoInc.S_rec o hS
    change MBarrier.UpdateBeforeWait _ _ (Ref.thread (commitLane L X g (56 + 8 * s.val),
      Poll.nth X (kvF L g s) (commitLane L X g (56 + 8 * s.val)) u)) at hub
    rw [show Poll.nth X (kvF L g s) (commitLane L X g (56 + 8 * s.val)) u = j by
      rw [← hu]; exact Poll.nth_eq he] at hub
    exact ⟨_, pci, hget, hcnt, harr, ⟨⟨pc, par, he⟩, hub⟩⟩
  · intro y j pc par u acq sc hy he hu
    obtain ⟨a, rfl⟩ := ldLane_prod hy
    have hlt : u + 1 < okPolls (kvE L g s) (X.tr (ldProd L g a)) := by
      rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
    obtain ⟨hS, hub⟩ := (kvRing hp hX hFw g hg s).empty_observes hX (a := a) hlt 0
    obtain ⟨⟨k, r, hk, hid, -, -⟩, pci, sp, hget, hb, ht, hcnt⟩ := N.S_rec hS
    obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
    obtain ⟨i, hi, -, hpoll⟩ := (kvRing hp hX hFw g hg s).polE (0, u) hS
    have hii : i = Notify.cm X (commitLane L X g (56 + 8 * s.val)) (kvE L g s) u :=
      (congrArg Prod.snd hi).symm
    subst hii
    change MBarrier.UpdateBeforeWait _ _ (Ref.thread (ldProd L g a,
      Poll.nth X (kvE L g s) (ldProd L g a) (u + 1))) at hub
    rw [show Poll.nth X (kvE L g s) (ldProd L g a) (u + 1) = j by
      rw [← hu]; exact Poll.nth_eq he] at hub
    have hobs : WaitObserves X (.async (commitLane L X g (56 + 8 * s.val),
        Notify.cm X (commitLane L X g (56 + 8 * s.val)) (kvE L g s) u)
        (.tcNotify (Notify.rank X (kvE L g s) (commitLane L X g (56 + 8 * s.val))
          (kvE L g s) u))) (ldProd L g a, j) (kvE L g s) acq sc := ⟨⟨pc, par, he⟩, hub⟩
    exact ⟨_, pci, sp, _, hget, hb, hcnt, hpoll, hobs, fun rd hrd =>
      ⟨_, _, ⟨_, sp, _, rfl, hrd, ⟨_, hget⟩, ht, hr⟩, hobs⟩⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
