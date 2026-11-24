-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Full
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Lemmas.Protocol.ReachJoint
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Q stages' hand-offs

Stage `s`'s full barrier `8 s` is completed by one lane of warp 14 (`tmaFull`: an expect-tx arrival
and two tensor copies per use) and its empty barrier `16 + 8 s` by the commits of the one lane of
warp 12 that commits (`qNotify`). The items of use `t` follow `t + 1` polls of the empty barrier
(`tmaFull_pol`), the commit of use `t` follows `t + 1` polls of the full barrier (`mma_q_commit`):
the stage is a `MbarRing.KRing` (`qRing`). The premise `TmaBytes` is the copies' byte count. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Frame (MbarOf)
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The full and the empty barrier of Q stage `s`. -/
abbrev qF (L : Launch) (g : Nat) (s : Fin 2) : Loc := obj L g (8 * s.val)
abbrev qE (L : Launch) (g : Nat) (s : Fin 2) : Loc := obj L g (8 * s.val + 16)

/-- The committing lane of stage `s`. -/
abbrev qCons (L : Launch) (X : Execution) (g : Nat) (s : Fin 2) : Nat :=
  commitLane L X g (8 * s.val + 16)

theorem q_tmaOff (s : Fin 2) : LdTmaOff (8 * s.val) := by
  have := s.isLt
  unfold LdTmaOff
  omega

theorem q_empty_init (s : Fin 2) : ∃ q, initOff q = 8 * s.val + 16 ∧ initCnt q = 1 := by
  fin_cases s <;> decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The Q empty barrier of stage `s` is a commit object** of one lane, polled with offset 1. -/
theorem qNotify (g : Nat) (s : Fin 2) :
    Notify.Obj X (qE L g s) (qCons L X g s) (qE L g s) 1 := by
  have hs := s.isLt
  obtain ⟨q, hq, hcn⟩ := q_empty_init s
  have hinit : PairTmaRing.InitFirst X (qE L g s) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hcn] at this
  have hno : ∀ {h k pc : Nat} {kd : Kind}, X.get (h, k) = some ⟨pc, kd⟩ →
      MbarOf ⟨pc, kd⟩ (qE L g s) → (∃ tx c rel sc, kd = .arrive (qE L g s) tx c rel sc) ∨
      (∃ a sp, kd = .tensorIssue a sp) ∨ (∃ noinc, kd = .asyncArrive (qE L g s) noinc) ∨
      (∃ s, kd = .copy s) → False := by
    intro h k pc kd he hm hk
    obtain ⟨-, hu⟩ := bar_use (o := 8 * s.val + 16) hp hX hFw he hm (fun c h => by
      rcases hk with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases h)
    cases hu with
    | ldArr _ _ ho | ldCopy _ _ _ ho => unfold LdTmaOff at ho; omega
    | ldAsync _ ho | epiArr _ _ ho | corrArr _ ho | softArr _ _ _ ho => omega
    | epiPoll _ _ _ _ hk' | corrPoll _ _ _ hk' | softPoll _ _ _ _ _ hk' | mmaPoll _ _ _ hk'
    | ldPoll _ _ _ _ hk' | mmaCommit _ _ _ hk' =>
      simp only at hk'
      rcases hk with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases hk'
  refine Notify.Obj.of_commits hX hinit
    (fun he => hno he rfl (.inl ⟨_, _, _, _, rfl⟩))
    (fun he hm => hno he hm (.inr (.inl ⟨_, _, rfl⟩)))
    (fun {i pc s'} he hm => hno (h := i.1) (k := i.2) he hm (.inr (.inr (.inr ⟨_, rfl⟩))))
    (fun {i pc m' noinc} he hm => by
      subst hm
      exact hno (h := i.1) (k := i.2) he rfl (.inr (.inr (.inl ⟨_, rfl⟩))))
    (fun {i pc sp tg} he => no_clc hp hX hFw i.1 i.2 pc sp tg he)
    (fun {i pc m'} he => no_inval hp hX hFw i m' ⟨pc, he⟩)
    (fun {i pc sp r} he ht => ⟨commitLane_eq hp hX hFw (c := i.1) (i := i.2) he ht,
      (mma_commit_of hp hX hFw (h := i.1) (k := i.2) he ht).2.2.2.1⟩)
    (fun {h k pc par acq sc} he => ?_) le_rfl
  obtain ⟨hc, hu⟩ := bar_use (o := 8 * s.val + 16) hp hX hFw he rfl (fun _ h => by cases h)
  cases hu with
  | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
  | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
  | epiPoll _ _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | ldPoll par' ok hw _ hk =>
    simp only [qE] at he ⊢
    rw [← obj_cta hc] at he ⊢
    exact (ld_tma_empty_par hp hX hFw hw (q_tmaOff s) he).2

/-- **Q stage `s` as a ring of kinds.** -/
def qRing (hB : TmaBytes X) (g : Nat) (hg : g < L.threads) (s : Fin 2) :
    KRing L kernel X 1 1 3 :=
  have hs := s.isLt
  have o := tmaFull hp hX hFw hB g (q_tmaOff s)
  have N := qNotify hp hX hFw g s
  have hc := commitLane_in hp hX hFw hg (8 * s.val + 16)
  have hparF : ∀ {h k pc par : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (qF L g s) par true acq sc⟩ →
      par % 2 = (okPolls (qF L g s) ((X.tr h).take k) + 0) % 2 := by
    intro h k pc par acq sc he
    obtain ⟨-, hu⟩ := bar_use (o := 8 * s.val) hp hX hFw he rfl (fun _ h => by cases h)
    cases hu with
    | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
    | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
    | epiPoll _ _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho => omega
    | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
    | mmaPoll _ _ _ hk =>
      simp only [Kind.wait.injEq] at hk
      simp only [qF]
      omega
  { F := qF L g s
    E := qE L g s
    prod := fun _ => tmaLane L X g
    cons := fun _ => qCons L X g s
    ownF := fun _ => 0
    opF := TmaUnits.op X (qF L g s) (tmaLane L X g) 2
    itF := TmaUnits.it X (qF L g s) (tmaLane L X g) 2
    cm := fun _ t => (qCons L X g s, Notify.cm X (qCons L X g s) (qE L g s) t)
    note := fun _ t => Notify.it X (qE L g s) (qCons L X g s) (qE L g s) t
    SF := TmaUnits.S X (qF L g s) (tmaLane L X g) 2 16384
    SE := Notify.S X (qE L g s) (qCons L X g s) (qE L g s)
    cover := fun a => ⟨0, Subsingleton.elim _ _⟩
    cF := o.counted
    cE :=
      { record := fun x hx => by
          obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := N.S_rec hx
          exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
        init := ⟨1, N.init⟩
        noInval := N.noInval }
    spins := poll_spin hX
    parF := fun _ _ _ _ _ _ he => hparF he
    parE := fun _ _ _ _ _ _ he => N.parity he
    fullF := fun _ j hj => o.card_phase hX (by decide) (by decide) (δ := 0) (Nat.zero_le _)
      (MbarRing.Poll.alternates hX (o.counted.pclean hX) fun _ _ _ _ _ he => hparF he)
      (Nat.zero_le _) hj
    fullE := fun _ n hn hj => N.card_phase hX (h := tmaLane L X g) hn hj
    polF := fun _ hx => tmaFull_pol hp hX hFw hB g (q_tmaOff s) hx
    polE := fun y hy => by
      obtain ⟨-, pc, sp, hget, hb, -, hcnt⟩ := N.S_rec hy
      refine ⟨_, rfl, len_of_get hget, ?_⟩
      have hob := fun o => obj_cta (L := L) hc.2.1 o
      have hb' : sp.mbar = obj L (qCons L X g s) (16 + 8 * s.val) := by
        rw [hob, Nat.add_comm]; exact hb
      have h1 := mma_q_commit hp hX hFw s hc.2.2 hget hb'
      simp only [qE, qF] at hcnt ⊢
      rw [hob, hob, Nat.add_comm 16] at h1
      rw [hcnt] at h1
      exact h1
    issueF := fun _ hx => o.issue hX hx
    issueE := fun y hy => by
      obtain ⟨⟨k, r, hk, hid, -, -⟩, pc, sp, hget, -⟩ := N.S_rec hy
      obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
      exact .single (Reach.commit_notify hget hr) }

/-- **The Q hand-offs** of stage `s`, between the lane `y` of warp 14 that won its elections and the
lane `c` of warp 12 that commits the release: `c`'s poll of the full barrier with `u` earlier ones
observes `y`'s two copies `2 u`, `2 u + 1` on it, and `y`'s poll of the empty barrier with `u + 1`
earlier ones the notification of `c`'s commit with `u` earlier ones, so the MMAs it tracks: a
stage's next copies follow every read of it. -/
theorem qHandoff (hB : TmaBytes X) (g : Nat) (hg : g < L.threads) (s : Fin 2) :
    ∃ c, MmaIn L g c ∧
    (∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (qE L g s) →
        i.1 = c) ∧
    (∀ {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d sp acc mask → MmaIn L g i.1 → i.1 = c) ∧
    (∀ {j pc par u : Nat} {acq : Bool} {sc : MbarScope},
      X.get (c, j) = some ⟨pc, .wait (qF L g s) par true acq sc⟩ →
      okPolls (qF L g s) ((X.tr c).take j) = u → ∀ a : Fin 2,
        ∃ i pci al sp, X.get (tmaLane L X g, i) = some ⟨pci, .tensorIssue al sp⟩ ∧
          sp.mbar = qF L g s ∧
          ((X.tr (tmaLane L X g)).take i).countP (issuesTo (qF L g s)) = 2 * u + a.val ∧
          u + 1 ≤ okPolls (qE L g s) ((X.tr (tmaLane L X g)).take i) ∧
          WaitObserves X (.async (tmaLane L X g, i) (.notify .load)) (c, j) (qF L g s) acq sc) ∧
    ∀ {j pc par u : Nat} {acq : Bool} {sc : MbarScope},
      X.get (tmaLane L X g, j) = some ⟨pc, .wait (qE L g s) par true acq sc⟩ →
      okPolls (qE L g s) ((X.tr (tmaLane L X g)).take j) = u + 1 →
        ∃ i pci sp rank, X.get (c, i) = some ⟨pci, .tc (.commit sp)⟩ ∧ sp.mbar = qE L g s ∧
          ((X.tr c).take i).countP (commitsTo (qE L g s)) = u ∧
          u + 1 ≤ okPolls (qF L g s) ((X.tr c).take i) ∧
          WaitObserves X (.async (c, i) (.tcNotify rank)) (tmaLane L X g, j) (qE L g s) acq sc ∧
          ∀ rd, TracksMma X rd (c, i) →
            AsyncObserved X rd .mmaDone (tmaLane L X g, j) acq sc := by
  have o := tmaFull hp hX hFw hB g (q_tmaOff s)
  have N := qNotify hp hX hFw g s
  have hc := commitLane_in hp hX hFw hg (8 * s.val + 16)
  refine ⟨qCons L X g s, hc,
    fun {i pc sp r} he ht => commitLane_eq hp hX hFw (c := i.1) (i := i.2) he ht,
    fun hi hin => commitLane_mma hp hX hFw hi hin, ?_, ?_⟩
  · intro j pc par u acq sc he hu a
    have hlt : u < okPolls (qF L g s) (X.tr (qCons L X g s)) := by
      rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
    obtain ⟨hS, hub⟩ := (qRing hp hX hFw hB g hg s).full_observes hX (b := 0) hlt a.succ
    obtain ⟨-, -, h1⟩ := o.source hS
    obtain ⟨⟨pci, al, sp, hget, hm⟩, hcnt⟩ := h1 (by simp)
    obtain ⟨i, hi, -, hpol⟩ := tmaFull_pol hp hX hFw hB g (q_tmaOff s) hS
    rw [hi] at hget hcnt
    change MBarrier.UpdateBeforeWait _ (TmaUnits.it X (qF L g s) (tmaLane L X g) 2 a.succ u)
      (Ref.thread (qCons L X g s, Poll.nth X (qF L g s) (qCons L X g s) u)) at hub
    rw [show Poll.nth X (qF L g s) (qCons L X g s) u = j by
      rw [← hu]; exact Poll.nth_eq he,
      show TmaUnits.it X (qF L g s) (tmaLane L X g) 2 a.succ u =
        .async (tmaLane L X g, i) (.notify .load) by
      simp only [TmaUnits.it, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte]
      rw [← hi]] at hub
    exact ⟨i, pci, al, sp, hget, hm, by simpa using hcnt, hpol, ⟨⟨pc, par, he⟩, hub⟩⟩
  · intro j pc par u acq sc he hu
    have hlt : u + 1 < okPolls (qE L g s) (X.tr (tmaLane L X g)) := by
      rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
    obtain ⟨hS, hub⟩ := (qRing hp hX hFw hB g hg s).empty_observes hX (a := 0) hlt 0
    obtain ⟨⟨k, r, hk, hid, -, -⟩, pci, sp, hget, hb, ht, hcnt⟩ := N.S_rec hS
    obtain ⟨-, -, -, -, hr⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
    obtain ⟨i, hi, -, hpoll⟩ := (qRing hp hX hFw hB g hg s).polE (0, u) hS
    have hii : i = Notify.cm X (qCons L X g s) (qE L g s) u := (congrArg Prod.snd hi).symm
    subst hii
    change MBarrier.UpdateBeforeWait _ _ (Ref.thread (tmaLane L X g,
      Poll.nth X (qE L g s) (tmaLane L X g) (u + 1))) at hub
    rw [show Poll.nth X (qE L g s) (tmaLane L X g) (u + 1) = j by
      rw [← hu]; exact Poll.nth_eq he] at hub
    have hobs : WaitObserves X (.async (qCons L X g s,
        Notify.cm X (qCons L X g s) (qE L g s) u)
        (.tcNotify (Notify.rank X (qE L g s) (qCons L X g s) (qE L g s) u)))
        (tmaLane L X g, j) (qE L g s) acq sc := ⟨⟨pc, par, he⟩, hub⟩
    exact ⟨_, pci, sp, _, hget, hb, hcnt, hpoll, hobs, fun rd hrd =>
      ⟨_, _, ⟨_, sp, _, rfl, hrd, ⟨_, hget⟩, ht, hr⟩, hobs⟩⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
