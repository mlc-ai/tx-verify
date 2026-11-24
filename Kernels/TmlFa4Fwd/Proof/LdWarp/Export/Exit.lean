-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A loader lane's counts at its exit

A loader lane that loaded `A` packets has made, at its exit, `32 A` row copies, an arrive-on per
packet on the packet's full slot, and one poll more than that of each empty slot: the drain's. A
lane of warp 14 with a packet has polled the second Q stage's empty barrier twice (`ld_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

set_option maxHeartbeats 8000000 in
/-- An exit is fired at the exit site. -/
theorem ld_exit_at {w : Nat} {d : Loader.D} {e : Event} (hev : Loader.Ev p L h w d e)
    (hk : e.kind = .exit) : d.site = .exit := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨site, v, kk⟩ := d
  cases site <;> simp only [Loader.Ev] at hev
  case exit => rfl
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev, Loader.Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all

/-- The occurrences of a slot among three more packets. -/
private theorem ringCnt_three (A : Nat) (s : Nat) (hs : s < 3) :
    Loader.ringCnt (A + 3) s = Loader.ringCnt A s + 1 := by
  rw [show A + 3 = A + 1 + 1 + 1 from rfl, Loader.ringCnt_succ, Loader.ringCnt_succ,
    Loader.ringCnt_succ]
  split_ifs <;> omega

/-- The occurrences of slot `c mod 3` before packet `A > c`. -/
private theorem ringCnt_gt {A c : Nat} (h : c < A) : c / 3 + 1 ≤ Loader.ringCnt A (c % 3) := by
  have hf : ∀ n s, s < 3 → Loader.ringCnt n s = (n + 2 - s) / 3 := by
    intro n s hs
    induction n with
    | zero => simp [Loader.ringCnt]; omega
    | succ n ih => rw [Loader.ringCnt_succ, ih]; split <;> omega
  rw [hf _ _ (Nat.mod_lt _ (by decide))]
  omega

/-- **A loader lane's counts at its exit.** -/
theorem ld_exit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc : Nat} (he : X.get (h, k) = some ⟨pc, .exit⟩) :
    ∃ A, (∀ s : Fin 3,
        okPolls (obj L h (56 + 8 * s.val)) ((X.tr h).take k) =
          ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) + 1) ∧
      (∀ c < A, c / 3 + 1 ≤
        ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * (c % 3))))) ∧
      ((X.tr h).take k).countP cpCopy = 32 * A ∧
      (Prologue.warpIndex L h = 14 → 0 < A → okPolls (obj L h 24) ((X.tr h).take k) = 2) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .exit⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    have hx : exit L h s' = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  have hs := ld_exit_at hev rfl
  have harr : ∀ s : Fin 3,
      ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) =
        Loader.ringCnt (n (.load .commit)) s.val := fun s => by
    have h1 := Loader.arr_ring hp hX hg hw hσ h0 s
    simp only [hs, Loader.inPkt, Nat.sub_zero, LdWarp.lcn] at h1
    refine Eq.trans ?_ h1
    refine Eq.trans ?_ (count hσ (.load (.asyncArrive (obj L h (32 + 8 * s.val)))))
    refine List.countP_congr fun e hme => ?_
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hme
    have hget : X.get (h, j) = some e := by
      rw [List.length_take] at hj
      change (X.tr h)[j]? = _
      rw [← hje, List.getElem_take, List.getElem?_eq_getElem]
    obtain ⟨pce, kd⟩ := e
    cases kd with
    | asyncArrive l ni =>
      cases ni with
      | true => simp [MbarRing.arriveOnTo, cls, Loader.cls]
      | false =>
        exfalso
        rcases ld_mbar_use hp hX hFw hw hget (l := l) rfl (fun _ h => by cases h) with
          ⟨_, _, _, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, _, hk, _⟩ <;>
          cases hk
    | _ => simp [MbarRing.arriveOnTo, cls, Loader.cls]
  refine ⟨n (.load .commit), fun s => ?_, fun c hc => ?_, ?_, fun h14 hA => ?_⟩
  · rw [show okPolls (obj L h (56 + 8 * s.val)) ((X.tr h).take k) =
      n (.load (.acquire (obj L h (56 + 8 * s.val)))) from
      count hσ (.load (.acquire (obj L h (56 + 8 * s.val))))]
    have h1 := Loader.acq_ring hp hX hg hw hσ h0 s
    simp only [hs, Loader.acqOff, LdWarp.lcn] at h1
    rw [harr, ← ringCnt_three _ _ s.isLt]
    exact h1
  · rw [harr ⟨c % 3, Nat.mod_lt _ (by decide)⟩]
    exact ringCnt_gt hc
  · have h1 := Loader.cp_count hp hX hg hw hσ h0
    simp only [Loader.CpCount, hs, Loader.inPkt, LdWarp.lcn] at h1
    change ((X.tr h).take k).countP Loader.isCp = _
    omega
  · rw [show okPolls (obj L h 24) ((X.tr h).take k) =
      n (.load (.acquire (obj L h 24))) from count hσ (.load (.acquire (obj L h 24)))]
    have h1 := Loader.q_acq hp hX hg hw hσ h0 24 (by simp)
    have hb : Loader.wOf b = 14 := by rw [← hR.1] at h14; exact h14
    simp only [hs, LdWarp.lcn, Loader.qAcq, hb, ↓reduceIte] at h1
    refine Eq.trans h1 ?_
    rw [ite_eq_right (by omega)]

/-- **A tensor load follows a packet's row copies.** -/
theorem ld_tma_copies (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc a : Nat} {sp : TensorCopy.Spec} (he : X.get (h, k) = some ⟨pc, .tensorIssue a sp⟩) :
    1 ≤ ((X.tr h).take k).countP cpCopy := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tensorIssue a sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := sp.mbar) rfl
    cases hc
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, hC⟩ := hJl.refE
  obtain ⟨-, -, h3, -⟩ := Loader.copy_site hev hub
  obtain ⟨t, c, hs⟩ := h3.mp ⟨a, sp, rfl⟩
  have hc := hC.commit
  simp only [hs, Loader.arrAt, Loader.inPkt, Nat.add_zero] at hc
  have hn : 1 ≤ n (.load .commit) := by
    change n (.load .commit) = _ at hc
    rw [hc]
    unfold Loader.tmaPk
    have h2 : t.val < 4 ∨ 1 ≤ kk := by
      by_cases ht : t.val < 4
      · exact .inl ht
      · refine .inr ?_
        have hw2 := hRing.words
        simp only [hs, Loader.ringCls, ht, ↓reduceIte] at hw2
        by_contra hk
        split at hw2 <;> simp only [Loader.RingWords] at hw2 <;> omega
    split_ifs <;> omega
  have h1 := Loader.cp_count hp hX hg hw hσ h0
  simp only [Loader.CpCount, hs, Loader.inPkt, LdWarp.lcn] at h1
  change 1 ≤ ((X.tr h).take k).countP Loader.isCp
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
