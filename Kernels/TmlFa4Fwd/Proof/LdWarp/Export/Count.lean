-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Lemmas.Protocol.NoIncRing
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' counts at their packets' arrivals

A loader lane's `cp.async.mbarrier.arrive` on K/V full slot `s` (32 + 8 s) with `u` earlier ones
follows `u + 1` successful polls of empty slot `s` (56 + 8 s), and so does one of the row copies it
tracks (`ld_async_arr`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem ringCnt_mod (c s : Nat) (hc : c % 3 = s) :
    Loader.ringCnt (c + 1) s = Loader.ringCnt c s + 1 := by
  rw [Loader.ringCnt_succ, hc]; simp

/-- The startup issues no copy. -/
private theorem start_no_copy {s : Startup.D} {pc : Nat} {sp : AsyncCopy.Spec}
    (hev' : Startup.Ev L h s ⟨pc, .copy sp⟩) (hx : exit L h s = none) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | enter r => exact absurd hx (by simp [exit])
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev' <;> obtain ⟨_, _, hk⟩ := hev' <;> cases hk
  | fence | bar => simp only [Startup.Ev] at hev'; cases hev'
  | elect j =>
    simp only [Startup.Ev] at hev'
    rcases hev' with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | init q =>
    simp only [Startup.Ev] at hev'
    rcases hev' with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk

private theorem ringCnt_self (c : Nat) : Loader.ringCnt (c + 1) (c % 3) = c / 3 + 1 := by
  have h : ∀ n s, s < 3 → Loader.ringCnt n s = (n + 2 - s) / 3 := by
    intro n s hs
    induction n with
    | zero => simp [Loader.ringCnt]; omega
    | succ n ih => rw [Loader.ringCnt_succ, ih]; split <;> omega
  rw [h _ _ (Nat.mod_lt _ (by decide))]
  omega

/-- **The arrive-ons of a loader lane are its no-increment ones.** -/
theorem arr_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k : Nat}
    (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) (o : Nat) :
    ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h o)) =
      ((X.tr h).take k).countP (cls L h (.load (.asyncArrive (obj L h o)))) := by
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

/-- **A packet's arrival on a K/V full barrier.** -/
theorem ld_async_arr (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (s : Fin 3) {pc : Nat}
    (he : X.get (h, k) = some ⟨pc, .asyncArrive (obj L h (32 + 8 * s.val)) true⟩) :
    okPolls (obj L h (56 + 8 * s.val)) ((X.tr h).take k) =
        ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) + 1 ∧
      ∃ j pcj sp, j < k ∧ X.get (h, j) = some ⟨pcj, .copy sp⟩ ∧ sp.completion = .asyncGroup ∧
        ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) + 1 ≤
          okPolls (obj L h (56 + 8 * s.val)) ((X.tr h).take j) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .asyncArrive (obj L h (32 + 8 * s.val)) true⟩ : Event).kind ≠ .ub f :=
    fun f h => by cases h
  -- the counts at a loader state
  have hcnt : ∀ {i b d n}, Frame.stateAt (thread p L) X h i =
      some (some (LdWarp.linj p L h b d n)) → n .ub = 0 →
      okPolls (obj L h (56 + 8 * s.val)) ((X.tr h).take i) =
        Loader.ringCnt (n (.load .commit) + Loader.acqOff d.site) s.val ∧
      ((X.tr h).take i).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) =
        Loader.ringCnt (n (.load .commit) - (Loader.inPkt d.site).2) s.val ∧
      ((X.tr h).take i).countP Loader.isCp + 32 * (Loader.inPkt d.site).2 =
        32 * n (.load .commit) + (Loader.inPkt d.site).1 := by
    intro i b d n hσ h0
    refine ⟨?_, ?_, Loader.cp_count hp hX hg hw hσ h0⟩
    · rw [show okPolls (obj L h (56 + 8 * s.val)) ((X.tr h).take i) =
        n (.load (.acquire (obj L h (56 + 8 * s.val)))) from
        count hσ (.load (.acquire (obj L h (56 + 8 * s.val))))]
      exact Loader.acq_ring hp hX hg hw hσ h0 s
    · have h1 := Loader.arr_ring hp hX hg hw hσ h0 s
      refine Eq.trans ?_ h1
      refine Eq.trans ?_ (count hσ (.load (.asyncArrive (obj L h (32 + 8 * s.val)))))
      exact arr_count hp hX hFw hw (32 + 8 * s.val)
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := obj L h (32 + 8 * s.val)) rfl
    cases hc
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, hC⟩ := hJl.refE
  -- the site, and the packet's slot
  obtain ⟨per, vv, hsite, hslot⟩ : ∃ per vv, d.site = .arrive per vv ∧
      Loader.pkOf per vv kk % 3 = s.val := by
    cases ld_use hp hRing hev (l := obj L h (32 + 8 * s.val)) rfl with
    | arrive per vv hs hl hk => exact ⟨per, vv, hs, by have := (obj_off hl).2; omega⟩
    | slot _ _ _ _ _ hk | tw _ _ _ _ hk | dw _ _ _ _ hk | dq _ _ _ hk | ta _ _ _ _ hk
    | da _ _ _ hk | tc _ _ _ _ _ _ hk _ => cases hk
  have hcommit : n (.load .commit) = Loader.pkOf per vv kk + 1 := by
    have h1 := hC.commit
    simp only [hsite, Loader.arrAt, Loader.inPkt] at h1
    exact h1
  obtain ⟨c1, c2, c3⟩ := hcnt hσ h0
  simp only [hsite, Loader.inPkt, Loader.acqOff, hcommit, Nat.add_zero, Nat.add_sub_cancel]
    at c1 c2 c3
  have hone := ringCnt_mod (Loader.pkOf per vv kk) s.val hslot
  refine ⟨by rw [c1, c2, hone], ?_⟩
  -- the packet's last row copy
  obtain ⟨j, ⟨pcj, kd⟩, hj, hjget, hjcp, hjc⟩ := exists_nthEv (X := X) (g := h) (k := k)
    (p := Loader.isCp) (n := 32 * (Loader.pkOf per vv kk + 1) - 1) (by omega)
  cases kd <;> simp [Loader.isCp] at hjcp
  rename_i sp
  have hubj : ∀ f, (⟨pcj, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw hjget hubj with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b', d', n', hσ', h0', hR', -, hev'⟩
  · exact (start_no_copy hev' hi.2).elim
  obtain ⟨a1, a2, -, -⟩ := Loader.copy_site hev' hubj
  have hcpsite : d'.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨sp', hk', hgrp⟩ := a2 hcpsite
  cases hk'
  obtain ⟨e1, -, e3⟩ := hcnt hσ' h0'
  rw [hjc] at e3
  refine ⟨j, pcj, sp, hj, hjget, hgrp, ?_⟩
  rw [e1, c2]
  obtain ⟨per', v', i', c', hs'⟩ : ∃ per' v' i' c', d'.site = .cp per' v' i' c' := by
    revert hcpsite
    cases d'.site <;> simp [Loader.Site.isCp]
  rw [hs'] at e3 ⊢
  simp only [Loader.inPkt, Loader.acqOff] at e3 ⊢
  have hcm : n' (.load .commit) = Loader.pkOf per vv kk := by
    have := i'.isLt
    have := c'.isLt
    omega
  rw [hcm, hone]

/-- A `cp.async` copy. -/
def cpCopy (e : Event) : Bool := match e.kind with | .copy _ => true | _ => false

/-- **A row copy of packet `c`** (the lane's copies `32 c` to `32 c + 31`) follows `c / 3 + 1` polls
of the empty barrier of the packet's slot. -/
theorem ld_copy_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc : Nat} {sp : AsyncCopy.Spec} (he : X.get (h, k) = some ⟨pc, .copy sp⟩) {c : Nat}
    (hc : ((X.tr h).take k).countP cpCopy / 32 = c) :
    okPolls (obj L h (56 + 8 * (c % 3))) ((X.tr h).take k) = c / 3 + 1 := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b, d, n, hσ, h0, -, -, hev⟩
  · exact (start_no_copy hev' hi.2).elim
  obtain ⟨a1, -, -, -⟩ := Loader.copy_site hev hub
  have hcpsite : d.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨per, v, i, j, hs⟩ : ∃ per v i j, d.site = .cp per v i j := by
    revert hcpsite
    cases d.site <;> simp [Loader.Site.isCp]
  have e1 := Loader.cp_count hp hX hg hw hσ h0
  have e2 := Loader.acq_ring hp hX hg hw hσ h0 ⟨c % 3, Nat.mod_lt _ (by decide)⟩
  simp only [Loader.CpCount, hs, Loader.inPkt] at e1
  have hi := i.isLt
  have hj := j.isLt
  have hcc : n (.load .commit) = c := by
    rw [← hc]
    change ((X.tr h).take k).countP Loader.isCp + 32 * 0 = 32 * n (.load .commit) + _ at e1
    change _ = ((X.tr h).take k).countP Loader.isCp / 32
    omega
  rw [show okPolls (obj L h (56 + 8 * (c % 3))) ((X.tr h).take k) =
    n (.load (.acquire (obj L h (56 + 8 * (c % 3))))) from
    count hσ (.load (.acquire (obj L h (56 + 8 * (c % 3)))))]
  refine Eq.trans e2 ?_
  change Loader.ringCnt (n (.load .commit) + Loader.acqOff d.site) (c % 3) = _
  rw [hs, hcc]
  exact ringCnt_self c

end
end PTX.Kernels.TmlFa4Fwd.Proof
