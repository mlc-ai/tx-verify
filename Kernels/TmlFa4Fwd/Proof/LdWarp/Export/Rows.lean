-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Lemmas.Protocol.NoIncRing
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

/-! # The row copies of a published packet

`ld_arr_rows`: a loader lane's arrive-on for the use `u` of K/V slot `s` follows its 32 row copies
of packet `3 u + s`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem ringCnt_div' (c : Nat) : Loader.ringCnt c (c % 3) = c / 3 := by
  have h : ∀ n s, s < 3 → Loader.ringCnt n s = (n + 2 - s) / 3 := by
    intro n s hs
    induction n with
    | zero => simp [Loader.ringCnt]; omega
    | succ n ih => rw [Loader.ringCnt_succ, ih]; split <;> omega
  rw [h _ _ (Nat.mod_lt _ (by decide))]
  omega

/-- **A published packet's row copies.** -/
theorem ld_arr_rows (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (s : Fin 3) {pc u : Nat}
    (he : X.get (h, k) = some ⟨pc, .asyncArrive (obj L h (32 + 8 * s.val)) true⟩)
    (hu : ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) = u) {x : Nat}
    (hx : x < 32) : ∃ j pcj sp, j < k ∧ X.get (h, j) = some ⟨pcj, .copy sp⟩ ∧
      ((X.tr h).take j).countP cpCopy = 32 * (3 * u + s.val) + x := by
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
  have hdiv : u = Loader.pkOf per vv kk / 3 := by
    rw [← hu, c2, ← hslot, ringCnt_div']
  have hs3 := s.isLt
  have hcpc : ∀ l : List Event, l.countP Loader.isCp = l.countP cpCopy := fun l =>
    List.countP_congr fun e _ => Iff.rfl
  rw [hcpc] at c3
  obtain ⟨j, ⟨pcj, kd⟩, hj, hjget, hjcp, hjc⟩ := exists_nthEv (X := X) (g := h) (k := k)
    (p := cpCopy) (n := 32 * (3 * u + s.val) + x) (by omega)
  cases kd <;> simp [cpCopy] at hjcp
  exact ⟨j, pcj, _, hj, hjget, hjc⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
