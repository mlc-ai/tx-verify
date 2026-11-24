-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.CountFact
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The row copies before a packet's arrival

A loader lane's arrive-on of slot `s` with `a` earlier ones is packet `3 a + s`'s, after the 32 row
copies of every packet up to it (`ld_arr_copies`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem ringCnt_eq {n s : Nat} (hs : s < 3) : Loader.ringCnt n s = (n + 2 - s) / 3 := by
  induction n with
  | zero => simp [Loader.ringCnt]; omega
  | succ n ih => rw [Loader.ringCnt_succ, ih]; split <;> omega

/-- **The row copies before a packet's arrival.** -/
theorem ld_arr_copies (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (s : Fin 3) {pc a : Nat}
    (he : X.get (h, k) = some ⟨pc, .asyncArrive (obj L h (32 + 8 * s.val)) true⟩)
    (ha : ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) = a) :
    ((X.tr h).take k).countP cpCopy = 32 * (3 * a + s.val + 1) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .asyncArrive (obj L h (32 + 8 * s.val)) true⟩ : Event).kind ≠ .ub f :=
    fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := obj L h (32 + 8 * s.val)) rfl
    cases hc
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, hC⟩ := hJl.refE
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
  have hcp := Loader.cp_count hp hX hg hw hσ h0
  have harr := Loader.arr_ring hp hX hg hw hσ h0 s
  have hcnt : ((X.tr h).take k).countP (MbarRing.arriveOnTo (obj L h (32 + 8 * s.val))) =
      n (.load (.asyncArrive (obj L h (32 + 8 * s.val)))) :=
    (arr_count hp hX hFw hw (32 + 8 * s.val)).trans
      (count hσ (.load (.asyncArrive (obj L h (32 + 8 * s.val)))))
  simp only [hsite, Loader.inPkt, LdWarp.lcn] at hcp harr
  have e : n (.load (.asyncArrive (obj L h (32 + 8 * s.val)))) =
      Loader.ringCnt (n (.load .commit) - 1) s.val := harr
  rw [hcnt, e, hcommit, Nat.add_sub_cancel, ringCnt_eq s.isLt] at ha
  simp only [Loader.CpCount, hsite, Loader.inPkt, LdWarp.lcn] at hcp
  have e2 : ((X.tr h).take k).countP cpCopy + 32 * 1 = 32 * n (.load .commit) + 32 := hcp
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
