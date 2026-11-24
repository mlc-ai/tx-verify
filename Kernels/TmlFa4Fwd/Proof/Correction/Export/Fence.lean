-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.FstPoll
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.ProxyFence
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Lib.ProxyFence
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative

@[expose] public section

/-! # The proxy fence between the final O stores and the ready arrival

A correction lane's arrival on the ready barrier of stage `st` is the second event after its
`fence.proxy.async.shared::cta`, so every final store of the stage is before the fence
(`corr_fst_fence`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (nexts)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem pred_tab : ∀ st : Fin 2, (∀ s ∈ Correction.allSites,
    (Correction.Site.fdone st 1 ∈ nexts s → s = .fdone st 0) ∧
    (Correction.Site.fdone st 0 ∈ nexts s → s = .fence st)) := by
  decide +kernel

private theorem arr_tab : ∀ st : Fin 2, ∀ s ∈ Correction.allSites,
    Correction.arrOff s = 208 + 8 * st.val → s = .fdone st 1 := by
  decide +kernel

/-- **The state before a ready arrival's site** of the correction role. -/
private theorem corr_pred (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {d : Correction.Control.D} {n : Cls → Nat} {e : Event} (he : X.get (h, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread p L) X h (k + 1) = some (some (CorrWarp.cinj p L h d n)))
    (hs : d.site ≠ .setmax) :
    ∃ d0 n0, Frame.stateAt (thread p L) X h k = some (some (CorrWarp.cinj p L h d0 n0)) ∧
      Correction.Control.Represents p L h d0 d e ∧
      Correction.Control.Ev p L h d0 e ∧ n0 .ub = 0 := by
  have hst := Frame.stateAt_succ (C := thread p L) (show (X.tr h)[k]? = some e from he)
  rw [hσ] at hst
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with
    ⟨s, n1, hσ0, -, -, hi, hev⟩ | ⟨d0, n0, hσ0, h0, hR, hi, hev1, hevR⟩
  · exfalso
    rw [hσ0] at hst
    obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L h) hst.symm
    simp only [glued, Code.glue] at h1
    rcases hn : Startup.succ L h s e with _ | _ | s' <;> rw [hn] at h1 <;>
      simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at h1
    unfold Code.enter at h1
    split at h1
    · rename_i i _
      simp only [Sum.inr.injEq, Sigma.mk.injEq] at h1
      obtain ⟨rfl, hh⟩ := h1
      exact hs (by rw [← eq_of_heq hh])
    · cases h1
  · rw [hσ0] at hst
    have h' : (thread p L h).next (CorrWarp.cinj p L h d0 n0) e =
        some (some (CorrWarp.cinj p L h d n)) := hst.symm
    rw [CorrWarp.next_cinj] at h'
    obtain ⟨o, ho1, ho⟩ := Option.map_eq_some_iff.mp h'
    cases o with
    | none => cases ho
    | some x =>
      simp only [Option.map_some, Option.some.injEq, CorrWarp.cinj, Prod.mk.injEq, Sum.inr.injEq,
        Sigma.mk.injEq, heq_eq_eq, true_and] at ho
      obtain ⟨rfl, -⟩ := ho
      exact ⟨d0, n0, hσ0, Correction.Control.represents (hR h0).1.counts hev1 hub ho1, hev1, h0⟩

/-- **The fence before a ready arrival**: every final store of the stage is before it. -/
theorem corr_fst_fence (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    (st : Fin 2) {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h (208 + 8 * st.val)) tx c rel sc⟩) :
    ∃ kf < k, (∃ pcf, X.get (h, kf) =
        some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩) ∧
      ∀ {i pci : Nat} {a : Acc} {bs : List Byte}, X.get (h, i) = some ⟨pci, .wr a bs⟩ →
        arrivals (obj L h (208 + 8 * st.val)) ((X.tr h).take i) = 0 → i < kf := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev1, -⟩
  · obtain ⟨c', hc'⟩ := start_mbar hev hi.2 (l := obj L h (208 + 8 * st.val)) rfl
    cases hc'
  -- the arrival's site
  have hs : d.site = .fdone st 1 := by
    rcases corr_mbar2 (hev1.data_or_vote.resolve_right (by rintro ⟨_,_,hh⟩; cases hh))
      (l := obj L h (208 + 8 * st.val)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
    · exact arr_tab st _ (Correction.mem_allSites _) (obj_inj hl).symm
    · cases hk
  have hlen : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hne0 : ∀ {k' : Nat} {d' : Correction.Control.D} {n' : Cls → Nat},
      Frame.stateAt (thread p L) X h k' = some (some (CorrWarp.cinj p L h d' n')) →
        ∃ j, k' = j + 1 := by
    intro k' d' n' hσ'
    cases k' with
    | zero => rw [Frame.stateAt_zero] at hσ'; cases hσ'
    | succ j => exact ⟨j, rfl⟩
  have noub : ∀ {j : Nat} {e : Event}, j < k → X.get (h, j) = some e → ∀ f, e.kind ≠ .ub f := by
    rintro j ⟨pcj, kd⟩ hj hej f hf
    simp only at hf
    subst hf
    have hc := count hσ .ub
    rw [h0, List.countP_eq_zero] at hc
    have hmem : (⟨pcj, .ub f⟩ : Event) ∈ (X.tr h).take k := by
      have : ((X.tr h).take k)[j]? = some ⟨pcj, .ub f⟩ := by
        rw [List.getElem?_take, ite_eq_left hj]; exact hej
      exact List.mem_of_getElem? this
    exact hc _ hmem (by simp [Proof.cls])
  -- one step back: the P arrival
  obtain ⟨k1, rfl⟩ := hne0 hσ
  obtain ⟨e1, he1⟩ : ∃ e, X.get (h, k1) = some e :=
    ⟨_, List.getElem?_eq_getElem (show k1 < (X.tr h).length by omega)⟩
  obtain ⟨d1, n1, hσ1, hn1, hev1', -⟩ := corr_pred hp hX hFw hw hw1 he1
    (noub (by omega) he1) hσ (by rw [hs]; simp)
  have back : ∀ {d0 d' : Correction.Control.D} {e : Event} {st' : Fin 2} {j : Fin 2},
      Correction.Control.Represents p L h d0 d' e → d'.site = .fdone st' j →
      Correction.Control.Ev p L h d0 e → d'.site ∈ nexts d0.site := by
    intro d0 d' e st' j hn hs' hevd
    obtain ⟨a,ev,hEv,_,hstep,ha,_⟩ := hn
    have hsa := ha.trans hs'
    rcases Correction.succ_cases hstep with ⟨hd, _, _, _, _, hwt⟩ | ⟨hf, -, hk⟩ | hM
    · have hd0 : d0.scheduler.site = .fdone st' j := hd ▸ hsa
      simp only [Correction.Ev, hd0] at hEv
      rw [hEv] at hwt
      cases hwt
    · rw [hk] at hsa
      rw [hsa] at hf
      cases hf
    · exact ha ▸ hM.1
  have hs1 : d1.site = .fdone st 0 := by
    have hm := back hn1 hs hev1'
    rw [hs] at hm
    exact (pred_tab st _ (Correction.mem_allSites _)).1 hm
  obtain ⟨k2, rfl⟩ := hne0 hσ1
  obtain ⟨e2, he2⟩ : ∃ e, X.get (h, k2) = some e :=
    ⟨_, List.getElem?_eq_getElem (show k2 < (X.tr h).length by omega)⟩
  obtain ⟨d2, n2, hσ2, hn2, hev2, -⟩ := corr_pred hp hX hFw hw hw1 he2
    (noub (by omega) he2) hσ1 (by rw [hs1]; simp)
  have hs2 : d2.site = .fence st := by
    have hm := back hn2 hs1 hev2
    rw [hs1] at hm
    exact (pred_tab st _ (Correction.mem_allSites _)).2 hm
  obtain ⟨pc2, kd2⟩ := e2
  simp only [Correction.Control.Ev, Correction.Control.D.scheduler, Correction.Ev, hs2] at hev2
  obtain ⟨f, fsc, rfl⟩ := hev2
  obtain ⟨rfl, rfl⟩ := proxy_fence hX he2
  refine ⟨k2, by omega, ⟨pc2, he2⟩, fun {i pci a bs} hi hz => ?_⟩
  obtain ⟨pc1, kd1⟩ := e1
  simp only [Correction.Control.Ev, Correction.Control.D.scheduler, Correction.Ev, hs1] at hev1'
  subst hev1'
  by_contra hge
  have h3 : i ≠ k2 := by rintro rfl; rw [he2] at hi; cases hi
  have h4 : i ≠ k2 + 1 := by rintro rfl; rw [he1] at hi; cases hi
  have h5 : i ≠ k2 + 1 + 1 := by rintro rfl; rw [he] at hi; cases hi
  have h6 : arrivals (obj L h (208 + 8 * st.val)) ((X.tr h).take (k2 + 1 + 1 + 1)) ≤
      arrivals (obj L h (208 + 8 * st.val)) ((X.tr h).take i) :=
    (List.take_sublist_take_left (by omega)).countP_le
  have h7 : 1 ≤ arrivals (obj L h (208 + 8 * st.val)) ((X.tr h).take (k2 + 1 + 1 + 1)) := by
    unfold arrivals
    rw [List.take_add_one, show (X.tr h)[k2 + 1 + 1]? = _ from he, Option.toList_some,
      List.countP_append]
    simp [arrivesOn, sourceArrive]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
