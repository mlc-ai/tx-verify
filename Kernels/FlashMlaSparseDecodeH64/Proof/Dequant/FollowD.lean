-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataState
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.TraceOk
import Lemmas.Flow.RoleStep
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The data thread machine follows a dequantizer lane on valid data

`followD`: on valid data (`DqValid`) the data thread machine (`threadD`) follows lane `g` of warps
8-11 up to its event `k`, with the invariant that its words are the trace's last loads
(`Dequant.Data.InvD`): by induction from `Follow`, the control state at each prefix is the erased
data state (`control_of_data`), and the data step exists by `dataNext_ok`. `deq_slot`: a followed
state of such a lane is the startup's or warpgroup 2's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Dequant
open Dequant.Data

theorem mem_take_get {f : Event} {j : Nat} (h : f ∈ (X.tr g).take j) :
    ∃ j' < j, X.get (g, j') = some f := by
  obtain ⟨i, hi, hf⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at hf
  rw [List.length_take] at hi
  exact ⟨i, by omega, by rw [← hf]; exact List.getElem?_eq_getElem _⟩

/-- A state of a lane of warps 8–11: the startup's or warpgroup 2's. -/
theorem deq_slot (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (hg : g < L.threads) {i : Nat} {s : (threadD P L g).D}
    (hs : Frame.stateAt (threadD P L) X g i = some (some s)) :
    (∃ b, s.1 = .inl b) ∨ ∃ d, s.1 = .inr ⟨.inl .dequant, d⟩ := by
  have hJ := (follow_iff.mp hFw g hg i).2 _ (control_of_data hs)
  obtain ⟨q, n⟩ := s
  rcases q with b | ⟨e | r, d⟩
  · exact .inl ⟨b, rfl⟩
  · cases e with
    | dequant => exact .inr ⟨d, rfl⟩
    | wg0 | wg1 =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warp] at hw
      omega
  · exact hJ.elim

theorem startup_site_pc_le (site : Startup.Site) : site.pc ≤ 2606 := by
  cases site with
  | sh j => fin_cases j <;> decide
  | elect j => fin_cases j <;> decide
  | init n => exact (by decide : ∀ n : Fin 23, Startup.initPc n ≤ 2606) n
  | enter r => cases r <;> decide
  | _ => decide

theorem startup_pc_le (b : Startup.D) : b.site.pc ≤ 2606 := startup_site_pc_le b.site

theorem atPc_nil {l : List Event} {p : Nat} (h : ∀ x ∈ l, x.pc ≠ p) : atPc l p = [] := by
  unfold atPc
  exact List.filter_eq_nil_iff.mpr fun x hx => by simpa using h x hx

/-- A role entered from the startup starts at its first state. -/
theorem invD_enter {b : Startup.D} {d : D} {l : List Event} (hl : ∀ x ∈ l, x.pc ≤ 2606)
    (h : Code.enter (startupCode P L g) (Code.withStubs (fragD P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) b = .inr ⟨.inl .dequant, d⟩) :
    InvD l d := by
  unfold Code.enter at h
  split at h
  · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases eq_of_heq h
    refine ⟨fun r h => Site.noConfusion h, fun r h => by simp [InRow] at h,
      fun r i h => by simp [Done] at h, fun r => ?_, fun r h => Site.noConfusion h,
      fun r h => by simp [InRow] at h, fun r i h => by simp [Done] at h⟩
    rw [atPc_nil (fun x hx => by have := hl x hx; unfold dqScalePc; omega)]
    simp
  · cases h

/-- **On valid data the data thread machine follows the lane** up to its event `k`, with the
invariant. -/
theorem followD (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσk : ∃ σk, Frame.stateAt (thread P L) X g k = some (some σk)) (hv : DqValid X g k) :
    ∀ j ≤ k, ∃ s, Frame.stateAt (threadD P L) X g j = some (some s) ∧
      (∀ d, s.1 = .inr ⟨.inl .dequant, d⟩ → InvD ((X.tr g).take j) d) ∧
      ∀ b, s.1 = .inl b → ∀ x ∈ (X.tr g).take j, x.pc ≤ 2606 := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σk, hσk⟩ := hσk
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  intro j hj
  induction j with
  | zero =>
    refine ⟨_, Frame.stateAt_zero, fun d hd => invD_enter (b := (startupCode P L g).init)
      (by simp) hd, fun b _ x hx => by simp at hx⟩
  | succ j ih =>
    obtain ⟨s, hs, hI, hSt⟩ := ih (by omega)
    have hf : X.get (g, j) = some ((X.tr g)[j]'(by omega)) := List.getElem?_eq_getElem _
    generalize (X.tr g)[j]'(by omega) = f at hf
    have hfu : ∀ fl, f.kind ≠ .ub fl := fun fl h => by
      obtain ⟨pc, kd⟩ := f
      cases h
      have := ub_last hX hf he
      omega
    have hσ := control_of_data hs
    have hc1 : Frame.stateAt (thread P L) X g (j + 1) =
        (thread P L g).next (eraseThread P L g s) f := by
      rw [Frame.stateAt_succ hf, hσ]; rfl
    obtain ⟨σ', hσ'⟩ : ∃ σ', (thread P L g).next (eraseThread P L g s) f = some (some σ') := by
      rcases h : (thread P L g).next (eraseThread P L g s) f with _ | _ | σ'
      · rw [Frame.stateAt_none_mono (hc1.trans h) (show j + 1 ≤ k by omega)] at hσk
        cases hσk
      · exact absurd (hc1.trans h) (follow_iff.mp hFw g hg (j + 1)).1
      · exact ⟨σ', rfl⟩
    have hpc := Frame.event_pcU hsD hX hf hs hfu
    obtain ⟨-, -, -, -, hinv, -, -⟩ := Frame.fired_siteU hsD hX hf hs hfu
    have hgood : ∀ f' ∈ (X.tr g).take j ++ [f], GoodEv f' := by
      intro f' hf'
      rcases List.mem_append.mp hf' with h | h
      · obtain ⟨j', hj', hg'⟩ := mem_take_get h
        exact hv j' (by omega) f' hg'
      · obtain rfl := List.mem_singleton.mp h
        exact hv j (by omega) f' hf
    have htake : (X.tr g).take (j + 1) = (X.tr g).take j ++ [f] := by
      have hf' : (X.tr g)[j]? = some f := hf
      rw [List.take_add_one, hf']; rfl
    rw [Frame.stateAt_succ hf, hs, htake]
    obtain ⟨q, n⟩ := s
    rcases deq_slot hFw hw hg hs with ⟨b, hb⟩ | ⟨d, hd⟩
    · obtain rfl : q = .inl b := hb
      obtain ⟨s', hs'⟩ := Code.roleThread_next_start_of (R' := fragD P L g) (n' := n) hσ'
      have hle : f.pc ≤ 2606 := hpc.trans_le (startup_pc_le b)
      have hall : ∀ x ∈ (X.tr g).take j ++ [f], x.pc ≤ 2606 := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hSt b rfl x hx
        · rw [List.mem_singleton.mp hx]; exact hle
      obtain ⟨b', -, hb'⟩ := Code.roleThread_next_start hs'
      exact ⟨s', hs', fun d' hd' => invD_enter hall (hb'.symm.trans hd'),
        fun _ _ => hall⟩
    · obtain rfl : q = .inr ⟨.inl .dequant, d⟩ := hd
      obtain ⟨c', hc, -⟩ := Code.roleThread_next_role hσ'
      obtain ⟨d', hd'⟩ := dataNext_ok (hI d rfl) hinv hpc hc hgood
      have hn : (fragD P L g .dequant).next d f = some (some d') := by
        change Data.succ P L g d f = _
        simp only [Data.succ, show Control.succ P L g d.c f = some (some c') from hc, hd']
      obtain ⟨s', hs'⟩ : ∃ s', (threadD P L g).next (.inr ⟨.inl .dequant, d⟩, n) f =
          some (some s') := Code.roleThread_next_of_role hn
      obtain ⟨d'', hn', hs''⟩ := Code.roleThread_next_role hs'
      refine ⟨s', hs', fun d₁ hd₁ => ?_, fun b₁ hb₁ => by rw [hs''] at hb₁; cases hb₁⟩
      rw [hs''] at hd₁
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hd₁
      subst hd₁
      obtain ⟨c'', hc'', hdn⟩ := next_ctl hn'
      exact invD_step (hI d rfl) hinv hpc hc'' hdn

end Dequant

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
