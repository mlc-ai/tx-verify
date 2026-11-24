-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsPkg
public import Kernels.InklingRelDecode.Proof.Protocol.BarAll
public import Kernels.InklingRelDecode.Proof.Interface.FootClass

@[expose] public section

/-!
# The allocation before every Tensor Memory access (`SO.TmemLife.alloc_before`)

Thread 0 of CTA `c` (lane 0 of warp 0) starts at the common start's `alloc`: its first event is
the allocation of 512 columns (`alloc_first`, `DStart.shape_alloc`). An MMA, `tcgen05.ld` or
`tcgen05.st` of a thread `h` of the CTA is fired from a state past the common start, so `h` has
made two barrier-0 events before it (`Bar.bar0_ordinal_two`), among them its arrival of ordinal 0
(`Bar.arrival_before`). Thread 0 has the arrival of that ordinal too (`Bar.bar0_member`), so its
trace goes past the allocation; `Bar.bar0_chain` orders the allocation before the access.

`TmemLifeRest` is what is left of `SO.TmemLife`: `ldst_before_dealloc` and
`dealloc_after_epilogue`, which need the exit generation of barrier 0.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **What is left of `SO.TmemLife`.** -/
structure TmemLifeRest (L : Launch) (X : Execution) : Prop where
  ldst_before_dealloc : ∀ {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
      {grp : CtaGroup} {dst : Option Loc} {da n : Nat},
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ →
      (d.1 / L.block) = (e.1 / L.block) →
      (X.TLd e a vals sh → TcMma.WaitBefore L X .waitLd e d) ∧
      (X.TSt e a vals sh → TcMma.WaitBefore L X .waitSt e d)
  dealloc_after_epilogue : ∀ {d : EvId} {h j : Nat} {pc pc' p : Nat} {grp : CtaGroup}
      {dst : Option Loc} {da n : Nat} {acq : Bool} {sc : MbarScope} {c : Nat},
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ → (h / L.block) = (d.1 / L.block) →
    X.get (h, j) = some ⟨pc', .wait (EvW.oFinal L c) p true acq sc⟩ →
      baseCausality L X (h, j) d

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The first event of thread 0 of a CTA is the allocation.** -/
theorem alloc_first {c : Nat} {e : Event} (he : X.get (c * L.block, 0) = some e) :
    e = ⟨DStart.evPc .alloc, .tc (.resource .one (some ⟨.shared, c, L.sharedBase⟩)
      (.alloc 512))⟩ := by
  have hb : L.block = 256 := hpre.block
  have hg : c * L.block < L.threads := event_thread_lt hX he
  have hσ : St Q L X (c * L.block) 0 = some (some (.d (.dstart ⟨.alloc, b32 0⟩))) := by
    rw [St, Frame.stateAt_zero]
    have h1 : (c * L.block) % L.block < 128 := by rw [hb]; omega
    have h2 : (c * L.block) % L.block < 32 := by rw [hb]; omega
    show some (some (if (c * L.block) % L.block < 128 then TSt.d (DComp.code L (c * L.block) Q).init
      else TSt.w (WComp.code L (c * L.block) Q).init)) = _
    rw [ite_eq_left_iff.mpr (fun h => absurd h1 h)]
    show some (some (TSt.d (.dstart (DStart.D.start L (c * L.block))))) = _
    unfold DStart.D.start
    rw [ite_eq_left_iff.mpr (fun h => absurd h2 h)]
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  have hblk : L.block % 32 = 0 := by rw [hb]
  have h := DStart.shape_alloc hblk (ProA.sharedOk_of_pre hpre) (fired_dstart hF) rfl
  rw [h]
  have hc : c * L.block / L.block = c := by rw [hb]; omega
  rw [hc]

/-- A state at an MMA, a `tcgen05.ld` or a `tcgen05.st` is past the common start. -/
theorem access_late {g k : Nat} {a : Nat} {vals : List Value} {sh : TcShape}
    (hacc : IsMma X (g, k) ∨ X.TLd (g, k) a vals sh ∨ X.TSt (g, k) a vals sh) :
    ∃ s, St Q L X g k = some (some s) ∧ ¬ tLb s < 2 := by
  rcases hacc with hm | ⟨pc, he⟩ | ⟨pc, he⟩
  · obtain ⟨pc, dst, sp, acc, mask, he⟩ := hm.get
    have hg : g < L.threads := event_thread_lt hX he
    obtain ⟨d, P, hσ, -⟩ :=
      mma_event_state hpre hX hf.sound hf.tracked hg he (.inl ⟨_, _, _, _, rfl⟩)
    exact ⟨_, hσ, by simp [tLb, BarOrd.wLb]⟩
  · have hg : g < L.threads := event_thread_lt hX he
    rcases (Lk.tcld_event hpre hX hf hg he).2.2 with ⟨d, hσ, -⟩ | ⟨d, hσ, -⟩
    · exact ⟨_, hσ, by simp [tLb, BarOrd.dLb]⟩
    · exact ⟨_, hσ, by simp [tLb, BarOrd.dLb]⟩
  · have hg : g < L.threads := event_thread_lt hX he
    obtain ⟨d, hσ, -⟩ := Lk.tcst_event hX hf hg he
    exact ⟨_, hσ, by simp [tLb, BarOrd.dLb]⟩

/-- **`SO.TmemLife.alloc_before`.** -/
theorem alloc_before {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (hacc : IsMma X e ∨ X.TLd e a vals sh ∨ X.TSt e a vals sh) :
    ∃ j pc grp dst n, X.get ((e.1 / L.block) * L.block, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block, j) e := by
  have hb : L.block = 256 := hpre.block
  obtain ⟨h, k⟩ := e
  simp only at hacc ⊢
  obtain ⟨ev, hev⟩ : ∃ ev, X.get (h, k) = some ev := by
    rcases hacc with hm | ⟨pc, he⟩ | ⟨pc, he⟩
    · obtain ⟨pc, dst, sp, acc, mask, he⟩ := hm.get
      exact ⟨_, he⟩
    · exact ⟨_, he⟩
    · exact ⟨_, he⟩
  have hh : h < L.threads := event_thread_lt hX hev
  have hk : k < (X.tr h).length := len_of_get hev
  obtain ⟨s, hσ, hl⟩ := access_late hpre hX hf hacc
  have h2 := Bar.bar0_ordinal_two hX hf.sound hk.le hσ hl
  obtain ⟨jf, pcf, hjf, hbf, hcf⟩ :=
    Bar.arrival_before hX hf.sound hf.tracked (h := h) (k := k) (r := 0) (by omega) (by omega)
  set g0 := h / L.block * L.block with hg0
  have hg0c : g0 / L.block = h / L.block := by rw [hg0, hb]; omega
  have hg0t : g0 < L.threads := by
    have : g0 ≤ h := by rw [hg0]; exact Nat.div_mul_le_self _ _
    omega
  obtain ⟨i0, pc0, hb0, -⟩ := Bar.bar0_member hpre hX hf.sound hf.tracked hbf (by omega)
    (by omega) hg0c
  have hb0' : X.get (g0, i0) = some ⟨pc0, .bar 0 none .sync⟩ := hb0
  have hi0 : i0 < (X.tr g0).length := len_of_get hb0'
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g0, 0) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (show 0 < (X.tr g0).length by omega)⟩
  have he0' := alloc_first hpre hX hf (c := h / L.block) he0
  subst he0'
  have hi1 : 1 ≤ i0 := by
    rcases Nat.eq_zero_or_pos i0 with h0 | h0
    · subst h0
      rw [he0] at hb0'
      cases hb0'
    · exact h0
  have hB := Bar.bar0_chain hpre hX hf.sound hf.tracked (g := g0) (h := h) (before := 0)
    (after := k) ⟨hg0t, hh, hg0c⟩ hbf (by omega) (by simp) (by omega)
    (by
      intro ev' hev'
      rw [show (X.tr g0)[0]? = _ from he0] at hev'
      cases hev'
      simp [Execution.isBarId])
    hjf hk
  exact ⟨0, _, _, _, _, he0, by omega, hB⟩

/-- **`SO.TmemLife`** from what is left of it. -/
theorem tmemLife_of (r : TmemLifeRest L X) : SO.TmemLife L X :=
  ⟨fun hacc => alloc_before hpre hX hf hacc, r.ldst_before_dealloc, r.dealloc_after_epilogue⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
