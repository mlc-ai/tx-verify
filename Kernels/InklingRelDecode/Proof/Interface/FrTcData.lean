-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk4Class
public import Kernels.InklingRelDecode.Proof.Interface.SwTcSt
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiSync

@[expose] public section

/-!
# Which states issue a `tcgen05.ld` or a `tcgen05.st`, with the address and the shape

A `tcgen05.ld` event of a thread comes from one of three states: the softmax region's load of the
S tile (`ldS`, at `Sm.tileAddr`), its load of `O` for the rescale (`ldO`, at `Sm.oAddr`) or the
epilogue's load (`Epi.Site.ld`, at `Prm.taddr`); every one is `.16x32bx2` with 64 registers
(`tcld_event`). A `tcgen05.st` event comes from the softmax region's `P` store (`tmemSt`, 32
registers at `Sm.tileAddr`) or rescale store (`stO`, 64 registers at `Sm.oAddr`; `tcst_event`).
The classification is `Lk.isTcColl_state` (the position is a warp-collective `tcgen05` position)
and the shapes of the sites' events.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A `tcgen05.ld` event** is the softmax region's S load or `O` load or the epilogue's load:
the state before it, its address and its shape. -/
theorem tcld_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc a : Nat} {vals : List Value} {sh : TcShape}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    sh = .s16x32bx2 64 ∧ vals.length = 64 ∧
      ((∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧
        ((d.site = .ldS ∧ a = Sm.tileAddr L g d) ∨ (d.site = .ldO ∧ a = Sm.oAddr L g d))) ∨
      ∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .ld ∧
        a = d.pr.taddr) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he (fun pc f h => by cases h)
  have hσ' : St Q L X g k = some (some s) := hσ
  have hs : tcSt s = true := by
    rw [← isTcColl_state hpre hX hf hg he hσ']
    rfl
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ' (tc_not_exit hs)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hb2 : L.block = 256 := hpre.block
  have hSh := ProA.sharedOk_of_pre hpre
  cases s with
  | w s => simp [tcSt] at hs
  | d s =>
    cases s with
    | pro d => simp [tcSt, Lk.dTc] at hs
    | dstart d =>
      have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
      obtain ⟨site, tm⟩ := d
      simp only [tcSt, Lk.dTc, decide_eq_true_eq] at hs
      rcases hs with h | h <;> (simp only [DStart.Shape, h] at hshape; simp at hshape)
    | sm d =>
      have hshape := Sm.shape hb2 hSh (fired_sm hF)
      have hshapeO := Sm.shapeO (fired_sm hF)
      have hw := fun h => Sm.shape_waitLdO hb (fired_sm hF) h
      simp only [tcSt, Lk.dTc, decide_eq_true_eq] at hs
      unfold Sm.Shape at hshape
      unfold Sm.ShapeO at hshapeO
      rcases hs with h | h | h | h | h | h | h | h <;> rw [h] at hshape hshapeO
      · obtain ⟨vals', hl, he'⟩ := hshape
        simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at he'
        obtain ⟨-, rfl, rfl, rfl⟩ := he'
        exact ⟨rfl, hl, Or.inl ⟨d, hσ', Or.inl ⟨h, rfl⟩⟩⟩
      · simp at hshape
      · obtain ⟨vals', -, -, -, he'⟩ := hshape
        simp at he'
      · simp at hshape
      · obtain ⟨vals', hl, he'⟩ := hshapeO
        simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at he'
        obtain ⟨-, rfl, rfl, rfl⟩ := he'
        exact ⟨rfl, hl, Or.inl ⟨d, hσ', Or.inr ⟨h, rfl⟩⟩⟩
      · have := hw h
        simp at this
      · obtain ⟨vals', -, -, -, he'⟩ := hshapeO
        simp at he'
      · simp at hshape
    | epi d =>
      have hshape := Epi.shape hb (fired_epi hF)
      simp only [tcSt, Lk.dTc, decide_eq_true_eq] at hs
      unfold Epi.Shape at hshape
      rcases hs with h | h | h <;> rw [h] at hshape
      · obtain ⟨vals', hl, he'⟩ := hshape
        simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at he'
        obtain ⟨-, rfl, rfl, rfl⟩ := he'
        exact ⟨rfl, hl, Or.inr ⟨d, hσ', h, rfl⟩⟩
      · simp at hshape
      · simp at hshape

/-- **A `tcgen05.st` event** is the softmax region's `P` store or rescale store: the state before
it, its address, its shape and its number of registers. -/
theorem tcst_event (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc a : Nat} {vals : List Value} {sh : TcShape}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.st a vals sh)⟩) :
    ∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧
      ((d.site = .tmemSt ∧ a = Sm.tileAddr L g d ∧ sh = .s16x32bx2 32 ∧ vals.length = 32) ∨
      (d.site = .stO ∧ a = Sm.oAddr L g d ∧ sh = .s16x32bx2 64 ∧ vals.length = 64)) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he (fun pc f h => by cases h)
  have hσ' : St Q L X g k = some (some s) := hσ
  obtain ⟨d, rfl, hsite⟩ := tcst_event_state hf.sound hX he hσ'
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ' (by simp [ExitState])
  refine ⟨d, hσ', ?_⟩
  rcases hsite with h | h
  · obtain ⟨vals', hl, -, -, he'⟩ := Sm.shape_tmemSt (fired_sm hF) h
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at he'
    obtain ⟨-, rfl, rfl, rfl⟩ := he'
    exact Or.inl ⟨h, rfl, rfl, hl⟩
  · obtain ⟨vals', hl, -, -, he'⟩ := Sm.shape_stO (fired_sm hF) h
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at he'
    obtain ⟨-, rfl, rfl, rfl⟩ := he'
    exact Or.inr ⟨h, rfl, rfl, hl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
