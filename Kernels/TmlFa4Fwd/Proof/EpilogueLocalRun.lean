-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

noncomputable section

theorem epilogueLocalStep {l : Launch} {g : Nat} {s t : TState}
    (hlo : 2768 ≤ s.pc) (hhi : s.pc ≤ 3100) (h : tauStep kernel [] l g s = some t) :
    tauStep kernel Assumptions.all l g s = some t := by
  simpa only [tauStep, epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩ :
    EpiloguePc s.pc)] using h

def LinearInstrFrame (pc : Nat) (F : List Nat) : Prop :=
  ∃ i, kernel.code[pc]? = some i ∧ nextPc i.op pc = pc + 1 ∧
    (∀ q, ¬ BrxTarget i.op q) ∧ writesRegs i.op ⊆ F

/-- Transport a local run whose instructions advance one PC, retaining its register frame.
The last step can branch since its successor does not need to satisfy another step's frame. -/
theorem epilogueLinearRun {l : Launch} {g n : Nat} {t u : TState} {F : List Nat}
    (hlo : 2768 ≤ t.pc) (hhi : t.pc + n ≤ 3101)
    (hCode : ∀ pc, t.pc ≤ pc → pc + 1 < t.pc + n → LinearInstrFrame pc F)
    (hLast : n ≠ 0 → ∃ ins, kernel.code[t.pc + n - 1]? = some ins ∧ writesRegs ins.op ⊆ F)
    (hSub : t.sub = 0) (hAcc : t.acc = [])
    (h : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      (∀ r ∉ F, u.regs r = t.regs r) ∧ u.sub = 0 ∧ u.acc = [] := by
  induction n generalizing t with
  | zero =>
    obtain rfl : t = u := Option.some.inj h
    exact ⟨rfl, fun _ _ => rfl, hSub, hAcc⟩
  | succ n ih =>
    cases ht : tauStep kernel [] l g t with
    | none => simp [run, ht] at h
    | some v =>
      have hs := epilogueLocalStep hlo (by omega) ht
      have hTail : run kernel [] l g n v = some u := by
        simpa only [run, ht, Option.bind_some] using h
      have hTau := tauStep_iff.mp ht
      have same {ins : Instr} (hc : kernel.code[t.pc]? = some ins) :
          v.sub = 0 ∧ v.acc = [] := by
        rcases tau_core_frame hc hTau with rfl | h
        · exact ⟨rfl, rfl⟩
        · exact ⟨h.sub.trans hSub, h.acc.trans hAcc⟩
      cases n with
      | zero =>
        obtain ⟨ins, hc, hF⟩ := hLast (by omega)
        have hPc : t.pc + 1 - 1 = t.pc := by omega
        rw [hPc] at hc
        obtain rfl : v = u := Option.some.inj hTail
        exact ⟨by simp only [run, hs, Option.bind_some], (fun r hr =>
          tau_core_regs hc hTau (fun hm => hr (hF hm))), same hc⟩
      | succ k =>
        obtain ⟨ins, hc, hpc, hb, hF⟩ := hCode t.pc (by omega) (by omega)
        have hv : v.pc = t.pc + 1 := by
          rcases tau_core_frame hc hTau with rfl | hFrame
          · rfl
          · exact hFrame.pc.elim (·.trans hpc) (fun hbr => (hb _ hbr).elim)
        obtain ⟨hr, hFrame, hSub', hAcc'⟩ := ih (t := v) (by omega) (by omega)
          (fun pc h₁ h₂ => hCode pc (by omega) (by omega))
          (fun _ => by simpa only [hv, show t.pc + 1 + (k + 1) = t.pc + (k + 1 + 1) by omega]
            using hLast (by omega)) (same hc).1 (same hc).2 hTail
        exact ⟨by rw [run, hs, Option.bind_some]; exact hr, (fun r hNot =>
          (hFrame r hNot).trans (tau_core_regs hc hTau (fun hm => hNot (hF hm)))),
          hSub', hAcc'⟩

theorem traceHeadOfDrop {X : Execution} {g i : Nat} {e : Event} {es : List Event}
    (hs : (X.tr g).drop i = e :: es) :
    X.get (g, i) = some e ∧ (X.tr g).drop (i + 1) = es := by
  constructor
  · change (X.tr g)[i]? = some e
    rw [show i = i + 0 by omega, ← List.getElem?_drop, hs]
    rfl
  · rw [← List.drop_drop, hs]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
