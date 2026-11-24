-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueElectProgress
public import Kernels.TmlFa4Fwd.Proof.PrologueInitChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Every earlier event has an instruction address below the current site. -/
def EarlierEvents (X : Execution) (g n pc : Nat) : Prop :=
  ∀ k < n, ∀ e, X.get (g, k) = some e → e.pc < pc

theorem EarlierEvents.mono {X : Execution} {g n pc dst : Nat} (h : EarlierEvents X g n pc)
    (hle : pc ≤ dst) : EarlierEvents X g n dst :=
  fun k hk e he => (h k hk e he).trans_le hle

theorem EarlierEvents.succ {X : Execution} {g n pc : Nat} {e : Event}
    (h : EarlierEvents X g n pc) (he : X.get (g, n) = some e) (hp : e.pc = pc) :
    EarlierEvents X g (n + 1) (pc + 1) := by
  intro k hk q hq
  by_cases hh : k = n
  · subst k
    rw [he, Option.some.injEq] at hq
    rw [← hq, hp]
    omega
  · have hn := h k (by omega) q hq
    omega

theorem releasedIfLast {l : Launch} {X : Execution} {g n : Nat} {e : Event}
    (he : X.get (g, n) = some e) (hf : e.kind.resume ≠ .blocking false)
    (h : n + 1 = (X.tr g).length) : Step.Released l X g := by
  apply Step.Released.of_get
  intro e' he'
  rw [← h, Nat.add_sub_cancel, he, Option.some.injEq] at he'
  rwa [← he']

/-- A proof that a decoded initializer is available at the current recorded cursor. -/
def InitIssuerOn (l : Launch) (X : Execution) (g : Nat) (Available : Nat → Prop)
    (Site : Fin 34 → Prop) : Prop :=
  ∀ (i : Fin 34) {n : Nat} {t : TState}, Site i → 0 < n → InitCursor l X g n t →
      Available (n + 1) → EarlierEvents X g n t.pc →
      (n = (X.tr g).length → Step.Released l X g) →
      t.pc = (initSite i).pc → t.fault = none →
      t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)) →
      t.regs (initSite i).countReg = some (b32 (initSite i).count) →
      X.get (g, n) = some (initEvent l g i) ∧ InitCursor l X g (n + 1) (next t)

/-- The unrestricted issuer used by the full prologue. -/
def InitIssuer (l : Launch) (X : Execution) (g : Nat) (Available : Nat → Prop) : Prop :=
  ∀ (i : Fin 34) {n : Nat} {t : TState}, 0 < n → InitCursor l X g n t →
      Available (n + 1) → EarlierEvents X g n t.pc →
      (n = (X.tr g).length → Step.Released l X g) →
      t.pc = (initSite i).pc → t.fault = none →
      t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)) →
      t.regs (initSite i).countReg = some (b32 (initSite i).count) →
      X.get (g, n) = some (initEvent l g i) ∧ InitCursor l X g (n + 1) (next t)

/-- Consume a decoded run of initializers and retain their exact event positions. -/
theorem initRecordsUsingOn {l : Launch} {X : Execution} {g : Nat} {Available : Nat → Prop}
    {Site : Fin 34 → Prop} (issuer : InitIssuerOn l X g Available Site) :
    ∀ (is : List (Fin 34)) (n : Nat) (t : TState), (∀ i ∈ is, Site i) → 0 < n →
      InitCursor l X g n t → EarlierEvents X g n t.pc →
      (n = (X.tr g).length → Step.Released l X g) → t.fault = none →
      (∀ k ≤ n + is.length, Available k) →
      (∀ k i, is[k]? = some i → (initSite i).pc = t.pc + k) →
      (∀ i ∈ is, t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)) ∧
        t.regs (initSite i).countReg = some (b32 (initSite i).count)) →
      let u := { t with pc := t.pc + is.length }
      InitCursor l X g (n + is.length) u ∧ EarlierEvents X g (n + is.length) u.pc ∧
      (n + is.length = (X.tr g).length → Step.Released l X g) ∧
      ∀ k i, is[k]? = some i → X.get (g, n + k) = some (initEvent l g i)
  | [], n, t, _, _, hCur, hPrev, hReady, _, _, _, _ => by
    simpa using (show InitCursor l X g n t ∧ EarlierEvents X g n t.pc ∧
      (n = (X.tr g).length → Step.Released l X g) ∧
      (∀ k i, ([] : List (Fin 34))[k]? = some i → X.get (g, n + k) = some (initEvent l g i)) from
      ⟨hCur, hPrev, hReady, by simp⟩)
  | i :: is, n, t, hAllowed, hn, hCur, hPrev, hReady, hf, hAvailable, hSite, hRegs => by
    have hPc : t.pc = (initSite i).pc := by simpa using (hSite 0 i rfl).symm
    obtain ⟨hAddr, hCount⟩ := hRegs i (by simp)
    have hFirst : Available (n + 1) := hAvailable _ (by simp only [List.length_cons]; omega)
    obtain ⟨he, hNext⟩ := issuer i (hAllowed i List.mem_cons_self) hn hCur hFirst hPrev hReady
      hPc hf hAddr hCount
    have hp' : (initEvent l g i).pc = t.pc := hPc.symm
    have hAfter : EarlierEvents X g (n + 1) (next t).pc := hPrev.succ he hp'
    have hReady' := releasedIfLast (l := l) he (by
      intro h
      cases h)
    have hSite' (k : Nat) (i' : Fin 34) (hh : is[k]? = some i') :
        (initSite i').pc = (next t).pc + k := by
      have hh' := hSite (k + 1) i' hh
      change (initSite i').pc = t.pc + 1 + k
      omega
    obtain ⟨hu, hEarlier, hReleased, hGet⟩ :=
      initRecordsUsingOn issuer is (n + 1) (next t)
        (fun i' hi' => hAllowed i' (List.mem_cons_of_mem _ hi')) (by omega) hNext hAfter hReady' hf
        (fun k hk => hAvailable k (by simp at *; omega)) hSite'
        (fun i' hi' => hRegs i' (by simp [hi']))
    have hIndex : n + 1 + is.length = n + (i :: is).length := by simp; omega
    have hState : { next t with pc := (next t).pc + is.length } =
        { t with pc := t.pc + (i :: is).length } := by
      have h' : (next t).pc + is.length = t.pc + (i :: is).length := by
        simp only [next, List.length_cons]
        omega
      rw [← h']
      rfl
    rw [hIndex, hState] at hu hEarlier
    rw [hIndex] at hReleased
    refine ⟨hu, hEarlier, hReleased, ?_⟩
    rintro (_ | k) i' hi'
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
      simpa only [Nat.add_zero, ← hi'] using he
    · have hk := hGet k i' hi'
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using hk

end
end PTX.Kernels.TmlFa4Fwd.Prologue
