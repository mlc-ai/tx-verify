-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEventProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

def scratchMemory (a : MemAccess) : Bool :=
  (a.kind == .load && !a.nc && (a.ext == .same || a.space == some .local) ||
    a.kind == .store && a.space == some .local) &&
  a.rule == some .threadAccess

private theorem scratchLoadKeeps {s : TState} {r w : Nat} {ds : List Nat} {ext : MemExt}
    (bs : List (Option Byte)) (hr : r ∉ ds) :
    (afterAccessLoad s ext w ds bs).regs r = s.regs r := by
  unfold afterAccessLoad
  split
  · rfl
  · split
    · rfl
    · exact setRegs_other _ _ _ _ hr

/-- Each scratch memory event uses the ordinary load or store continuation. -/
theorem scratchMemoryContinuation {l : Launch} {g : Nat} {s u : TState}
    {a : MemAccess} {e : Event} (hm : scratchMemory a = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    (a.kind = .load ∧ ∃ bs, u = afterAccessLoad s a.ext a.elem.width a.regs bs) ∨
      a.kind = .store ∧ u = afterStore s a.srcs := by
  have haveRule : a.rule = some .threadAccess := by
    simpa [scratchMemory] using (Bool.and_eq_true_iff.mp hm).2
  have hCases : (a.kind = .load ∧ a.nc = false ∧ (a.ext = .same ∨ a.space = some .local)) ∨
      (a.kind = .store ∧ a.space = some .local) := by
    simpa [scratchMemory, and_assoc] using (Bool.and_eq_true_iff.mp hm).1
  rcases hCases with ⟨hKind, hNc, hSame | hLocal⟩ | ⟨hKind, hLocal⟩
  · obtain ⟨_, bs, _, rfl⟩ := fires_load hKind hNc hf hSame
    exact .inl ⟨hKind, bs, by rw [hSame, afterAccessLoad_same]⟩
  · have hNoDirect : a.locSpace? = none := by simp [MemAccess.locSpace?, hLocal]
    simp only [eventTmpl, memTmpl, haveRule, hNoDirect] at hf
    simp at hf
    rcases accessTmpl_load (A := Assumptions.all) (L := l) (g := g) (t := s) hKind with
      ⟨_, ht⟩ | ⟨_, _, _, ht⟩ | ⟨_, _, hNc', _⟩
    · rw [ht] at hf
      cases hf.2
    · rw [ht] at hf
      obtain ⟨bs, _, _, hu⟩ := hf
      exact .inl ⟨hKind, bs, Option.some.inj hu⟩
    · cases hNc.symm.trans hNc'
  · have hNoDirect : a.locSpace? = none := by simp [MemAccess.locSpace?, hLocal]
    simp only [eventTmpl, memTmpl, haveRule, hNoDirect] at hf
    simp at hf
    rcases accessTmpl_store (A := Assumptions.all) (L := l) (g := g) (t := s) hKind with
      ⟨_, ht⟩ | ⟨_, _, _, ht⟩
    · rw [ht] at hf
      cases hf.2
    · rw [ht] at hf
      exact .inr ⟨hKind, Option.some.inj hf.2⟩

/-- Scratch-loop memory events preserve every register outside the decoded load destinations. -/
theorem scratchMemoryFrame {l : Launch} {g r : Nat} {s u : TState}
    {a : MemAccess} {e : Event} (hm : scratchMemory a = true) (hr : r ∉ a.regs)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    u.regs r = s.regs r := by
  rcases scratchMemoryContinuation hm hf with ⟨_, bs, rfl⟩ | ⟨_, rfl⟩
  · exact scratchLoadKeeps bs hr
  · unfold afterStore
    split <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Loader
