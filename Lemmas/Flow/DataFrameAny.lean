-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataAdvance
public import Lemmas.Flow.RegionFrame

@[expose] public section

/-! # The data step of any event that keeps the successor's data facts

A proof tool, generic over the kernel. A value machine at an event whose instruction writes no
register of the successor's data facts (`eventWrites`) and whose continuation up to the next event
stays in a frame set (`frameSetG`, writing none of them) keeps those facts: `DataStep.frameAny`,
for every kind of event (the event leaves the thread at its position or the next one:
`eventTmpl_return_frame_at`). -/

namespace PTX.Flow.Code
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A frame set that writes none of a list of registers writes none of a sublist. -/
theorem frameSetG_mono {S rs rs' : List Nat} (h : frameSetG K S rs' = true)
    (hs : ∀ r ∈ rs, r ∈ rs') : frameSetG K S rs = true := by
  unfold frameSetG at h ⊢
  simp only [List.all_eq_true] at h ⊢
  intro pc hpc
  have h1 := h pc hpc
  cases hc : K.code[pc]? with
  | none => rw [hc] at h1; exact h1
  | some ins =>
    rw [hc] at h1
    simp only at h1 ⊢
    by_cases hl : ins.op.isLocal = true
    · simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
      exact ⟨⟨⟨h1.1.1.1, fun r hr => h1.1.1.2 r (hs r hr)⟩, h1.1.2⟩, h1.2⟩
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
      exact h1

/-- **The data step of an event that keeps the successor's facts.** -/
theorem DataStep.frameAny {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    (hA : RulesFrame A) {S : List Nat} (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    (hs0 : Assumption.SegFreePc A (C'.pc d))
    (hp0 : (S.contains (C'.pc d) || evAtB K (C'.pc d)) = true)
    (hp1 : (S.contains (C'.pc d + 1) || evAtB K (C'.pc d + 1)) = true)
    (hF : ∀ R, Holds R (C'.facts d) → Holds R (dF d))
    (hev : ∀ ins, K.code[C'.pc d]? = some ins → ∀ e d', C'.next d e = some (some d') →
      ((dF d').map Prod.fst).all (fun r => !(eventWrites ins.op).contains r) = true)
    (hB : ∀ e d', C'.next d e = some (some d') → frameSetG K S ((dF d').map Prod.fst) = true)
    (hsub : ∀ e d', C'.next d e = some (some d') → ∀ x ∈ dF d', x ∈ dF d) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain ⟨hpc, -, -, -, hreg⟩ := hat
  have hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u := fun op u h =>
    execLocalA_frame hA h (hpc ▸ hs0)
  rw [← hpc] at hf
  have hup := callbackFrame_fires (eventTmpl_return_frame_at (op := ins.op) hloc) hf
  have hkept := callbackFrame_fires (eventTmpl_kept_at (op := ins.op) hloc) hf
  have hH : Holds t.regs (dF d') := holds_of_mem fun r v hm =>
    holds_mem (hF _ hreg) (hsub e d' hn _ hm)
  refine .inl fun t' hr _ => (rtg_frameSetG hA (hB e d' hn) hS ?_ ?_ hr).2
  · rcases hup with h | h
    · rw [h, hpc]; exact hp0
    · rw [h, hpc]; exact hp1
  · refine holds_of_mem fun r v hm => ?_
    rw [hkept r ?_]
    · exact holds_mem hH hm
    · intro hmem
      have := List.all_eq_true.mp (hev ins hc' e d' hn) r (List.mem_map.mpr ⟨_, hm, rfl⟩)
      simp [hmem] at this

end
end PTX.Flow.Code
