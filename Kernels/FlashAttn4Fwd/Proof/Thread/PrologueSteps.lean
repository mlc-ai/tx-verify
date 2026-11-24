-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueStart
public import Lemmas.Flow.Next

@[expose] public section

/-! # What a prologue step owes, and the tools of the step proofs

A prologue event leads to a prologue state, whose concrete states satisfy the facts of its site
and the invariant, or (at the cluster wait) to a role, whose concrete state is at the role's
`setmaxnreg` with the prologue's registers live there (`Good`). Each step proof evaluates the
local code after the event on its footprint (`pro_seg`); a branch on a warp-index test whose
outcome the evaluation cannot see (the warp index is symbolic) is taken as one step with the
test's value from the table (`bra_to`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A concrete state of a prologue successor. -/
def Good (L : Launch) (g : Nat) : D ⊕ RoleKind → TState → Prop
  | .inl p, t => At t p.site.pc (facts L g p) ∧ Inv L g p
  | .inr k, t => At t k.entry (factsAt L g (warpOf L g) (rankOf L g) k.entry)

/-- The obligation of one prologue event: a pending fault, or local steps to a concrete state of
the successor. -/
abbrev Step (L : Launch) (g : Nat) (d : D) (u : TState) (e : Event) : Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ Good L g d' t'

variable {L : Launch} {g w rk : Nat}

/-- A branch on a test the table states, as one step to the target's facts. -/
theorem bra_to {t : TState} {pc target p b : Nat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc (factsAt L g w rk pc)) (hp : p ∈ Flow.live pc)
    (hv : valueOf L g w rk p = .pred pick)
    (hb : b = if pick then target else pc + 1) (hl : ∀ r ∈ Flow.live b, r ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' b (factsAt L g w rk b) := by
  obtain ⟨t', hr, ht⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g) hc pick h
    (hv ▸ holds_mem h.2.2.2.2 (mem_factsFrom hp)) asms_localRule_none hsf
  rw [← hb] at ht
  exact ⟨t', hr, At.mono ht (holds_factsFrom_mono ht.2.2.2.2 hl)⟩

/-- Facts at the next instruction from a state whose registers differ in `ws` only. -/
theorem at_next_of {t t' : TState} {pc : Nat} {ws : List Nat}
    (h : At t pc (factsAt L g w rk pc)) (hpc : t'.pc = pc + 1) (hs : t'.sub = t.sub)
    (ha : t'.acc = t.acc) (hf : t'.fault = t.fault)
    (hw : ∀ r ∈ ws, r ∈ Flow.live (pc + 1) → t'.regs r = some (valueOf L g w rk r))
    (hfr : ∀ r, r ∉ ws → t'.regs r = t.regs r)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ ws ∨ r ∈ Flow.live pc) :
    At t' (pc + 1) (factsAt L g w rk (pc + 1)) := by
  refine ⟨hpc, hs.trans h.2.1, ha.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr => ?_⟩
  by_cases hm : r ∈ ws
  · exact hw r hm hr
  · rw [hfr r hm]
    rcases hl r hr with h' | h'
    · exact absurd h' hm
    · exact holds_mem h.2.2.2.2 (mem_factsFrom h')

/-- An event that writes one register with its table value continues at the next
instruction with the table's facts. -/
theorem at_set {t : TState} {pc r : Nat} {v : Value} (h : At t pc (factsAt L g w rk pc))
    (hv : v = valueOf L g w rk r) (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ [r] ∨ x ∈ Flow.live pc) :
    At (PTX.next (setReg t r v)) (pc + 1) (factsAt L g w rk (pc + 1)) :=
  at_next_of (ws := [r]) h (by simp [PTX.next, setReg, h.1]) rfl rfl rfl
    (fun x hx _ => by
      simp only [List.mem_singleton] at hx
      subst hx
      simp [setReg, PTX.next, hv])
    (fun x hx => by
      simp only [List.mem_singleton] at hx
      simp [setReg, PTX.next, Function.update_of_ne hx]) hl

/-- After an election that writes the leader's lane to the dead register `d` and the
election's predicate to `p`: the site's facts and the predicate. -/
theorem at_elect {t : TState} {pc d p : Nat} {x : Value} {b : Bool}
    (h : At t pc (factsAt L g w rk pc)) (hd : d ∉ Flow.live pc) (hp : p ∉ Flow.live pc) :
    At (PTX.next (setReg (setReg t d x) p (.pred b))) (pc + 1)
      ((p, .pred b) :: factsAt L g w rk pc) := by
  refine At.set ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩ (not_mem_factsFrom hp)
  exact holds_update h.2.2.2.2 (not_mem_factsFrom hd)

theorem good_inl {p : D} {t : TState} (h : At t p.site.pc (facts L g p)) (hi : Inv L g p) :
    Good L g (.inl p) t := ⟨h, hi⟩

/-- A site outside warps 0 and 12's elections satisfies the invariant. -/
theorem inv_of {p : D} (h0 : ∀ e, p.site ≠ .elect e) (h1 : ∀ j, p.site ≠ .init j)
    (h2 : p.site ≠ .elect12) (h3 : p.site ≠ .init320) : Inv L g p :=
  ⟨fun h => by rcases h with ⟨e, he⟩ | ⟨j, hj⟩ <;> simp_all,
    fun h => by rcases h with h | h <;> simp_all⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
