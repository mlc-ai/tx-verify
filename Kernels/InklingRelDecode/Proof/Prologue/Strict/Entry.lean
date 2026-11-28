-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Safe
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.SafePtc
public import Kernels.InklingRelDecode.Proof.Iface.EntryEnv

@[expose] public section

/-! # The tags the softmax entry takes over from the prologue

At the exit of the prologue (program counter 574) the registers the softmax's typed windows start
from hold the words and predicates the control table and `QT proQt` give. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG Control

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem entry_class : ∀ p ∈ Iface.entryEnv, (p.1 ∈ ctlLive 574 ∧ p.1 ≠ 525) ∨
    ((proQt 574).lookup p.1 = some (.bits 32) ∧ p.2 = .old (.bits 32)) ∨
    (p.1 = 525 ∧ p.2 = .old (.bits 32)) := by decide +kernel

theorem lookup_mem {α : Type} {l : List (Nat × α)} {r : Nat} {x : α} :
    l.lookup r = some x → (r, x) ∈ l := by
  induction l with
  | nil => simp
  | cons p l ih =>
    intro h
    by_cases hr : (r == p.1) = true
    · simp only [List.lookup, hr] at h
      have := beq_iff_eq.mp hr
      subst this
      cases h
      exact List.mem_cons_self ..
    · simp only [List.lookup, hr] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- **The registers of the softmax's entry are typed** at a state of the prologue's exit. -/
theorem entry_typed {d : Data.D} {t : TState} (hw0 : w = b32 0) (hk : Ok Q L g d)
    (hs : d.c.site = .exit) (hat : (Data.code Q L g w).AtD d t) (hq : QT proQt t)
    (hpc : t.pc = 574) : TypedF Iface.entryEnv t := by
  intro r tg h
  have hmem : (r, tg) ∈ Iface.entryEnv := lookup_mem h
  obtain ⟨hr', htg⟩ : (r, tg) ∈ Iface.entryEnv ∧ True := ⟨hmem, trivial⟩
  rcases entry_class _ hmem with ⟨hc, hne⟩ | ⟨hp, rfl⟩ | ⟨rfl, rfl⟩
  · have reg := reg_ctl hat (r := r) (by rw [hs]; exact hc)
    have hf : d.c.first = b32 (Q.qStart (reqOf L g)) := hk.1.first (by rw [hs]; decide)
    have hl : d.c.last = b32 (Q.qStart (reqOf L g + 1)) := hk.1.last (by rw [hs]; decide)
    have hq' : d.c.seq = b32 (Q.seqK (reqOf L g)) := hk.1.seq (by rw [hs]; decide)
    rw [reg]
    simp only [Iface.entryEnv, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h <;> obtain ⟨rfl, rfl⟩ := h
    all_goals
      first
      | (rw [valueOf_plain (by decide +kernel)]
         simp only [registerValue, TagF.ok, Tag.ok, hf, hl, hq', hw0]
         first
         | exact ⟨_, rfl⟩
         | exact ⟨_, rfl, dat32_bits _⟩
         | exact absurd rfl hne)
  · exact hq r _ (by rw [hpc]; exact hp)
  · have := tag_reg hat (τ := .scale) (by rw [hs]; decide +kernel)
    simp only [Data.Tag.reg] at this
    simp only [Data.Tag.val] at this
    exact ⟨_, this.trans (by rfl)⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
