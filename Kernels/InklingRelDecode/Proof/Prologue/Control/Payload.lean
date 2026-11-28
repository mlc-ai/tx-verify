-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Proof PTX.Flow

/-- The subtraction at 38 reads the first word as bits. At 42 the length is
the right operand, so a surviving length is the integer result of pc 38. -/
def Words (d : D) : Prop :=
  d.first.regBits.isSome ∧ ∃ x, subValue d.last d.first = .bits 32 x

def Payload (d : D) : Prop :=
  (41 ≤ d.site.pc → d.first.regBits.isSome) ∧
  (130 ≤ d.site.pc → ∃ x, subValue d.last d.first = .bits 32 x)

@[reducible] noncomputable def checkedCode (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code kernel Assumptions.all L g :=
  {code Q L g w with inv := fun d => Inv (g%L.block) d ∧ Payload d}

theorem words_payload {d : D} (ok : Words d) : Payload d := ⟨fun _ => ok.1,fun _ => ok.2⟩

private theorem later (s : Site) (h₀ : s ≠ .sMax) (hr : ∀ j, s ≠ .ld j) : 130 ≤ s.pc := by
  have bound (z : Site) : (match z with | .sMax | .ld _ => True | _ => 130 ≤ z.pc) := by
    cases z <;> repeat' first | exact trivial | (rename_i i; revert i)
    all_goals decide +kernel
  have hb := bound s
  cases s <;> first | exact hb | contradiction | exact False.elim (hr _ rfl)

private theorem unchanged {Q L g d e t} (hn : next Q L g d e = some (some t))
    (h : ∀ j, d.site ≠ .ld j) : t.first = d.first ∧ t.last = d.last := by
  cases hs : d.site <;> simp only [next,hs] at hn
  all_goals try exact False.elim (h _ hs)
  all_goals repeat' split at hn
  all_goals first | contradiction | (cases hn; exact ⟨rfl,rfl⟩) | cases hn

/-- Outside the three request reads the successor changes only the site or the
winner of an election. The initial setmaxnreg advances to the first read. -/
theorem payload_next {Q L g d e t} (hn : next Q L g d e = some (some t))
    (hi : Payload d) (h : ∀ j, d.site ≠ .ld j) : Payload t := by
  by_cases head : d.site=.sMax
  · simp only [next,head,Option.some.injEq] at hn
    subst t
    change (41≤34 → _) ∧ (130≤34 → _)
    exact ⟨fun h => by omega,fun h => by omega⟩
  · obtain ⟨a,b⟩ := unchanged hn h
    have bound := later d.site head h
    exact words_payload ⟨a ▸ hi.1 (by omega),b ▸ a ▸ hi.2 bound⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
