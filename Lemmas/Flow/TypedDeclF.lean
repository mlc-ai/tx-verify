-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFH
public import Lemmas.Flow.ArithCore

@[expose] public section

/-! # `mul.f32` without a rounding modifier, where the ideal rule does not decline

`mul.f32` has no Core rule to fall back to when the ideal-real reading declines (a NaN operand,
`0 * inf`), so its step faults there. On `.f32` data whose ideal reading does not decline it
writes the product, a datum. `segQ_mulD` is the segment of one such instruction under the tag
invariant and `TauAll R`, where `R` says the ideal rule does not decline at the instruction's pc
(a fact about the lane's own states, `Iface.LateValues.noDecline`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

/-- A source operand of `.f32` data: a register of tag `dat32` or a `0f` constant. -/
def d32o (env : EnvF) : Opnd → Bool
  | .reg r => d32 env r
  | .f32imm _ => true
  | _ => false

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem d32o_is {env : EnvF} {t : TState} {o : Opnd} (h : d32o env o = true)
    (ht : TypedF env t) : ∃ v, OpndIs L g t o v ∧ Dat32 v := by
  cases o <;> simp only [d32o, Bool.false_eq_true] at h
  · obtain ⟨x, hx, hd⟩ := d32_ok h ht
    exact ⟨x, OpndIs.reg hx, hd⟩
  · exact ⟨_, OpndIs.imm, dat32_bits _⟩

/-- The ideal product of two data that the rule does not decline is a datum. -/
theorem idealMul_dat {va vb : Value} (ha : Dat32 va) (hb : Dat32 vb) (h : idealMul va vb ≠ none) :
    ∃ v, idealMul va vb = some (pure v) ∧ Dat32 v := by
  unfold idealMul at h ⊢
  rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
  · simp [hx, bindRead] at h
  rcases readEReal_dat hb.1 with hy | ⟨y, hy⟩
  · simp [hx, hy, bindRead] at h
  rcases hm : mulEReal x y with _ | r
  · simp [hx, hy, hm, bindRead] at h
  · exact ⟨_, by simp [hx, hy, hm, bindRead], dat32_erealValue r⟩

/-- **The local step of `mul.f32 d, a, b`** on data whose ideal reading does not decline writes
a datum. -/
theorem mulD_step {t : TState} (hI : IdealAt A (.mul .f32) L g t)
    (hD : DeclineAt A (.mul .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hda : Dat32 va) (hdb : Dat32 vb)
    (hnd :
      execIdealFloat L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) ≠ none) :
    ∃ v, execLocalA A L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) =
      .ok (PTX.next (setReg t d v)) ∧ Dat32 v := by
  have hi : execIdealFloat L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) =
      (idealMul va vb).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealMul, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  rw [hi] at hnd
  obtain ⟨v, hv, hdv⟩ := idealMul_dat hda hdb (fun h => hnd (by rw [h]; rfl))
  refine ⟨v, ?_, hdv⟩
  rw [exec_mulE hI hD ha hb]
  unfold mulE
  rw [hv]
  rfl

/-- **One `mul.f32` under the tag invariant**: the segment of the instruction at `pc` writes a
datum to `d` when the ideal rule does not decline there (`hnd`, of the states of `TauAll R`). -/
theorem segQ_mulD {K : Kernel} {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {fz : Bool}
    {a b : Opnd} {F G : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .float { mulI fz with dsts := [some d], srcs := [a, b] }⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A (.mul .f32) L g t ∧ DeclineAt A (.mul .f32) L g t)
    (hnd : ∀ t : TState, t.pc = pc → R t →
      execIdealFloat L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) ≠ none)
    (ha : d32o (qt pc) a = true) (hb : d32o (qt pc) b = true)
    (hq : afterF qt pc [(d, .dat32)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G := by
  refine SegQ.local1 hc rfl hG fun t ht ⟨hQ, hT⟩ => ?_
  have hty : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hty
  obtain ⟨vb, hvb, hdb⟩ := d32o_is (L := L) (g := g) hb hty
  obtain ⟨hI1, hD1⟩ := hI t ht.1
  obtain ⟨v, hex, hdv⟩ := mulD_step hI1 hD1 hva hvb hda hdb (hnd t ht.1 (hT t .refl))
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hdv⟩
  refine ⟨_, hex, by simp [PTX.next, setReg, ht.1], rfl, rfl, rfl,
    fun p hp => by simp [setReg, PTX.next, hd p hp],
    fun hu => ⟨QTF.after1 hQ ht.1 (by simp [PTX.next, setReg, ht.1]) hw1 hw2 hq,
      fun w hw => hT w (.head hu hw)⟩⟩

end
end PTX.Flow.TyG
