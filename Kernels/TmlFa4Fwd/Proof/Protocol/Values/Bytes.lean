-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.KvValue
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.QSource
import Lemmas.Tcgen05.TcMmaF16Pair
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The operand bytes of the MMAs

The blocks of a CTA are the numbers its copies wrote (`blocks`): element `(row, d)` of Q stage `st`
is that of the stage's copy of box `d / 64`, and those of the K and V blocks of tile round `u` are
the elements of packets `2 u` and `2 u + 1`. The operand elements of the MMAs are these
(`operandBytes`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm AsyncCopy

noncomputable section
open Classical

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The element `(row, d)` of Q stage `st` that the stage's copy wrote, `x` without a copy. -/
def qEl (p : Params) (L : Launch) (X : Execution) (c : Nat) (st q : Fin 2) (row d : Nat) (x : ℝ) :
    ℝ :=
  if h : ∃ org i, QCp p L X c st q org i then
    (inputVal p false (boxCoord h.choose d row)).getD 0 else x

/-- An element of a K/V packet, `x` without one. -/
def kvEl (L : Launch) (X : Execution) (c t row d : Nat) (x : ℝ) : ℝ :=
  if h : ∃ x, KvEl L X c t row d x then h.choose else x

/-- **The blocks that a CTA's copies loaded**, those of `J` where no copy did. -/
def blocks (p : Params) (L : Launch) (X : Execution) (J : Nat → Inputs) (c : Nat) : Inputs where
  q st row d := qEl p L X c (if st = 0 then 0 else 1) (if d < 64 then 0 else 1) row (d % 64)
    ((J c).q st row d)
  k u row d := kvEl L X c (2 * u) row d ((J c).k u row d)
  v u row d := kvEl L X c (2 * u + 1) row d ((J c).v u row d)

variable {J : Nat → Inputs}

/-- An element of a packet is the element its copy wrote. -/
theorem kvEl_eq (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {c t row d : Nat} {x y : ℝ} (h : KvEl L X c t row d x) :
    kvEl L X c t row d y = x := by
  have hh : ∃ x, KvEl L X c t row d x := ⟨x, h⟩
  unfold kvEl
  rw [dite_eq_left hh]
  exact hh.choose_spec.unique hp hX hFw h

/-- An element of a Q stage is the one of its copy's box. -/
theorem qEl_eq (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {c row d : Nat} {st q : Fin 2} {y : ℝ} {org : Fin 3 → Int} {i : EvId}
    (h : QCp p L X c st q org i) :
    qEl p L X c st q row d y = (inputVal p false (boxCoord org d row)).getD 0 := by
  have hh : ∃ org i, QCp p L X c st q org i := ⟨org, i, h⟩
  unfold qEl
  rw [dite_eq_left hh]
  obtain ⟨i', hC'⟩ := hh.choose_spec
  rw [hC'.unique hp hX hFw h]

/-- **The operand elements of the MMAs are the copies' blocks.** -/
theorem operandBytes (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hIn : InputsUnwritten p X) : OperandBytes (blocks p L X J) L X where
  q {g k st u j d s acc mask ops index row c} hst hR hi hd hops hrow hc hbl := by
    have hq : (⟨c / 64, by omega⟩ : Fin 2) = if c < 64 then 0 else 1 := by
      split <;> apply Fin.ext <;> simp only [Fin.isValue, Fin.val_zero, Fin.val_one] <;> omega
    have hst' : (⟨st, hst⟩ : Fin 2) = if st = 0 then 0 else 1 := by
      split <;> apply Fin.ext <;> simp only [Fin.isValue, Fin.val_zero, Fin.val_one] <;> omega
    obtain ⟨org, i, o, hC, ho, hn, he⟩ := q_copy_exists hp hX hFw hst hR ⟨c / 64, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, inputVal p false (boxCoord org (c % 64) row) = some x := by
      unfold inputVal
      simp only [Bool.false_eq_true, ↓reduceIte]
      split <;> exact ⟨_, rfl⟩
    have hval : (blocks p L X J (g / L.block)).q st row c = x := by
      simp only [blocks]
      rw [← hq, ← hst', qEl_eq hp hX hFw hC, hx, Option.getD_some]
    have hby := fun z (hz : z < 2) => q_operand hp hX hFw hIn hst hR hi hops hrow hc hz (hbl z hz)
      hC ho hn he
    rw [hval]
    refine ⟨_, _, hby 0 (by decide), hby 1 (by decide), ?_⟩
    rw [hx]
    exact rebuild_number (.inr rfl) x
  k {g k st u j d s acc mask ops index row c} hst hR hi hd hops hrow hc hbl := by
    have hKR : KvRead L X g k (2 * u) := ⟨st, u, j, .inl ⟨hR, rfl⟩⟩
    obtain ⟨x, hx⟩ := kv_el_exists hp hX hFw hIn hKR hrow hc
    rw [show (blocks p L X J (g / L.block)).k u row c = x from kvEl_eq hp hX hFw hx]
    exact kv_elem16 hp hX hFw hKR hi hops hrow hc hx hbl
  v {g k st u j d s acc mask ops index row c} hst hR hi hd hops hrow hc hbl := by
    have hKR : KvRead L X g k (2 * u + 1) := ⟨st, u, j, .inr ⟨hR, rfl⟩⟩
    obtain ⟨x, hx⟩ := kv_el_exists hp hX hFw hIn hKR hrow hc
    rw [show (blocks p L X J (g / L.block)).v u row c = x from kvEl_eq hp hX hFw hx]
    exact kv_elem16 hp hX hFw hKR hi hops hrow hc hx hbl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
