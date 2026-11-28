-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataScript
public import Kernels.InklingRelDecode.Proof.Common.DataScriptSoft

@[expose] public section

/-! # The states of a data warp against its script

`DataCnt p lim σ c`: the number `c` of collectives a data lane has made at the state `σ`, as far as
the state fixes it (exactly for the startup, the prologue and the Softmax, from below for the
epilogue). `data_state` then gives the three facts of the classification: a state is at a
collective exactly when the script has its pc at `c`, its time is the slot of `c`, and a state at no
collective is earlier than every later slot. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {g : Nat}

/-- What a state says about the collectives its lane has made (`p` preloaded blocks, `lim`
loop rounds). -/
def DataCnt (p lim : Nat) : (thread Q L g).D → Nat → Prop
  | (.inl s, _), c => c = startCount s.site
  | (.inr ⟨.inl (.prologue _), .inl d⟩, _), c =>
    c = proCount p d.site ∧ ∀ b : Fin 3, d.site.block = some b → b.val < p
  | (.inr ⟨.inl (.prologue _), .inr ⟨_, .inl d⟩⟩, _), c =>
    c = softCount p d.i d.site ∧ d.site ≠ .epilogue ∧
      (d.site.isShuffle = true → d.i < lim) ∧ (d.i < lim ∨ lim = 0) ∧
      (Softmax.needsPrevious d.site = true → 0 < d.i)
  | (.inr ⟨.inl (.prologue _), .inr ⟨_, .inr ⟨_, e⟩⟩⟩, _), c =>
    epiBase p lim ≤ c ∧ (e.site = .shfl → c = epiBase p lim ∧ lim ≠ 0) ∧
      (e.site ≠ .wait → e.site ≠ .shfl → lim ≠ 0 → epiBase p lim + 1 ≤ c)
  | _, _ => False

/-- The clock of a data lane's state: the time table's, by role. -/
def stateClock : (thread Q L g).D → Nat
  | (.inl s, _) => startClock s.site
  | (.inr ⟨.inl (.prologue _), .inl d⟩, _) => proClock d.site
  | (.inr ⟨.inl (.prologue _), .inr ⟨_, .inl d⟩⟩, _) => softClock d.site d.i
  | (.inr ⟨.inl (.prologue _), .inr ⟨_, .inr ⟨_, e⟩⟩⟩, _) => epiClock e.site
  | _ => 0

/-- With no loop rounds the script ends before the Softmax. -/
private theorem cn_none_zero {p n : Nat} (h : 13 + 5 * p ≤ n) : dataCn p 0 n = none := by
  have h0 : ¬ n = 0 := by omega
  have h1 : ¬ n ≤ 12 + 5 * p := by omega
  have e : Lib.shflBase 0 = 0 := by simp [Lib.shflBase]
  simp [dataCn, h0, h1, e]

/-- The three facts of a state with pc `pc` and clock `clk` at script position `c`. -/
def DataFacts (p lim c pc clk : Nat) : Prop :=
  (isWarpAt pc = true ↔ dataCn p lim c = some pc) ∧
  (isWarpAt pc = true → clk = dataSlot p lim c) ∧
  (isWarpAt pc = false → ∀ n, (dataCn p lim n).isSome = true → c ≤ n → clk < dataSlot p lim n)

/-- **The three facts of a data state** at a script position. -/
theorem data_state {p lim : Nat} (hp : p ≤ 3) (hl : lim < 2 ^ 31) {σ : (thread Q L g).D} {c : Nat}
    (h : DataCnt p lim σ c) : DataFacts p lim c ((thread Q L g).pc σ) (stateClock σ) := by
  obtain ⟨s, n⟩ := σ
  rcases s with st | ⟨r, d⟩
  · change c = startCount st.site at h
    subst h
    change DataFacts p lim _ st.site.pc (startClock st.site)
    exact ⟨start_at_iff p lim st.site, fun w => (start_slot_at p lim _ w).symm,
      fun w m _ le => start_slot_lt (p := p) (lim := lim) st.site w le⟩
  rcases r with r | r
  · cases r with
    | dispatch => exact h.elim
    | prologue w =>
      rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
      · obtain ⟨rfl, gate⟩ := h
        change DataFacts p lim _ d.site.pc (proClock d.site)
        exact ⟨pro_at_iff hp gate, fun w => (pro_slot_at hp gate w).symm, fun w m hn le =>
          pro_slot_lt hp hl gate w hn le⟩
      · obtain ⟨rfl, noE, sh, early, pv⟩ := h
        change DataFacts p lim _ d.site.pc (softClock d.site d.i)
        refine ⟨soft_at_iff d.site sh pv, fun w => ?_, fun w m hn le => ?_⟩
        · have w' : d.site.isShuffle = true := by rwa [← soft_warp_iff]
          exact (soft_slot_at (p := p) (lim := lim) d.site (sh w') pv w).symm
        · rcases early with lt | rfl
          · exact soft_slot_lt (p := p) (lim := lim) hp hl d.site (.inl ⟨noE, lt⟩)
              (by rwa [← soft_warp_iff]) pv hn le
          · exfalso
            have := cn_none_zero (p := p) (n := m) (by unfold softCount at le; omega)
            rw [this] at hn
            cases hn
      · obtain ⟨hc, hs, past⟩ := h
        change DataFacts p lim _ d.site.pc (epiClock d.site)
        refine ⟨epi_at_iff d.site hc hs, fun w => ?_, fun w m hn le => ?_⟩
        · have sh : d.site = .shfl := by
            have := epi_warp_iff d.site
            rw [w] at this
            exact of_decide_eq_true this.symm
          obtain ⟨rfl, -⟩ := hs sh
          rw [epi_slot_at (p := p) (lim := lim), sh]
        · have sh : d.site ≠ .shfl := fun e => by
            have := epi_warp_iff d.site
            rw [w] at this
            simp [e] at this
          exact epi_slot_lt d.site hc sh (fun a b => past a sh b) hn le
  · exact h.elim

private theorem cn_le {p lim n : Nat} (h : (dataCn p lim n).isSome = true) :
    n < epiBase p lim ∨ (lim ≠ 0 ∧ n = epiBase p lim) := by
  have e : epiBase p lim = 13 + 5 * p + Lib.shflBase lim := rfl
  unfold dataCn at h
  split_ifs at h with a b c d
  · omega
  · omega
  · omega
  · omega
  · simp at h

/-- **A state at the exit** has made more collectives than the script has. -/
theorem data_exit {p lim : Nat} {σ : (thread Q L g).D} {c : Nat} (h : DataCnt p lim σ c)
    (hpc : (thread Q L g).pc σ = 2855) :
    ∀ n, (dataCn p lim n).isSome = true → n < c := by
  intro n hn
  obtain ⟨s, k⟩ := σ
  rcases s with st | ⟨r, d⟩
  · change st.site.pc = 2855 at hpc
    exfalso
    revert hpc
    cases st.site <;> first | decide | (rename_i r; cases r <;> decide)
  rcases r with r | r
  · cases r with
    | dispatch => exact h.elim
    | prologue w =>
      rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
      · have := d.site.pc_range
        change d.site.pc = 2855 at hpc
        omega
      · change d.site.pc = 2855 at hpc
        rcases d.site.pc_range with a | a
        · omega
        · exfalso
          obtain ⟨-, noE, -⟩ := h
          exact noE a
      · obtain ⟨hc, hs, past⟩ := h
        change d.site.pc = 2855 at hpc
        have nw : d.site ≠ .wait := fun e => by rw [e] at hpc; exact absurd hpc (by decide)
        have ns : d.site ≠ .shfl := fun e => by rw [e] at hpc; exact absurd hpc (by decide)
        rcases cn_le hn with a | ⟨nz, rfl⟩
        · omega
        · have := past nw ns nz
          omega
  · exact h.elim

end PTX.Kernels.InklingRelDecode.Proof
