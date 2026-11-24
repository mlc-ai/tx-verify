-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Thread.Machine
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # `row_sum`: the events of the sites

The event each site performs, as a function of the abstract state: the read of element `i` of
row `g`, the store of the accumulator to `B[g]`, the exit. The launch content of an element
(`good`) and the accumulator after `i` elements read as launch content (`accV`). -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat}

/-- Row `g`, element `i` of `A`; element `g` of `B`. -/
def gA (A K g i : Nat) : Loc := ⟨.global, 0, A + 4 * (K * g + i)⟩
def gB (B g : Nat) : Loc := ⟨.global, 0, B + 4 * g⟩

/-- The read of `A[g][i]` returning `bs`, the write of `a` to `B[g]`, and the exit. -/
def rdE (A K g i : Nat) (bs : List (Option Byte)) : Event :=
  ⟨Flow.load_0, .rd { loc := gA A K g i, size := 4 } bs⟩
def wrE (B g : Nat) (a : Value) : Event :=
  ⟨Flow.store_0, .wr { loc := gB B g, size := 4 } a.toBytes⟩
def exE : Event := ⟨Flow.exit_0, .exit⟩

/-- The launch content of `A[g][i]`. -/
def good (x : Nat → ℝ) (K g i : Nat) : List (Option Byte) :=
  (fl (x (K * g + i))).toBytes.map some

/-- The accumulator after `i` elements that read as launch content: the zero it starts as,
then the `f32` sum. -/
def accV (x : Nat → ℝ) (K g i : Nat) : Value := if i = 0 then b32 0 else fl (S K x g i)

theorem good_rebuild : rebuild 3 (good x K g i) = .ok (fl (x (K * g + i))) :=
  rebuild_scalar (by show 0 < 4; decide) rfl

theorem accOk_accV (x : Nat → ℝ) (K g i : Nat) : AccOk (accV x K g i) := by
  unfold accV
  split_ifs
  · exact accOk_z0
  · exact accOk_fl _

theorem valFloat_accV (x : Nat → ℝ) (K g i : Nat) : valFloat .f32 (accV x K g i) = .ok (S K x g i)
    := by
  unfold accV
  split_ifs with h
  · subst h
    rw [valFloat_z0]
    simp [S]
  · rfl

theorem S_succ (x : Nat → ℝ) (K g i : Nat) : S K x g (i + 1) = S K x g i + x (K * g + i) :=
  Finset.sum_range_succ _ _

/-- The template of the load: the read of element `i`. -/
theorem tmpl_load (hpre : Pre L A B M K x mem0) {i : Nat} {a : Value} {t : TState} (hi : i < K)
    (hgM : g < M) (h : At t Site.load.pc (facts A B M K g ⟨.load, i, a⟩)) :
    eventTmpl Prod L g t (.mem ldAcc) =
      .read { loc := gA A K g i, size := 4 } (afterLoad t [11]) := by
  have hrA := hpre.rangeA
  have haA := hpre.alignA
  have hKg := row_le hgM (show i + 1 ≤ K by omega)
  have hr : t.regs 23 = some (b64 (A + 4 * (K * g + i))) := by
    rw [reg_at (d := ⟨.load, i, a⟩) h (by table_decide)]
    rs_values
  show memTmpl Prod L g t ldAcc = _
  rw [memTmpl_load rfl rfl rfl rfl (by decide)]
  change loadTmpl Prod L g t .global false 32 [11] 23 0 = _
  rw [loadTmpl_global h.2.1 hr (by omega) (by decide) (by omega)]
  rfl

/-- The template of the store: the write of the accumulator to `B[g]`. -/
theorem tmpl_store (hpre : Pre L A B M K x mem0) {i : Nat} {a : Value} {t : TState}
    (ha : a.bytes = 4) (hgM : g < M) (h : At t Site.store.pc (facts A B M K g ⟨.store, i, a⟩)) :
    eventTmpl Prod L g t (.mem stAcc) =
      .write { loc := gB B g, size := 4 } a.toBytes (afterStore t [.reg 13]) := by
  have hrB := hpre.rangeB
  have haB := hpre.alignB
  have hr22 : t.regs 22 = some (b64 (B + 4 * g)) := by
    rw [reg_at (d := ⟨.store, i, a⟩) h (by table_decide)]
    rs_values
  have hr13 : t.regs 13 = some a := by
    rw [reg_at (d := ⟨.store, i, a⟩) h (by table_decide)]
    rs_values
  show memTmpl Prod L g t stAcc = _
  rw [memTmpl_store rfl rfl rfl rfl (by decide)]
  change storeTmpl L g t .global 32 22 0 [.reg 13] = _
  rw [storeTmpl_global h.2.1 hr22 (by omega) (by decide) (by omega) hr13,
    storeValue_of_bytes (by simpa using ha)]
  rfl

/-- The event a site performs. -/
def SiteEvent (A B K g : Nat) (d : ThreadD) (e : Event) : Prop :=
  match d.site with
  | .load => ∃ bs, e = rdE A K g d.i bs
  | .store => e = wrE B g d.a
  | .exit => e = exE

/-- **A fired event is its site's event**, and the site's state holds the facts that make its
instruction an event: a load is in range, a store has the final counter. -/
theorem site_event (hpre : Pre L A B M K x mem0) {d : ThreadD} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hinv : Inv M K g d) (h : At t d.site.pc (facts A B M K g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) : SiteEvent A B K g d e := by
  obtain ⟨s, i, a⟩ := d
  obtain ⟨hab, hl, hs⟩ := hinv
  cases s with
  | load =>
    obtain ⟨hi, hgM⟩ : i < K ∧ g < M := hl rfl
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    rw [tmpl_load hpre hi hgM h] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact ⟨bs, he⟩
  | store =>
    obtain ⟨-, hgM⟩ : i = K ∧ g < M := hs rfl
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    rw [tmpl_store hpre hab.1 hgM h] at hf
    exact hf.1
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp only [eventTmpl, Fires] at hf
    exact hf.1

end
end PTX.Kernels.RowSum.Proof
