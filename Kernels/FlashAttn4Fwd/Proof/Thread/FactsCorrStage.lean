-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts
public import Lemmas.Flow.ElemAccess

@[expose] public section

/-! # The staging writes of the correction warps

Element `el` of store `h` of final chunk `j` of stage `st` (`Site.fst st j h el`) writes the four
bytes of the half-precision word `fw d (4 h + el)` (the products of pair `4 h + el` of the chunk
with `1 / l'`) at `stage L g st (2 (j % 4) + h) + 16384 (j / 4) + 4 el` of the thread's CTA: the
store's base register holds the swizzled address of 16-byte chunk `2 (j % 4) + h` of the
thread's row in stage `st`'s first half, its offset selects the half `j / 4`, and its four
sources are the words of the chunk (`fst_write`, from the decoded instructions and the site's
register facts). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The register holding the staging address of 16-byte chunk `c` of stage `st`. -/
def fstBase (st c : Nat) : Nat :=
  if c = 0 then 625 + st else if st = 0 then 644 + c else 651 + c

/-- The register holding word `q` of final chunk `j` of stage `st`. -/
def fwReg (st j q : Nat) : Nat := (if st = 0 then 3296 else 3619) + 40 * j - 3 * q

/-- The sources of store `h` of final chunk `j` of stage `st`. -/
def fstSrcs (st j h : Nat) : List Opnd :=
  (List.range 4).map fun el => .reg (fwReg st j (4 * h + el))

/-- The 32-bit shared vector store from `base` at `off` of `srcs`. -/
def stv32 (base : Nat) (off : Int) (srcs : List Opnd) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    vec := srcs.length, addr := ⟨.reg base 32, off⟩, srcs := srcs }

/-- The instruction at `pc` is a 32-bit shared vector store from `base` at `off` of `srcs`. -/
def stvIs (pc base : Nat) (off : Int) (srcs : List Opnd) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .mem a⟩ => a == stv32 base off srcs
  | _ => false

theorem stvIs_spec {pc base : Nat} {off : Int} {srcs : List Opnd} (h : stvIs pc base off srcs) :
    kernel.code[pc]? = some ⟨none, .mem (stv32 base off srcs)⟩ := by
  unfold stvIs at h
  split at h
  · rename_i a hc
    simp only [beq_iff_eq] at h
    rw [hc, h]
  · cases h

set_option maxHeartbeats 8000000 in
/-- The instruction of store `h` of final chunk `j` of stage `st`. -/
theorem code_fst_spec (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4) :
    kernel.code[(Site.fst st j h el).pc]? = some ⟨none, .mem (stv32
      (fstBase st.val (2 * (j.val % 4) + h.val)) ((16384 * (j.val / 4) : Nat) : Int)
      (fstSrcs st.val j.val h.val))⟩ := by
  apply stvIs_spec
  simp only [Site.pc]
  fin_cases st <;> fin_cases j <;> fin_cases h <;> decide +kernel

set_option maxHeartbeats 8000000 in
/-- The base and the sources of a store are live at it. -/
theorem fst_live (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4) :
    fstBase st.val (2 * (j.val % 4) + h.val) ∈ Flow.live (Site.fst st j h el).pc ∧
      fwReg st.val j.val (4 * h.val + el.val) ∈ Flow.live (Site.fst st j h el).pc := by
  simp only [Site.pc]
  fin_cases st <;> fin_cases j <;> fin_cases h <;> fin_cases el <;> decide +kernel

set_option maxHeartbeats 8000000 in
theorem fstBase_value (L : Launch) (g : Nat) (d : D) (st : Fin 2) (c : Fin 8) :
    valueOf L g d (fstBase st.val c.val) = b32 (stage L g st.val c.val) := by
  fin_cases st <;> fin_cases c <;>
    simp only [fstBase, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
      Option.getD_some]

set_option maxHeartbeats 8000000 in
theorem fwReg_value (L : Launch) (g : Nat) (d : D) (st : Fin 2) (j : Fin 8) (q : Fin 8) :
    valueOf L g d (fwReg st.val j.val q.val) = fw d q.val := by
  fin_cases st <;> fin_cases j <;> fin_cases q <;>
    simp only [fwReg, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
      Option.getD_some]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}

/-- **A staging write**: element `el` of store `h` of final chunk `j` of stage `st` writes the
word `fw d (4 h + el)` at its swizzled address. -/
theorem fst_write {t : TState} {e : Event} {ins : Instr} {o : Option TState} (hpre : Pre P L mem0)
    {st : Fin 2} {j : Fin 8} {h : Fin 2} {el : Fin 4} (hs : d.site = .fst st j h el)
    (hat : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) :
    acc.loc = ⟨.shared, ctaOf L g,
      stage L g st.val (2 * (j.val % 4) + h.val) + 16384 * (j.val / 4) + 4 * el.val⟩ ∧
      acc.size = 4 ∧ bs = (fw d (4 * h.val + el.val)).toBytes := by
  rw [hs] at hc hf hat
  obtain rfl := Option.some.inj (hc.symm.trans (code_fst_spec st j h el))
  have hl := fst_live st j h el
  have hr : t.regs (fstBase st.val (2 * (j.val % 4) + h.val)) =
      some (b32 (stage L g st.val (2 * (j.val % 4) + h.val))) := by
    have := holds_mem hat.2.2.2.2 (mem_factsFrom (List.mem_append_left _ (hs ▸ hl.1)))
    rw [this, fstBase_value L g d st ⟨_, by omega⟩]
  have hv : t.regs (fwReg st.val j.val (4 * h.val + el.val)) =
      some (fw d (4 * h.val + el.val)) := by
    have := holds_mem hat.2.2.2.2 (mem_factsFrom (List.mem_append_left _ (hs ▸ hl.2)))
    rw [this, fwReg_value L g d st j ⟨_, by omega⟩]
  have hlt := stage_lt (g := g) hpre st.val (2 * (j.val % 4) + h.val) st.isLt (by omega)
  have hsub : t.sub = el.val := by rw [hat.2.1]; rfl
  obtain ⟨h1, h2, h3⟩ := fires_stv32_off hr rfl (by omega) (by simp [fstSrcs]) hf acc bs hk
  refine ⟨by rw [h1, hsub]; rfl, h2, h3 _ _ ?_ hv (cvtPairV_bytes _ _)⟩
  rw [hsub]
  simp [fstSrcs]

/-- **The footprint of a staging store's write** (`WrAt`), from its site's instruction and
registers. -/
theorem site_wr {t : TState} {e : Event} {ins : Instr} {o : Option TState} (hpre : Pre P L mem0)
    (hat : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) : WrAt L g d e := by
  intro st j h el hs ac bs hk
  obtain ⟨h1, h2, -⟩ := fst_write hpre hs hat hc hf hk
  exact ⟨h1, h2⟩

/-- **The predicate of a vote** (`VoteAt`): whether `α < 1`, from its site's instruction and
registers. -/
theorem site_vote {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hi : Inv L g d)
    (hat : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : VoteAt d e := by
  intro st hs m a b hk
  have hat' : At t d.site.pc (facts L g d) :=
    ⟨hat.1, by rw [hat.2.1, hs]; rfl, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
  fin_cases st
  · obtain ⟨⟨m', b', rfl⟩, -⟩ := step_vote0 hpre hs hi hat' hc hf
    simp only at hk
    injection hk with h1 h2
    exact h2.symm
  · obtain ⟨⟨m', b', rfl⟩, -⟩ := step_vote1 hpre hs hi hat' hc hf
    simp only at hk
    injection hk with h1 h2
    exact h2.symm

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
