-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionEvents
public import Lemmas.Flow.ElemAccess

@[expose] public section

/-! # The rescale stores of the correction warps

The store of rescale chunk `j` of stage `st` (`Site.rst st j`) is a `tcgen05.st` from the chunk's
address of sixteen registers; register `p` holds half `p % 2` of the product of pair `p / 2` of
the chunk with `α` (`rs d (p / 2) (p % 2)`), so value `p` of the store is that product
(`rst_store`, from the decoded instruction and the site's register facts). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The register holding value `p` of rescale chunk `j` of stage `st`. -/
def rstReg (st j p : Nat) : Nat := (if st = 0 then 2765 else 3023) + 32 * j - 2 * (p / 2) + p % 2

/-- The sources of the store of rescale chunk `j` of stage `st`. -/
def rstSrcs (st j : Nat) : List Opnd := (List.range 16).map fun p => .reg (rstReg st j p)

/-- The instruction at `pc` is a `tcgen05.st` from `ta` of `ss`. -/
def tcStIs (pc ta : Nat) (ss : List Opnd) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .tcSt ta' ss'⟩ => ta' == ta && ss' == ss
  | _ => false

theorem tcStIs_spec {pc ta : Nat} {ss : List Opnd} (h : tcStIs pc ta ss = true) :
    kernel.code[pc]? = some ⟨none, .tcSt ta ss⟩ := by
  unfold tcStIs at h
  split at h
  · rename_i ta' ss' hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hc, h.1, h.2]
  · cases h

set_option maxHeartbeats 8000000 in
theorem code_rst_spec (st : Fin 2) (j : Fin 8) :
    kernel.code[(Site.rst st j).pc]? = some ⟨none, .tcSt (ldAddr st j) (rstSrcs st.val j.val)⟩ := by
  apply tcStIs_spec
  simp only [Site.pc]
  fin_cases st <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 8000000 in
theorem rst_live (st : Fin 2) (j : Fin 8) (p : Fin 16) :
    rstReg st.val j.val p.val ∈ Flow.live (Site.rst st j).pc := by
  simp only [Site.pc]
  fin_cases st <;> fin_cases j <;> fin_cases p <;> decide +kernel

set_option maxHeartbeats 8000000 in
theorem rstReg_value (L : Launch) (g : Nat) (d : D) (st : Fin 2) (j : Fin 8) (p : Fin 16) :
    valueOf L g d (rstReg st.val j.val p.val) = rs d (p.val / 2) (p.val % 2) := by
  fin_cases st <;> fin_cases j <;> fin_cases p <;>
    simp only [rstReg, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
      Option.getD_some]

/-- **A rescale store**: value `p` of the store of chunk `j` is the product
`rs d (p / 2) (p % 2)`. -/
theorem rst_store {L : Launch} {g : Nat} {d : D} {t : TState} {e : Event} {ins : Instr}
    {o : Option TState} {st : Fin 2} {j : Fin 8} (hs : d.site = .rst st j)
    (hat : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) {a : Nat} {vals : List Value}
    (hk : e.kind = .tc (.st a vals .s32x32b)) {p : Nat} (hp : p < 16) :
    vals[p]? = some (rs d (p / 2) (p % 2)) := by
  rw [hs] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (code_rst_spec st j))
  have hv : t.regs (rstReg st.val j.val p) = some (rs d (p / 2) (p % 2)) := by
    have := holds_mem hat.2.2.2.2 (mem_factsFrom (List.mem_append_left _
      (hs ▸ rst_live st j ⟨p, hp⟩)))
    rw [this, rstReg_value L g d st j ⟨p, hp⟩]
  refine fires_tcSt_vals ?_ hf hk (by simp [rstSrcs, hp]) hv
  intro s hs'
  cases hs'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
