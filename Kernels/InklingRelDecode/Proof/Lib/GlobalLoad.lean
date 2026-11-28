-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.LoadAt
public import Lemmas.Flow.MemTmpl
import Lemmas.Flow.Step.ShapeRegs

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- The code at `pc` is a plain global load of `w / 8` bytes through the 64-bit register `base`
with offset zero. -/
def globalLoad (pc base w : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ =>
    a.rule == some .threadAccess && a.locSpace? == some .global &&
      a.addr.base == .reg base 64 && a.kind == .load && a.sem == .weak && !a.nc &&
      a.addr.off == 0 && a.elem.width == w
  | _ => false

theorem global_load_at {pc base w : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (h : globalLoad pc base w = true) :
    ∃ a : MemAccess, ins.op = .mem a ∧ a.rule = some .threadAccess ∧
      a.locSpace? = some .global ∧ a.addr.base = .reg base 64 ∧ a.kind = .load ∧
      a.sem = .weak ∧ a.nc = false ∧ a.addr.off = 0 ∧ a.elem.width = w := by
  unfold globalLoad at h
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [] at h <;> try contradiction
  rename_i a
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨a, rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **A plain global load through a register reads at the register's address.** -/
theorem global_load_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc base w x : Nat} {ins : Instr} {e : Event} {o : Option TState} {acc : Acc}
    {bs : List (Option Byte)}
    (hc : kernel.code[pc]? = some ins) (h : globalLoad pc base w = true) (hsub : t.sub = 0)
    (reg : t.regs base = some (b64 x)) (hx : x < 2 ^ 64)
    (hf : Fires pc (eventTmpl A L g t ins.op) e o) (hk : e.kind = .rd acc bs) :
    acc.loc = ⟨.global, 0, x⟩ ∧ acc.size = w / 8 := by
  obtain ⟨a, hop, hr, hl, hb, hkd, hs, hnc, hoff, hw⟩ := global_load_at hc h
  rw [hop] at hf
  have hm : eventTmpl A L g t (.mem a) = loadTmpl A L g t .global false w a.regs base 0 := by
    change memTmpl A L g t a = _
    rw [memTmpl_direct_weakLoad hr hl hb hkd hs, hnc, hw, hoff]
  rw [hm] at hf
  have hea := effAddr_global (L := L) (g := g) reg hx
  obtain ⟨h1, h2⟩ := loadTmpl_rd hea hf hk
  refine ⟨?_, h2⟩
  rw [hsub] at h1
  simpa [Loc.at] using h1

/-- **A plain global load reads, or faults.** -/
theorem global_load_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc base w : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (h : globalLoad pc base w = true)
    (hf : Fires pc (eventTmpl A L g t ins.op) e o) :
    (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f := by
  obtain ⟨a, hop, hr, hl, hb, hkd, hs, hnc, hoff, hw⟩ := global_load_at hc h
  rw [hop, eventTmpl, memTmpl_direct_weakLoad hr hl hb hkd hs, hnc, hw, hoff] at hf
  exact fires_load_kind hf

end PTX.Kernels.InklingRelDecode.Proof.Lib
