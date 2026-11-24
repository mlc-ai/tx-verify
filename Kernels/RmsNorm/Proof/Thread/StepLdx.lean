-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.StepVec
public import Kernels.RmsNorm.Proof.Thread.Pieces

@[expose] public section

/-! # The input loads

After the last element of an input load the code splits each of the four words into halves,
converts them to single precision and chains the fused multiply-adds of their squares, each
instruction a piece (`pc_unpack32`, `pc_widen`, `pc_fma`, `pc_mov`). The machine continues when
none of their outcomes faults (`xOk`); otherwise the thread is dead at the first that faults. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem setRegs_fault {t : TState} {ds : List Nat} {vs : List Value} :
    (setRegs t ds vs).fault = t.fault := by
  induction ds generalizing t vs with
  | nil => cases vs <;> rfl
  | cons d ds ih => cases vs with
    | nil => rfl
    | cons v vs => exact (ih (t := setReg t d v) (vs := vs)).trans rfl

theorem facts_eq {d : D} {s : Site} (hs : d.site = s) : facts P g d = factsAt P g s.pc d := by
  simp [facts, hs]

/-- The state after the first input load with words `vs`. -/
def ldxaNext (d : D) (vs : List Value) : D :=
  { d with site := .stxa0, sub := 0, acc := [], xa := vs }

theorem step_ldxa (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldxa) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldxa.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rw [hs] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
  rw [tmpl_ldx hpre (k := 0) ((.inl rfl)) hrow (reg_of hF (by table_decide))] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs => if xOk vs (z0) then
      some (ldxaNext d vs) else none) := fun e => by simp only [next, hs]; rfl
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  rms_hyps hpre
  have hpc : t.pc = Flow.load_0 := h.1.trans (show d.site.pc = _ by rw [hs]; rfl)
  set d1 := ldxaNext d ([a0, a1, a2] ++ [v]) with hd1
  have hU : At (afterVec t [53, 54, 55, 56] ([a0, a1, a2] ++ [v])) 30
      (factsAt P g 30 d1) := by
    refine ⟨by simp [afterVec, hpc], rfl, rfl, by simp [afterVec, setRegs_fault, h.2.2.2.1], ?_⟩
    have hframe : ∀ r, r ∉ [53, 54, 55, 56] →
        (setRegs t [53, 54, 55, 56] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [53, 54, 55, 56] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  have S' : SegD kernel Prod L g 28 30 (factsAt P g 30 d1) 58 (factsAt P g 58 d1)
      (xOk ([a0, a1, a2] ++ [v]) (z0) = true) := by
    have p30 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_30
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := p30
    have p31 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_31
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p31
    have p32 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_32
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p32
    have p33 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_33
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := S.comp p33
    have p34 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_34
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p34
    have p35 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_35
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p35
    have p36 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_36
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := S.comp p36
    have p37 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_37
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p37
    have p38 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_38
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p38
    have p39 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_39
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := S.comp p39
    have p40 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_40
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p40
    have p41 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_41
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p41
    have p42 := pc_fmaImm (P := P) (L := L) (g := g) (d := d1) Flow.code_42
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p42
    have p43 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_43
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p43
    have p44 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_44
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p44
    have p45 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_45
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p45
    have p46 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_46
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p46
    have p47 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_47
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p47
    have p48 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_48
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p48
    have p49 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_49
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p49
    have p50 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_50
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p50
    have p51 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_51
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p51
    have p52 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_52
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p52
    have p53 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_53
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p53
    have p54 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_54
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p54
    have p55 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_55
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p55
    have p56 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_56
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p56
    have p57 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_57
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p57
    exact S.iff (by simp only [xOk, Bool.and_eq_true]; exact Iff.rfl)
  have hS := S' _ hU
  by_cases hok : xOk ([a0, a1, a2] ++ [v]) (z0) = true
  · obtain ⟨t2, hr2, ht2⟩ := hS.1 hok
    refine .inl ⟨d1, t2, by rw [hnext]; simp only [hok, ↓reduceIte, Option.map_some],
      run_rtg hr2, atD_of rfl rfl ht2, ?_⟩
    simp only [hd1, ldxaNext]
    have := hrow
    inv_tac
  · exact .inr ⟨by rw [hnext]; simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.map_none],
      hS.2 hok⟩

/-- The state after the second input load with words `vs`. -/
def ldxbNext (d : D) (vs : List Value) : D :=
  { d with site := .stxb0, sub := 0, acc := [], xb := vs }

theorem step_ldxb (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldxb) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldxb.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rw [hs] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
  rw [tmpl_ldx hpre (k := 4096) ((.inr rfl)) hrow (reg_of hF (by table_decide))] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs => if xOk vs (fmaRun d.xa 8 z0) then
      some (ldxbNext d vs) else none) := fun e => by simp only [next, hs]; rfl
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  rms_hyps hpre
  have hpc : t.pc = Flow.load_1 := h.1.trans (show d.site.pc = _ by rw [hs]; rfl)
  set d1 := ldxbNext d ([a0, a1, a2] ++ [v]) with hd1
  have hU : At (afterVec t [73, 74, 75, 76] ([a0, a1, a2] ++ [v])) 62
      (factsAt P g 62 d1) := by
    refine ⟨by simp [afterVec, hpc], rfl, rfl, by simp [afterVec, setRegs_fault, h.2.2.2.1], ?_⟩
    have hframe : ∀ r, r ∉ [73, 74, 75, 76] →
        (setRegs t [73, 74, 75, 76] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [73, 74, 75, 76] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  have S' : SegD kernel Prod L g 28 62 (factsAt P g 62 d1) 90 (factsAt P g 90 d1)
      (xOk ([a0, a1, a2] ++ [v]) (fmaRun d.xa 8 z0) = true) := by
    have p62 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_62
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := p62
    have p63 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_63
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p63
    have p64 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_64
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p64
    have p65 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_65
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := S.comp p65
    have p66 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_66
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p66
    have p67 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_67
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p67
    have p68 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_68
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := S.comp p68
    have p69 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_69
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p69
    have p70 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_70
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p70
    have p71 := pc_unpack32 (P := P) (L := L) (g := g) (d := d1) Flow.code_71
        (by table_decide) (by decide) (fun _ => rfl) (fun _ => rfl) (by table_decide)
    have S := S.comp p71
    have p72 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_72
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p72
    have p73 := pc_widen (P := P) (L := L) (g := g) (d := d1) Flow.code_73
        (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p73
    have p74 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_74
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p74
    have p75 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_75
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p75
    have p76 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_76
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p76
    have p77 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_77
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p77
    have p78 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_78
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p78
    have p79 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_79
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p79
    have p80 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_80
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p80
    have p81 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_81
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p81
    have p82 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_82
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p82
    have p83 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_83
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p83
    have p84 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_84
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p84
    have p85 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_85
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p85
    have p86 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_86
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p86
    have p87 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_87
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p87
    have p88 := pc_fma (P := P) (L := L) (g := g) (d := d1) Flow.code_88
        (by table_decide) (by table_decide) (fun _ => rfl) (by table_decide)
    have S := S.comp p88
    have p89 := pc_mov (P := P) (L := L) (g := g) (d := d1) Flow.code_89
        (by table_decide) (by val_bytes) (fun _ => rfl) (by table_decide)
    have S := S.comp_seg p89
    exact S.iff (by simp only [xOk, Bool.and_eq_true]; exact Iff.rfl)
  have hS := S' _ hU
  by_cases hok : xOk ([a0, a1, a2] ++ [v]) (fmaRun d.xa 8 z0) = true
  · obtain ⟨t2, hr2, ht2⟩ := hS.1 hok
    refine .inl ⟨d1, t2, by rw [hnext]; simp only [hok, ↓reduceIte, Option.map_some],
      run_rtg hr2, atD_of rfl rfl ht2, ?_⟩
    simp only [hd1, ldxbNext]
    have := hrow
    inv_tac
  · exact .inr ⟨by rw [hnext]; simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.map_none],
      hS.2 hok⟩

end
end PTX.Kernels.RmsNorm.Proof
