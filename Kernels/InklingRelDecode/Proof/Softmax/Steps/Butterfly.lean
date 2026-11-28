-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Rescale
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Flow.Code
import Kernels.InklingRelDecode.Flow.Code.Part035

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

/-- The registers that hold the minimum of the carried words, and all that read them. -/
def minRegs : List Nat := [1534,1536,1538,1540,1544]
def wordRegs : List Nat := 1542 :: 1543 :: minRegs

theorem val_min (d : D) {r : Nat} (h : r ∈ minRegs) :
    valueOf e L g d r = Lib.minWord d.held.word d.held.peer := by
  simp only [minRegs,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [valueOf]

theorem val_frame {c c' : Carry} {r : Nat} (h : r ∉ wordRegs) (same : c.base = c'.base)
    (s s' : Site) : valueOf e L g ⟨s,i,c⟩ r = valueOf e L g ⟨s',i,c'⟩ r := by
  simp only [wordRegs,minRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := h
  simp only [valueOf,same,h1,h2,h3,h4,h5,h6,h7,↓reduceIte]

/-- After a butterfly shuffle the next instruction minimizes the operand and the received value. -/
private theorem min_seg {s z : Site} {src dst dm : Nat} (a w : Value)
    (code : kernel.code[s.pc+1]? = some ⟨none,MinCore.minOp dm [src,dst]⟩)
    (emu : Assumptions.emuSites.contains (s.pc+1) = false) (h1 : s.pc+1 ≠ 2562)
    (h2 : s.pc+1 ≠ 600) (h3 : s.pc+1 ≠ 807) (hz : z.pc = s.pc+2)
    (hdm : dm ∈ minRegs)
    (cover : ∀ r ∈ ctlLive z.pc, r = dm ∨ (r ∈ ctlLive s.pc ∧ r ∉ wordRegs)) :
    SegU kernel Assumptions.all L g (s.pc+1)
      ((src,a) :: (dst,w) :: facts e L g ⟨s,i,v⟩ s.pc) z.pc
      (facts e L g ⟨z,i,{v with word := a, peer := w}⟩ z.pc) := by
  intro t ⟨pc,sub,acc,fault,hs,hd,regs⟩
  have m := min_at (L := L) (g := g) (dm := dm) pc emu h1 h2 h3 hs hd
  have ci : kernel.code[t.pc]? = some ⟨none,MinCore.minOp dm [src,dst]⟩ := pc ▸ code
  cases hm : MinCore.minE [a,w] with
  | error f =>
    rw [hm] at m
    exact .inr (dead_of_error ci rfl fault m)
  | ok x =>
    rw [hm] at m
    have hτ := tau_of_ok ci rfl fault m
    refine .inl ⟨_,Relation.ReflTransGen.single hτ,by simp only [PTX.next,setReg]; omega,sub,acc,
      fault,holds_of_pointwise ?_⟩
    intro r hr
    rcases cover r hr with rfl | ⟨hm',hw⟩
    · rw [val_min _ hdm]
      simp [PTX.next,setReg,Lib.minWord,hm]; rfl
    · have ne : r ≠ dm := by
        rintro rfl
        exact hw (by simp [wordRegs,hdm])
      rw [← val_frame (c := v) (c' := {v with word := a, peer := w}) hw rfl s z]
      simp only [PTX.next,setReg,Function.update_of_ne ne]
      exact holds_mem regs (mem_factsFrom hm')

/-- A butterfly shuffle that carries the operand and the received value into the next minimum. -/
theorem shuffle_min {s z : Site} {dst src dm n : Nat}
    (hc : kernel.code[s.pc]? = some ⟨none,.warp ⟨.shfl .bfly,some (.int .b 32),[some dst],
      [.reg src,.imm n,.imm 31],some (.imm (-1))⟩⟩)
    (hm : kernel.code[s.pc+1]? = some ⟨none,MinCore.minOp dm [src,dst]⟩)
    (hn : ∀ m a b c recv ok, next e L g ⟨s,i,v⟩ ⟨s.pc,.shfl m a b c recv ok⟩ =
      some (some ⟨z,i,{v with word := a, peer := recv}⟩))
    (live : SiteBody s ∧ SiteBody z) (free : dst ∉ ctlLive s.pc) (ne : src ≠ dst)
    (one : ∀ t : TState, ∃ m, readBits L g t 32 (.imm n) = .ok m)
    (emu : Assumptions.emuSites.contains (s.pc+1) = false) (h1 : s.pc+1 ≠ 2562)
    (h2 : s.pc+1 ≠ 600) (h3 : s.pc+1 ≠ 807) (hz : z.pc = s.pc+2)
    (hdm : dm ∈ minRegs)
    (cover : ∀ r ∈ ctlLive z.pc, r = dm ∨ (r ∈ ctlLive s.pc ∧ r ∉ wordRegs)) :
    (code e L g).StepAtU ⟨s,i,v⟩ where
  site := fun _ => ⟨_,hc,rfl,trivial⟩
  step := by
    intro t ev u ins hat hi get fire
    obtain rfl := Option.some.inj (get.symm.trans hc)
    obtain ⟨a,b,c,recv,ok,rfl,rfl⟩ := fires_shfl (p := none) fire
    obtain ⟨m,one'⟩ := one t
    obtain ⟨same,-,-,-⟩ := Lib.shfl_operand one' rfl fire rfl
    obtain ⟨pc,sub,acc,fault,regs⟩ := hat
    have key : dst ∉ ((code e L g).facts ⟨s,i,v⟩).map Prod.fst := by
      change dst ∉ (factsFrom _ _).map Prod.fst
      rwa [factsFrom_keys]
    obtain ⟨w,steps,good⟩ := Code.landsU (C := code e L g)
      (d := ⟨z,i,{v with word := a, peer := recv}⟩) (u := PTX.next (setReg t dst recv))
      ⟨congrArg (·+1) pc,sub,acc,fault,
        (holds_cons _ _ _ _).mpr ⟨by simp only [PTX.next,setReg,Function.update_of_ne ne,same],
          (holds_cons _ _ _ _).mpr ⟨by simp only [PTX.next,setReg,Function.update_self],
            holds_update regs fun p h eq => key (eq ▸ List.mem_map_of_mem h)⟩⟩⟩
      (min_seg a recv hm emu h1 h2 h3 hz hdm cover) (body_inv hi live.1 live.2) rfl rfl
    exact .inl (.inr ⟨_,w,hn .bfly a b c recv ok,steps,good⟩)

theorem step_shfl7 : (code e L g).StepAtU ⟨.shfl7,i,v⟩ :=
  shuffle_min (s := .shfl7) (z := .shfl8) (dst := 1535) (src := 507) (dm := 1536) (n := 8)
    Flow.code_shfl_7 Flow.code_2243 (fun _ _ _ _ _ _ => rfl) (by decide) (by decide +kernel)
    (by decide) (fun _ => ⟨_,rfl⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel)

theorem step_shfl8 : (code e L g).StepAtU ⟨.shfl8,i,v⟩ :=
  shuffle_min (s := .shfl8) (z := .shfl9) (dst := 1537) (src := 1536) (dm := 1538) (n := 4)
    Flow.code_shfl_8 Flow.code_2245 (fun _ _ _ _ _ _ => rfl) (by decide) (by decide +kernel)
    (by decide) (fun _ => ⟨_,rfl⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel)

theorem step_shfl9 : (code e L g).StepAtU ⟨.shfl9,i,v⟩ :=
  shuffle_min (s := .shfl9) (z := .shfl10) (dst := 1539) (src := 1538) (dm := 1540) (n := 2)
    Flow.code_shfl_9 Flow.code_2247 (fun _ _ _ _ _ _ => rfl) (by decide) (by decide +kernel)
    (by decide) (fun _ => ⟨_,rfl⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel)

theorem step_shfl10 : (code e L g).StepAtU ⟨.shfl10,i,v⟩ :=
  shuffle_min (s := .shfl10) (z := .store10) (dst := 1541) (src := 1540) (dm := 1534) (n := 1)
    Flow.code_shfl_10 Flow.code_2249 (fun _ _ _ _ _ _ => rfl) (by decide) (by decide +kernel)
    (by decide) (fun _ => ⟨_,rfl⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
