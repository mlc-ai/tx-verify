-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- One decoded input to the loader swizzle calculation and its live range. -/
structure LaneWord where
  register : Nat
  defined : Nat
  stop : Nat
  source : Nat
  isShift : Bool

/-- The two shift-and-mask pairs that seed the recurring swizzles. -/
def laneWord : Fin 4 → LaneWord
  | 0 => ⟨1967, 925, 927, 1061, true⟩
  | 1 => ⟨1119, 926, 1138, 1967, false⟩
  | 2 => ⟨2129, 1388, 1390, 1061, true⟩
  | 3 => ⟨1147, 1389, 1744, 2129, false⟩

/-- Whether this word is defined at the current loader instruction. -/
def LaneWord.live (f : LaneWord) (pc : Nat) : Prop := f.defined < pc ∧ pc < f.stop
instance (f : LaneWord) (pc : Nat) : Decidable (f.live pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def LaneWord.input (f : LaneWord) (tid : Nat) : Nat :=
  if f.isShift then tid else 8 * tid

/-- The bit operation computed by the lane preparation instruction. -/
def LaneWord.output (f : LaneWord) (tid : Nat) : Nat :=
  if f.isShift then 8 * tid else 8 * (tid % 8)

/-- The CTA-local thread ID and its decoded warm and steady copy-column operands. -/
def LoaderCopyLaneFrame (l : Launch) (g : Nat) (s : TState) : Prop :=
  s.regs 1061 = some (b32 (g % l.block)) ∧
    ∀ site : Fin 4, (laneWord site).live s.pc →
      s.regs (laneWord site).register = some (b32 ((laneWord site).output (g % l.block)))

/-- The lane and column frame at common dispatch. -/
theorem loaderCopyLaneFrameAtDispatch {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = 174) (ht : s.regs 1061 = some (b32 (g % l.block))) :
    LoaderCopyLaneFrame l g s := by
  refine ⟨ht, ?_⟩
  intro site hl
  rw [hPc] at hl
  exact ((show ∀ i : Fin 4, ¬ (laneWord i).live 174 by decide) site hl).elim

private def LaneWord.instruction (f : LaneWord) : Instr :=
  ⟨none, .int ⟨if f.isShift then .shl else .and, .int .b 32, false, [some f.register],
    [.reg f.source, .imm (if f.isShift then 3 else 56)]⟩⟩

private theorem laneWordCode (site : Fin 4) :
    kernel.code[(laneWord site).defined]? = some (laneWord site).instruction := by
  fin_cases site
  · exact Flow.code_925
  · exact Flow.code_926
  · exact Flow.code_1388
  · exact Flow.code_1389

private theorem laneWordRun {l : Launch} {g tid : Nat} (site : Fin 4) (hTid : tid < 512) :
    Seg kernel [] l g 1 (laneWord site).defined
      [((laneWord site).source, b32 ((laneWord site).input tid))]
      ((laneWord site).defined + 1)
      [((laneWord site).register, b32 ((laneWord site).output tid))] := by
  have h32 : tid < 4294967296 := by omega
  have h64 : tid < 18446744073709551616 := by omega
  have h32' : 8 * tid < 4294967296 := by omega
  have h64' : 8 * tid < 18446744073709551616 := by omega
  have hMul : tid * 8 = 8 * tid := Nat.mul_comm _ _
  have hAnd : 8 * tid &&& 56 = 8 * (tid % 8) := by
    have h := congrArg (fun n => n <<< 3) (Nat.and_two_pow_sub_one_eq_mod tid 3)
    change (tid &&& 7) <<< 3 = (tid % 8) <<< 3 at h
    rw [Nat.shiftLeft_and_distrib] at h
    simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm _ 8] using h
  fin_cases site <;> intro t ht <;>
    simp only [laneWord, LaneWord.input, LaneWord.output, Bool.false_eq_true,
      ↓reduceIte] at ht ⊢ <;>
    seg_fp ht using
      norm_bits [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32',
        Nat.mod_eq_of_lt h64', hMul, hAnd]

private def checkLaneWord (f : LaneWord) (pc : Nat) (ins : Instr) : Bool :=
  (!decide (f.live pc) || !(loaderRingWrites ins.op).contains f.register) &&
  (!decide (f.live (pc + 1)) || pc == f.defined || decide (f.live pc)) &&
  match ins.op with
  | .bra target _ => !decide (f.live target) || decide (f.live pc)
  | .brx .. => false
  | _ => true

private theorem laneCodeAt {pc : Nat} {ins : Instr} (hLo : 174 ≤ pc) (hHi : pc < 1901)
    (hCode : kernel.code[pc]? = some ins) (site : Fin 4) :
    (!(loaderRingWrites ins.op).contains 1061 &&
      checkLaneWord (laneWord site) pc ins) = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (i, n) => !(loaderRingWrites i.op).contains 1061 &&
      checkLaneWord (laneWord site) n i) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hCode]
  rfl

private theorem checkedLaneInput {l : Launch} {g : Nat} {s : TState}
    (hf : LoaderCopyLaneFrame l g s) (site : Fin 4) (hPc : s.pc = (laneWord site).defined) :
    s.regs (laneWord site).source = some (b32 ((laneWord site).input (g % l.block))) := by
  fin_cases site
  · exact hf.1
  · exact hf.2 0 (hPc.symm ▸ (show (laneWord 0).live 926 by decide))
  · exact hf.1
  · exact hf.2 2 (hPc.symm ▸ (show (laneWord 2).live 1389 by decide))

/-- Each returning loader step preserves the thread ID and all currently live
lane-column facts, including the two backedges of the steady packet loop. -/
theorem loaderCopyLaneFrameStep {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hShape : RingShape s)
    (hFrame : LoaderCopyLaneFrame l g s) (hw : WStep kernel Assumptions.all l g s e u) :
    LoaderCopyLaneFrame l g u := by
  refine ⟨?_, ?_⟩
  · apply Eq.trans _ hFrame.1
    apply loaderPipelineStepRegs hLo hHi _ hw
    intro i hc
    simpa using (Bool.and_eq_true_iff.mp (laneCodeAt hLo hHi hc 0)).1
  intro site hActive
  let f := laneWord site
  have decoded {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      checkLaneWord f s.pc i = true :=
    (Bool.and_eq_true_iff.mp (laneCodeAt hLo hHi hc site)).2
  have hKeep (hl : f.live s.pc) :
      u.regs f.register = some (b32 (f.output (g % l.block))) := by
    apply Eq.trans _ (hFrame.2 site hl)
    apply loaderPipelineStepRegs hLo hHi _ hw
    intro i hc
    have h := decoded hc
    simp only [checkLaneWord, Bool.and_eq_true, hl, decide_true, Bool.not_true, Bool.false_or]
      at h
    simpa using h.1.1
  have advance {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hNot : s.pc ≠ f.defined) (hPc : u.pc = s.pc + 1) : f.live s.pc := by
    have hn : f.live (s.pc + 1) := hPc ▸ hActive
    have h := decoded hc
    simp only [checkLaneWord, Bool.and_eq_true, hn, decide_true, Bool.not_true, Bool.false_or]
      at h
    have hEither : s.pc = f.defined ∨ f.live s.pc := by simpa using h.1.2
    exact hEither.resolve_left hNot
  rcases hw with ⟨_, ht⟩ | ⟨event, _, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc, hClean, _⟩ := Softmax.tauScoreSource ht
    by_cases hs : s.pc = f.defined
    · have hTid : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
      have hCode := laneWordCode site
      have hLocal : f.instruction.op.isLocal = true := by fin_cases site <;> rfl
      have hat := pipelineAtCut hs hShape
        (show Holds s.regs [(f.source, b32 (f.input (g % l.block)))] from
          ⟨checkedLaneInput hFrame site hs, trivial⟩)
        hClean ⟨_, hCode, hLocal⟩
      obtain ⟨t, hr, hT⟩ := laneWordRun site hTid s hat
      have hOne : tauStep kernel [] l g s = some t := by
        simpa [run] using hr
      have hSame : u = t := Option.some.inj ((tauStep_iff.mpr hCore).symm.trans hOne)
      rw [hSame]
      exact hT.2.2.2.2.1
    apply hKeep
    rcases tau_core_frame hc hCore with rfl | hNext
    · exact advance hc hs rfl
    have hPc := hNext.pc
    have hB := decoded hc
    cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
    case bra target uni =>
      change f.live u.pc at hActive
      rw [hPc] at hActive
      simp only [checkLaneWord, Bool.and_eq_true, hop, hActive, decide_true, Bool.not_true,
        Bool.false_or] at hB
      exact of_decide_eq_true hB.2
    case brx => simp [checkLaneWord, hop] at hB
    all_goals exact advance hc hs hPc
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hNot : s.pc ≠ f.defined := by
      intro hs
      have hCode := laneWordCode site
      rw [← hs] at hCode
      obtain rfl := Option.some.inj (hc.symm.trans hCode)
      have hl : f.instruction.op.isLocal = true := by fin_cases site <;> rfl
      rw [hl] at hLocal
      cases hLocal
    apply hKeep
    have hCore : EStep kernel [] l g s event (some u) := by
      obtain ⟨tmpl, hOut, hFire⟩ := he
      exact ⟨tmpl, by rwa [← loaderOutCore hLo (by omega)], hFire⟩
    rcases (estep_return_pc hCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact advance hc hNot h

/-- The warm K empty gate carries its real CTA-local column. -/
theorem LoaderCopyLaneFrame.warmColumn {l : Launch} {g : Nat} {s : TState}
    (h : LoaderCopyLaneFrame l g s) (hPc : s.pc = 957) :
    s.regs 1119 = some (b32 (8 * ((g % l.block) % 8))) :=
  h.2 1 (hPc.symm ▸ (show (laneWord 1).live 957 by decide))

/-- Each steady K gate carries the column initialized before the first steady packet. -/
theorem LoaderCopyLaneFrame.steadyColumn {l : Launch} {g : Nat} {s : TState}
    (h : LoaderCopyLaneFrame l g s) (hPc : s.pc = 1427) :
    s.regs 1147 = some (b32 (8 * ((g % l.block) % 8))) :=
  h.2 3 (hPc.symm ▸ (show (laneWord 3).live 1427 by decide))

/-- The steady V swizzle checkpoint keeps the same lane-column word as steady K. -/
theorem LoaderCopyLaneFrame.steadySwizzleColumn {l : Launch} {g : Nat} {s : TState}
    (h : LoaderCopyLaneFrame l g s) (hPc : s.pc = 1451) :
    s.regs 1147 = some (b32 (8 * ((g % l.block) % 8))) :=
  h.2 3 (hPc.symm ▸ (show (laneWord 3).live 1451 by decide))


end
end PTX.Kernels.TmlFa4Fwd.Loader
