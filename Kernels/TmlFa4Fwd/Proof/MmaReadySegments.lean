-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyIntervals
public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzero
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Loader Prologue Epilogue

noncomputable section

def readyFrame (l : Launch) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 12)]

def readyWord (use : Nat) : Nat := MbarRing.Index.round 3 use % 2

theorem readyWord_lt (use : Nat) : readyWord use < 2 := Nat.mod_lt _ (by decide)

theorem loaderPhaseWord_ready (use : Nat) : loaderPhaseWord (readyParity use) =
    b32 (readyWord use) := by
  have h := readyWord_lt use
  change b32 (if decide (readyWord use = 1) then 1 else 0) = b32 (readyWord use)
  interval_cases hWord : readyWord use <;> simp_all

def ringFrame (l : Launch) (r q use : Nat) : List (Nat × Value) :=
  (r, b32 (readyStage use).val) :: (q, b32 (readyWord use)) :: readyFrame l

/-- The first ready request starts at parity zero. -/
theorem readyInitialPhase (l : Launch) (g : Nat) :
    Seg kernel Assumptions.all l g 1 2140 (readyFrame l) 2141
      ((2536, b32 0) :: readyFrame l) := by
  intro t ht
  dsimp only [readyFrame] at ht ⊢
  seg_fp ht using decide

/-- The fixed first ready wait addresses slot zero. -/
theorem readyInitialAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel Assumptions.all l g 1 2144 ((2536, b32 0) :: readyFrame l) 2145
      ((2537, b32 (l.sharedBase + 32)) :: (2536, b32 0) :: readyFrame l) := by
  intro t ht
  let u := next (setReg t 2537 (b32 (l.sharedBase + 32)))
  have hr := evalSharedAdd (g := g) ht.1 ht.2.2.2.1 ht.2.2.2.2.2.1
    (show l.sharedBase + 32 < 2 ^ 32 by have := hp.shared.2.1; omega) Flow.code_2144
  refine ⟨u, localRun (by decide) (by decide) ht.1 rfl (by simpa [run] using hr), ?_⟩
  exact ht.set (by simp [readyFrame])

/-- Both steady and short paths start from logical use one after the first wait. -/
theorem readySeedShort (l : Launch) (g : Nat) :
    Seg kernel Assumptions.all l g 4 2280 (readyFrame l) 2284 (ringFrame l 7207 7208 1) := by
  intro t ht
  dsimp only [readyFrame, ringFrame, readyStage, readyWord, MbarRing.Index.slot,
    MbarRing.Index.round] at ht ⊢
  seg_fp ht using decide

theorem readySeedSteady (l : Launch) (g : Nat) :
    Seg kernel Assumptions.all l g 4 2287 (readyFrame l) 2291 (ringFrame l 7207 7208 1) := by
  intro t ht
  dsimp only [readyFrame, ringFrame, readyStage, readyWord, MbarRing.Index.slot,
    MbarRing.Index.round] at ht ⊢
  seg_fp ht using decide

/-- Framing the decoded cursor steps retains the shared base and warp role. -/
theorem readyAdvanceFramed (l : Launch) (g : Nat) (i : Fin 2) (use : Nat) :
    let site := readyAdvanceSite i
    Seg kernel Assumptions.all l g 5 site.1
      (ringFrame l site.2.1.1 site.2.1.2 use) (site.1 + 5)
      (ringFrame l site.2.2.1 site.2.2.2 (use + 1)) := by
  dsimp only
  let site := readyAdvanceSite i
  have hCore : ∀ stage : Fin 3, ∀ phase : Bool, Seg kernel [] l g 5 site.1
      ((site.2.1.1, b32 stage.val) :: (site.2.1.2, loaderPhaseWord phase) :: readyFrame l)
      (site.1 + 5)
      ((site.2.2.1, b32 ((stage.val + 1) % 3)) ::
        (site.2.2.2, loaderPhaseWord (loaderNextPhase stage phase)) :: readyFrame l) := by
    intro stage phase
    dsimp only [site]
    fin_cases i <;> fin_cases stage <;> cases phase <;> intro t ht <;>
      simp only [readyAdvanceSite, loaderPhaseWord, loaderNextPhase, readyFrame] at ht ⊢ <;>
      seg_fp ht using decide
  have hStraight : ((kernel.code.drop site.1).take (5 - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  intro t ht
  have hSeg := hCore (readyStage use) (readyParity use)
  rw [← readyStage_succ, ← readyParity_succ, loaderPhaseWord_ready, loaderPhaseWord_ready] at hSeg
  obtain ⟨u, hu, hf⟩ := hSeg t ht
  exact ⟨u, localRun (by fin_cases i <;> decide) (by fin_cases i <;> decide) ht.1 hStraight hu, hf⟩

/-- Three identical address-calculation templates consume the live ring index. -/
structure ReadyAddressSite where
  pc : Nat
  slotReg : Nat
  phaseReg : Nat
  byteReg : Nat
  indexedReg : Nat
  readyReg : Nat

def readyAddressSite : Fin 3 → ReadyAddressSite
  | 0 => ⟨2291, 7207, 7208, 2575, 1191, 2568⟩
  | 1 => ⟨2349, 1192, 2572, 2586, 1193, 2571⟩
  | 2 => ⟨2542, 7207, 7208, 2619, 1194, 2609⟩

def readyAddr (l : Launch) (use : Nat) : Nat :=
  l.sharedBase + (8 * (readyStage use).val + 32)

private theorem readyAddrCode (i : Fin 3) :
    let s := readyAddressSite i
    kernel.code[s.pc + 1]? = some ⟨none, .int ⟨.add, .int .s 32, false,
      [some s.indexedReg], [.reg 2535, .reg s.byteReg]⟩⟩ ∧
    kernel.code[s.pc + 2]? = some ⟨none, .int ⟨.add, .int .s 32, false,
      [some s.readyReg], [.reg s.indexedReg, .imm 32]⟩⟩ := by
  fin_cases i
  · exact ⟨Flow.code_2292, Flow.code_2293⟩
  · exact ⟨Flow.code_2350, Flow.code_2351⟩
  · exact ⟨Flow.code_2543, Flow.code_2544⟩

private theorem addB32 {l : Launch} {g pc dst base a b : Nat} {rhs : Opnd} {t : TState}
    {F : List (Nat × Value)} (ht : At t pc F) (ha : t.regs base = some (b32 a))
    (hValue : readValue l g t 32 rhs = .ok (b32 b))
    (hb : readBits l g t 32 rhs = .ok (BitVec.ofNat 64 b)) (hBound : a + b < 2 ^ 32)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      [.reg base, rhs]⟩⟩)
    (hLocal : rhs.varying? = none) :
    run kernel [] l g 1 t = some (next (setReg t dst (b32 (a + b)))) := by
  have hReg : (Opnd.reg base).varying? = none := rfl
  apply run_local hc (by simp [Op.isLocal, Op.varyingSregs, hReg, hLocal]) ht
  rw [execLocalA_nil, execLocal_int rfl]
  have hA : readValue l g t 32 (.reg base) = .ok (b32 a) := by
    simp [readValue, readReg, ha, pure, Except.pure]
  simp only [execInt, DType.width, hA, hValue, readBits_b32 ha (by omega),
    hb, b32, bind, Except.bind, pure, Except.pure]
  rw [← BitVec.ofNat_add, truncBits_ofNat hBound (by decide)]

theorem readyAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat)
    (i : Fin 3) (use : Nat) :
    let s := readyAddressSite i
    Seg kernel Assumptions.all l g 3 s.pc (ringFrame l s.slotReg s.phaseReg use) (s.pc + 3)
      ((s.readyReg, b32 (readyAddr l use)) :: ringFrame l s.slotReg s.phaseReg use) := by
  dsimp only
  let site := readyAddressSite i
  let stage := readyStage use
  let F := ringFrame l site.slotReg site.phaseReg use
  have hShift (slot : Fin 3) :
      let facts := (site.slotReg, b32 slot.val) :: (site.phaseReg, b32 (readyWord use)) ::
        readyFrame l
      Seg kernel [] l g 1 site.pc facts (site.pc + 1)
        ((site.byteReg, b32 (8 * slot.val)) :: facts) := by
    dsimp only
    intro t ht
    fin_cases i <;> fin_cases slot <;>
      dsimp only [site, readyAddressSite, readyFrame] at ht ⊢ <;> seg_fp ht using decide
  have hBound : l.sharedBase + (8 * stage.val + 32) < 2 ^ 32 := by
    have h := hp.shared.2.1
    have hSlot := stage.isLt
    omega
  have hPacked : ∀ r ∈ F.map Prod.fst, r ≠ site.readyReg ∧ r ≠ site.indexedReg := by
    fin_cases i <;> simp [F, ringFrame, readyFrame, site, readyAddressSite]
  intro t ht
  obtain ⟨u, hu, hU⟩ := hShift stage t ht
  have hBase : u.regs 2535 = some (b32 l.sharedBase) := hU.2.2.2.2.2.2.2.1
  have hByte : u.regs site.byteReg = some (b32 (8 * stage.val)) := hU.2.2.2.2.1
  let v := next (setReg u site.indexedReg (b32 (l.sharedBase + 8 * stage.val)))
  have hv : run kernel [] l g 1 u = some v :=
    addB32 hU hBase (by simp [readValue, readReg, hByte, pure, Except.pure])
      (readBits_b32 hByte (by omega)) (by omega) (readyAddrCode i).1 rfl
  have hV := hU.set (r := site.indexedReg) (v := b32 (l.sharedBase + 8 * stage.val)) (by
    intro pair hp
    rcases List.mem_cons.mp hp with rfl | hp
    · fin_cases i <;> simp [site, readyAddressSite]
    · exact (hPacked _ (List.mem_map_of_mem hp)).2)
  have hAt : At v (site.pc + 2) ((site.indexedReg, b32 (l.sharedBase + 8 * stage.val)) :: F) :=
    ⟨hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.2⟩
  let w := next (setReg v site.readyReg (b32 (l.sharedBase + 8 * stage.val + 32)))
  have hw : run kernel [] l g 1 v = some w :=
    addB32 hAt hAt.2.2.2.2.1
      rfl rfl
      (by omega) (readyAddrCode i).2 rfl
  have hW := hAt.set (r := site.readyReg) (v := b32 (l.sharedBase + 8 * stage.val + 32)) (by
    intro pair hp
    rcases List.mem_cons.mp hp with rfl | hp
    · fin_cases i <;> simp [site, readyAddressSite]
    · exact (hPacked _ (List.mem_map_of_mem hp)).1)
  have hStraight : ((kernel.code.drop site.pc).take (3 - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  refine ⟨w, localRun (by fin_cases i <;> decide) (by fin_cases i <;> decide) ht.1 hStraight
    (run_comp (run_comp hu hv) hw), hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, ?_⟩
  exact ⟨by simpa only [readyAddr, ← Nat.add_assoc] using hW.2.2.2.2.1, hW.2.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
