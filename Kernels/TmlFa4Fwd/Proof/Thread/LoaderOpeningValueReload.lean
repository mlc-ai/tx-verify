-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueSecond
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVReload
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

private theorem primingVFirstReloadFromLastStore {l : Launch} {g word : Nat}
    {F : List (Nat × Value)}
    (hResidual : (1089,b32 word) ∈ F)
    (hKeep₀ : ((kernel.code.drop 800).take 2).all
      (fun ins => (((6,.pred false)::F).map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true)
    (hKeep₁ : ((kernel.code.drop 803).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    {s : TState} (hs : At s 800 ((6,.pred false)::F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧ At u 804 F := by
  let G := (6,.pred false)::F
  obtain ⟨t,ht,hT⟩ := primingVLoopSeed l g s (hs.mono trivial)
  obtain ⟨htA,hStable⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hs.1
    hKeep₀ (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hGT : Holds t.regs G :=
    holdsSchedulerFrame hs.2.2.2.2 hStable (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g) Flow.code_802
    false (hT.mono hGT) hGT.1 (by simp)
  have hwA := (loaderLinear (regs := []) (by decide) (by decide) hT.1
    (by simp) (by decide) hw).1
  have hF : Holds w.regs F := hW.2.2.2.2.2
  obtain ⟨u,hu,hU⟩ := primingVFirstReloadPrep (g := g) w
    (hW.mono ⟨holds_mem hF hResidual,trivial⟩)
  obtain ⟨huA,hRetain⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hW.1
    hKeep₁ (by decide) hu
  exact ⟨u,run_rtg (run_comp (run_comp htA hwA) huA),
    hU.mono (holdsSchedulerFrame hF hRetain (fun _ hm => List.mem_map_of_mem hm))⟩

/-- Both words of the first V pointer are read out of the same last local store. -/
def OpeningValueFirstPointerReloadedAt (p : Params) (l : Launch) (X : Execution)
    (g index batch head row : Nat) : Prop :=
  ∀ word : Fin 2, let site := primingVPointerReload 0
    X.get (g,index+word.val) = some ⟨site.pc,.rd (site.word g l.localBase word)
      (pointerReadBytes (primingVRowPointer p batch head row) word)⟩

/-- The first V broadcast issues from both actual reloaded words of the same lane. -/
structure OpeningValueReloadedLane (p : Params) (l : Launch) (X : Execution)
    (g i batch head row : Nat) (F : List (Nat × Value)) (endState : Option TState) : Prop where
  reloaded : OpeningValueFirstPointerReloadedAt p l X g i batch head row
  continuation : ∃ t, At t 805 (primingVReloadWords 0 (primingVRowPointer p batch head row) ++ F) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (i+2)) (some t) ∧
    Run kernel Assumptions.all l g t ((X.tr g).drop (i+2)) endState

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g i batch qHead tile row : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hh : qHead/6 < p.kvHeads) {ending : Option TState}
    (hBuilt : OpeningValuePointersStoredLane p l X g i batch (qHead/6) row
      (primingVAdmissionCarry p l batch qHead tile) ending)
include hp hMax hg hb hh hBuilt

/-- The real V replay reloads both words before its first pointer broadcast. -/
theorem openingValuePointerReloadWithFrameOfMaximal :
    OpeningValueReloadedLane p l X g (i+6) batch (qHead/6) row
      (primingVAdmissionCarry p l batch qHead tile) ending := by
  let F := primingVAdmissionCarry p l batch qHead tile
  let site := primingVPointerReload 0
  let base := primingVRowPointer p batch (qHead/6) row
  obtain ⟨s,hs,hPast,hTail⟩ := hBuilt.continuation
  have hRes : (1089,b32 (vPrimingResidual p batch tile)) ∈ F := by
    simp [F,primingVAdmissionCarry]
  obtain ⟨r,hr,hR⟩ := primingVFirstReloadFromLastStore hRes
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  have hAt : At r site.pc ((site.baseReg,b64 l.localBase)::F) := by
    refine hR.mono ⟨holds_mem hR.2.2.2.2 ?_,hR.2.2.2.2⟩
    simp [site,primingVPointerReload,F,primingVAdmissionCarry,primingVScratchAbi]
  have hHead := sourceScratchPayload_live hp 1
    (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide)) hh
  have hWidth : base < 2^64 := by
    obtain ⟨he,hFit,_⟩ := hHead
    rw [he] at hFit
    exact hFit
  have hFresh : ∀ pair ∈ F, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg := by
    intro pair hm
    have hCheck : (F.map Prod.fst).all
        (fun r => decide (r ≠ site.lowReg ∧ r ≠ site.highReg)) = true := by kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCheck _ (List.mem_map_of_mem hm))
  have hSaved : PrimingCellValue X g (i+6) 799 (site.cell g l.localBase) (b64 base).toBytes := by
    simpa only [site,base,SavedPointerReload.cell,primingVPointerReload,sourceScratchAccess,
      Fin.val_zero,Nat.mul_zero,Nat.add_zero,show kvLocalOffset 0 0 = 0 by decide]
      using hBuilt.latest 0
  have he : X.get (g,i+5) = some ⟨799,.wr (sourceScratchAccess l g 1)
      (b64 (primingVRowPointer p batch (qHead/6) (row+64))).toBytes⟩ := hBuilt.saved
  have hAddr : l.localBase+site.offset < 2^64 := by
    have := hp.localMemory.2.1
    change l.localBase+0 < 2^64
    omega
  have hAlign : (l.localBase+site.offset)%8 = 0 := by
    have := hp.localMemory.1
    change (l.localBase+0)%8 = 0
    omega
  obtain ⟨t,ht,hP,hT,hLow,hHigh⟩ := site.readOfMaximal hMax hg (by decide) Flow.code_804
    hAddr hAlign (by decide) hWidth hAt hFresh hr hPast hTail
    (len_of_get he) (releasedIfLast he (by intro h; cases h)) hSaved
  refine ⟨?_,t,ht,hP,hT⟩
  intro word
  have hWord : word = 0 ∨ word = 1 := by fin_cases word <;> simp
  rcases hWord with rfl | rfl
  · simpa only [site,base,Fin.val_zero,Nat.add_zero] using hLow
  · exact hHigh

end PTX.Kernels.TmlFa4Fwd.Loader
