-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDrainWords
import Kernels.TmlFa4Fwd.Proof.MmaFallbackEntry
import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

inductive MmaCuQGroup where
  | fallback
  | drain

namespace MmaCuQGroup

def scan : MmaCuQGroup → GroupScan
  | .fallback => .select
  | .drain => .drain

def site (kind : MmaCuQGroup) : ScanSite := scanSite kind.scan

def readSite (kind : MmaCuQGroup) : Nat := kind.site.head + 11

def ordReg : MmaCuQGroup → Nat
  | .fallback => 1184
  | .drain => 1198

private def predReg : MmaCuQGroup → Nat
  | .fallback => 348
  | .drain => 421

private def addrReg : MmaCuQGroup → Nat
  | .fallback => 7879
  | .drain => 7886

def dstReg : MmaCuQGroup → Nat
  | .fallback => 7195
  | .drain => 7211

def facts (kind : MmaCuQGroup) (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  groupScanFacts kind.scan first p.batch (g/l.block) ++ drainRoots p l g

private theorem prepareGate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (kind : MmaCuQGroup) (g : Nat) {first : Nat} (hFirst : first ≤ p.batch) :
    let ix := first + laneOf l g
    Seg kernel [] l g 3 (kind.site.head+5)
      [(kind.site.advanced,b32 first),(1180,b32 (laneOf l g)),(kind.site.batch,b32 p.batch)]
      (kind.site.head+8) [(kind.ordReg,b32 ix),(kind.predReg,.pred (decide (p.batch < ix)))] := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  cases kind
  · dsimp only [site,scan,scanSite,ordReg,predReg]
    intro t ht
    obtain ⟨u,hr,hu⟩ := fallbackCuQReadGate hp g hFirst hLane t ht
    exact ⟨u,hr,hu.mono ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.1,trivial⟩⟩
  · dsimp only [site,scan,scanSite,ordReg,predReg]
    intro t ht
    have hShape := hp.shape.2.2.2.2.2
    have hb := hp.shape.2.1
    have hi : first+laneOf l g < 2^31 := by omega
    have hi32 : first+laneOf l g < 2^32 := by omega
    have hf32 : first < 2^32 := by omega
    have hl32 : laneOf l g < 2^32 := by omega
    have hb32 : p.batch < 2^32 := by omega
    seg_fp ht using
      simp only [b32, ← BitVec.ofNat_add, truncBits_ofNat hf32 (by decide),
          truncBits_ofNat hl32 (by decide), truncBits_ofNat hi32 (by decide),
          truncBits_ofNat hb32 (by decide), compare, Option.getD_some,
          signedWord hi, signedWord hb, Int.ofNat_lt, gt_iff_lt]

private theorem gateInstr (kind : MmaCuQGroup) :
    kernel.code[kind.site.head+8]? =
      some ⟨some (kind.predReg,false), .bra (kind.readSite+1) false⟩ := by
  cases kind
  · exact Flow.code_1996
  · exact Flow.code_2704

private theorem gateRootsUnwritten (kind : MmaCuQGroup) :
    (((kernel.code.drop (kind.site.head+5)).take 3).all
      (fun i => ([kind.site.base,kind.site.batch,kind.site.sentinel,kind.site.cta,
        1180,7506,1072]).all (fun r => !(writesRegs i.op).contains r))) = true := by
  cases kind <;> decide +kernel

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (kind : MmaCuQGroup)
include hp kind

theorem readGate {g first : Nat} (hFirst : first ≤ p.batch) {s : TState}
    (hs : At s (kind.site.head+5) ((kind.site.advanced,b32 first)::kind.facts p l g first)) :
    let ix := first + laneOf l g
    ∃ u, run kernel Assumptions.all l g 4 s = some u ∧
      At u (if p.batch < ix then kind.readSite+1 else kind.readSite-2)
        ((kind.ordReg,b32 ix)::kind.facts p l g first) := by
  let ix := first + laneOf l g
  let F := kind.facts p l g first
  have hSaved := hs.2.2.2.2.2
  have hP : At s (kind.site.head+5) [(kind.site.advanced,b32 first),
      (1180,b32 (laneOf l g)),(kind.site.batch,b32 p.batch)] := by
    apply hs.mono
    refine ⟨hs.2.2.2.2.1,holds_mem hSaved ?_,holds_mem hSaved ?_,trivial⟩
    · simp [facts,drainRoots]
    · simp [facts,groupScanFacts,site]
  obtain ⟨t,ht,hT⟩ := prepareGate hp kind g hFirst s hP
  have hStraight : ((kernel.code.drop (kind.site.head+5)).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by cases kind <;> decide +kernel
  have hKeep : Holds t.regs F := by
    apply holdsSchedulerFrame hSaved
      (fun _ hr => schedulerLocalFrame (gateRootsUnwritten kind) hStraight ht hs.1.ge
        (by rw [hs.1]) hr)
    intro x hx
    have h := List.mem_map_of_mem (f := Prod.fst) hx
    simpa [F,facts,groupScanFacts,drainRoots,site] using h
  have hFrame : At t (kind.site.head+8) ((kind.ordReg,b32 ix)::F) :=
    hT.mono ⟨hT.2.2.2.2.1,hKeep⟩
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    (gateInstr kind) (decide (p.batch < ix)) hFrame hT.2.2.2.2.2.1 (by simp)
  have hs₁ : 1904 ≤ kind.site.head+5 := by cases kind <;> decide
  have hs₂ : kind.site.head+5+3 ≤ 2768 := by cases kind <;> decide
  have hs₃ : 1904 ≤ kind.site.head+8 := by cases kind <;> decide
  have hs₄ : kind.site.head+8+1 ≤ 2768 := by cases kind <;> decide
  have hPc : kind.site.head+8+1 = kind.readSite-2 := by cases kind <;> decide
  refine ⟨u,run_comp (localRun hs₁ hs₂ hs.1 hStraight ht)
    (localRun hs₃ hs₄ hFrame.1 rfl hu),?_⟩
  simpa only [decide_eq_true_eq,hPc] using hU

private theorem addressCore (g : Nat) {index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 (kind.readSite-2) [(kind.ordReg,b32 index),(7506,b64 p.cuQBase)]
      kind.readSite [(kind.addrReg,b64 (p.cuQBase+4*index))] := by
  cases kind
  · exact fallbackCuQReadAddress hp g hi
  · dsimp [readSite,site,scan,scanSite,ordReg,addrReg]
    intro t ht
    have hb := hp.shape.2.1
    have hRegion := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRegion
    have h31 : index < 2^31 := by omega
    have h32 : index < 2^32 := by omega
    have hBase : p.cuQBase < 2^64 := by omega
    have hOff : 4*index < 2^64 := by omega
    have hAddr : p.cuQBase+4*index < 2^64 := by omega
    have hFour : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
    have hProduct : (index : Int)*4 = ((4*index : Nat) : Int) := by push_cast; omega
    seg_fp ht using simp only [b64,kind_s_beq_s,↓reduceIte,hFour,signedWord h31,
      truncBits_ofNat h32 (by decide),truncBits_ofNat hOff (by decide),
      truncBits_ofNat hBase (by decide),hProduct,BitVec.ofInt_natCast,← BitVec.ofNat_add,
      truncBits_ofNat hAddr (by decide)]

private theorem loadOut {g index : Nat} {s : TState} (hi : index ≤ p.batch)
    (hs : At s kind.readSite [(kind.addrReg,b64 (p.cuQBase+4*index))]) :
    out kernel Assumptions.all l g s =
      .ev (.read {loc := globalLoc (p.cuQBase+4*index),size := 4} (afterLoad s [kind.dstReg])) := by
  cases kind
  · exact fallbackCuQReadOut hp hi hs
  · have hRegion := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hRegion
    have hSum : p.cuQBase+4*index < 2^64 := by omega
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    rw [out_eq_core (by rw [hs.1]; decide) (by rw [hs.1]; decide),
      out_event hs.2.2.2.1 (by rw [hs.1]; exact Flow.code_2707) rfl rfl]
    change Out.ev (loadTmpl [] l g s .global false 32 [7211] 7886 0) = _
    exact congrArg Out.ev (loadTmpl_global (t := s) (w := 32)
      hs.2.1 hs.2.2.2.2.1 hSum (by decide) (by omega))

theorem readAddress {g first : Nat} {s : TState} (hi : first+laneOf l g ≤ p.batch)
    (hs : At s (kind.readSite-2) ((kind.ordReg,b32 (first+laneOf l g))::kind.facts p l g first)) :
    ∃ u, run kernel Assumptions.all l g 2 s = some u ∧
      At u kind.readSite (kind.facts p l g first) ∧
      out kernel Assumptions.all l g u =
        .ev (.read {loc := globalLoc (p.cuQBase+4*(first+laneOf l g)),size := 4}
          (afterLoad u [kind.dstReg])) := by
  have hAt : At s (kind.readSite-2) [(kind.ordReg,b32 (first+laneOf l g)),
      (7506,b64 p.cuQBase)] := hs.mono ⟨hs.2.2.2.2.1,
        holds_mem hs.2.2.2.2.2 (by simp [facts,drainRoots]),trivial⟩
  obtain ⟨u,hu,hU⟩ := addressCore hp kind g hi s hAt
  have hStraight : ((kernel.code.drop (kind.readSite-2)).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by cases kind <;> decide +kernel
  have hWrites : ((kernel.code.drop (kind.readSite-2)).take 2).all
      (fun i => ((kind.facts p l g first).map Prod.fst).all
        (fun r => !(writesRegs i.op).contains r)) = true := by
    simp only [facts,groupScanFacts,drainRoots,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append]
    cases kind <;> decide +kernel
  have hKeep := holdsSchedulerFrame hs.2.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hu hs.1.ge (by rw [hs.1]) hr)
    (fun _ hx => List.mem_map_of_mem hx)
  exact ⟨u,localRun (by cases kind <;> decide) (by cases kind <;> decide)
    hs.1 hStraight hu,hU.mono hKeep,loadOut hp kind hi hU⟩

end MmaCuQGroup
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
