-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitOutputSlots
public import Kernels.TmlFa4Fwd.Proof.Protocol.LseSingleVisit
public import Kernels.TmlFa4Fwd.Proof.Result.Post
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCoordinates
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

/-- Every covering output writer of a single-visit row carries the specified FP32 byte. -/
theorem singleVisitOutputByte {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {batch head row col k : Nat} (hb : batch < p.batch) (hh : head < p.heads)
    (hr : row < p.qLength batch) (hc : col < 128) (hk : k < 4)
    (hTrip : trips p batch (row/256) = 1) :
    OutputByte X ((p.oLoc (p.qOffset batch+row) head col).at k)
      ((Value.float .f32 (attention p batch head row col)).byteAt k) := by
  refine ⟨outputHasWriter hp hX hDone hFootprint hb hh hr hc hk, ?_⟩
  let loc := (p.oLoc (p.qOffset batch+row) head col).at k
  have hTarget := outputByte_in (hp.packedRow_lt hb hr) hh hc hk
  obtain ⟨hCuQ,_⟩ := hFootprint.metadataProtected hp
  intro writer a bytes hw hCover
  change a.Covers loc at hCover
  change p.oRegion.Contains loc at hTarget
  have hSpace : a.loc.space = .global := hCover.1.symm
  rcases Thread.globalWriteSource hX hw.intent hSpace with
    ⟨i,data,_,he⟩ | ⟨i,x,y,j,addr,spec,rfl,hIssue,hLoc,hSize⟩
  · obtain ⟨q,hq,h,hHead,hStore,hSize⟩ := Thread.lseWriteShape hp hX he hSpace
    let off := loc.addr-a.loc.addr
    have hOff : off < 4 := by
      have hBounds := hCover.2.2
      change a.loc.addr ≤ loc.addr ∧ loc.addr < a.loc.addr+a.size at hBounds
      unfold off
      omega
    have hByteLoc : loc = a.loc.at off := by
      have hBounds := hCover.2.2.1
      have hAddr : loc.addr = a.loc.addr+off := by unfold off; omega
      have hSpaces := hCover.1
      have hCtas := hCover.2.1
      rcases hLoc : loc with ⟨space,cta,addr⟩
      simp only [hLoc] at hAddr hSpaces hCtas
      unfold Loc.at
      rw [Loc.mk.injEq]
      exact ⟨hSpaces,hCtas,hAddr⟩
    rw [hStore] at hByteLoc
    exact (lseByte_apart_output hp hq hHead hOff (hByteLoc ▸ hTarget)).elim
  · have hDest := hLoc.trans (congrArg some (Acc.loc_of_one hCover hSize))
    obtain ⟨actual,ha,stage,box,hLo,hHi,rfl⟩ :=
      OutputWarp.issuedAssignment hp hX hIssue
    let coords := assignedCoordinates p actual (i.1/l.block)
    have hHead := (assignedCoordinates_valid hp hLo hHi).2
    obtain ⟨hx,hy,hj,hRow,hByteLoc⟩ :=
      Protocol.Output.writebackByteCoordinates hp ha hHead hDest
    let row' := stageRow coords.1 stage + y
    let col' := 32*box.val+x
    have hCol' : col' < 128 := by unfold col'; have := box.isLt; omega
    have hEq : (p.oLoc (p.qOffset batch+row) head col).at k =
        (p.oLoc (p.qOffset actual+row') coords.2 col').at j := by
      simpa only [row',col',coords,Nat.add_assoc] using hByteLoc
    obtain ⟨hPacked,hH,hC,hK⟩ := outputByte_inj hh hHead hc hCol' hk hj hEq
    obtain ⟨hBatch,hR⟩ := hp.packedRow_inj hb ha hr hRow hPacked
    subst actual
    have hTile : coords.1 = row/256 := by
      have hs := stage.isLt
      have hRowEq : row = 256*coords.1 + 128*stage.val+y := hR
      omega
    obtain ⟨rfl,hReady⟩ := Thread.Output.readyOfWritebackSpec hp hX stage box hIssue
    have hSlot := Protocol.Output.singleVisitAttentionSlot hp hX hDone hFootprint
      hb hLo hHi (hTile.symm ▸ hTrip) hRow hx hy hj hIssue hReady
    obtain ⟨o,stored,byte,ho,hActual,hWriteLoc,hWritten,_,hBytes,_,_,_,_⟩ := hw
    have hObserved := Protocol.Output.OrderedSlot.writeByte hX hIssue ho hWritten hSlot
    have hOut : wbyte a bytes loc = some byte := by
      rw [hBytes,wbyte,Acc.loc_of_one hCover hSize,Nat.sub_self]
      rfl
    rw [hOut,hObserved]
    change some ((Value.float .f32 (attention p batch coords.2 row' col')).byteAt j) = _
    have hR' : row = row' := hR
    have hH' : head = coords.2 := hH
    rw [← hR',← hH',← hC,← hK]

/-- The recorded output bytes still to verify are those of tiles with repeated visits. -/
def RepeatedOutputValues (p : Params) (X : Execution) : Prop :=
  ∀ batch < p.batch, ∀ head < p.heads, ∀ row < p.qLength batch,
    trips p batch (row / 256) ≠ 1 →
    ∀ col < 128, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
    a.Covers ((p.oLoc (p.qOffset batch + row) head col).at k) →
    wbyte a bytes ((p.oLoc (p.qOffset batch + row) head col).at k) =
      some ((Value.float .f32 (attention p batch head row col)).byteAt k)

/-- The verified single-visit rows and the repeated-visit outputs cover every valid row. -/
theorem outputValuesOfRepeatedVisits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    (hValues : RepeatedOutputValues p X) : OutputValues p X := by
  intro batch hb head hh row hr col hc k hk
  by_cases hSingle : trips p batch (row / 256) = 1
  · exact (singleVisitOutputByte hp hX hDone hFootprint hb hh hr hc hk hSingle).2
  · exact hValues batch hb head hh row hr hSingle col hc k hk

end
end PTX.Kernels.TmlFa4Fwd.Result
