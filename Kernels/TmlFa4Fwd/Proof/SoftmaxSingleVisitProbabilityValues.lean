-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilitySource
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbabilityOperandValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitObservedRound
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitEarlyProbabilityHandoff
import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitTailProbabilityHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX Prologue Epilogue Thread PTX.TcMma

/-- The actual PV operand of a single-visit tile reads the corresponding BF16
probability byte of the selected row, including both probability packets. -/
theorem singleVisitProbabilityOperandByte {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (hWarp : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRow : 128 * (2 * (assignedCoordinates p batch (g/l.block)).1 +
      (stageOf ⟨warpIndex l g,hWarp⟩).val) + (g%l.block)%128 < p.qLength batch)
    {i : EvId} {frag : Fin 8} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : PvInstruction X i (firstPvBlock false (stageOf ⟨warpIndex l g,hWarp⟩))
      frag d op acc mask)
    (hCta : g/l.block = i.1/l.block)
    {k byte : Nat} (hk : k < 16) (hByte : byte < 2)
    {operands : AsyncCopy.MmaOperands} (hOperands : X.async.mmaOperands i = some operands) :
    let coords := assignedCoordinates p batch (g/l.block)
    let stage := stageOf ⟨warpIndex l g,hWarp⟩
    let row := 128 * (2 * coords.1 + stage.val) + (g%l.block)%128
    let weight := shiftedWeight p batch coords.2 row (16*frag.val+k) (firstReference p batch
      coords.2 row 1)
    operands.a[Mma.qkByteIndex (tmemRow l g).val k byte]? =
      some (some ((Value.float .bf16 weight).byteAt byte)) := by
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  let stage := stageOf warp
  let coords := assignedCoordinates p batch (g/l.block)
  let row := 128 * (2 * coords.1 + stage.val) + (g%l.block)%128
  let weights := fun n =>
    shiftedWeight p batch coords.2 row n (firstReference p batch coords.2 row 1)
  let q := pvQuarter frag
  let index : Fin 32 := ⟨2*k+byte,by omega⟩
  let word := 8*(frag.val%2) + index.val/4
  have hWord : word < 16 := by
    have hHalf := Nat.mod_lt frag.val (show 0 < 2 by decide)
    dsimp [word,index]
    omega
  obtain ⟨j,producer,commit,wait,hPhase,hRound⟩ :=
    singleVisitObservedFirstRoundWithPhase hp hX hDone hFrame hWarp hb hLo hHi hTrip hRow hg
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨output,spec,hOutput,hOutCta⟩ :=
    secondOutputCommitOfCompletedWork hp hX hDone hg hWork
  obtain ⟨_,_,hDesc,hOpCta,_⟩ := hPv.valueOperand hp hX
  have hOpCta := hOpCta.trans hCta.symm
  have hMma : X.MmaIssue i d op acc mask := ⟨_,hPv.decoded⟩
  have hStores := hRound
  obtain ⟨_,_,_,_,_,_,hPublication,_⟩ := hStores
  let packedFor (q : Fin 4) := (List.range 16).map (probabilityWord (fun i => weights (32*q.val+i)))
  have hExact (q : Fin 4) : X.get (g,j+1+probabilityTraceIndex q) =
      some ⟨probabilityPc .first q,
        .tc (.st (probabilityAddress l g stage q) (packedFor q) .s32x32b)⟩ := by
    have hKey (k : Nat) : visitKey 1 0 k = k := by simp [visitKey]
    simp only [hKey] at hPublication
    fin_cases q
    · exact hPublication 1
    · exact hPublication 2
    · exact hPublication 3
    · exact hPublication 6
  let packed := packedFor q
  have he := hExact q
  have hLen : packed.length = 16 := by simp [packed,packedFor]
  have hBefore : StoreDoneBefore l X (g,j+1+probabilityTraceIndex q) i := by
    have hBound := q.isLt
    by_cases hEarly : q.val < 3
    · exact Protocol.Scores.singleVisitEarlyProbabilityStoreDoneBeforePv
        hp hX hDone hFrame hg hWarp hb hLo hHi hTrip hRound hPv hCta q hEarly
    · have hLast : q = 3 := Fin.ext (show q.val = 3 by omega)
      have hLate : 6 ≤ frag.val := by
        have hQ : frag.val/2 = 3 := congrArg Fin.val hLast
        omega
      rw [hLast]
      exact Protocol.Scores.singleVisitTailProbabilityStoreDoneBeforePv
        hp hX hDone hFrame hg rfl hb hLo hHi hTrip hRound hPv hLate hCta
  have hAddr := hPv.tailProbabilityAddress hp hX stage
  have hCell := pvFromProbability hDesc hOpCta stage frag index hAddr
  have hAccess : X.MmaACell i
      (tcDataCell l g .s32x32b (probabilityAddress l g stage q) word) :=
    ⟨d,op,acc,mask,_,_,hMma,hCell⟩
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hLenK := (hp.lengths batch hb).2
  have hRead := singleVisitProbabilityReadSource hp hX hDone hFrame hg rfl hb hLo hHi hTrip
    (by omega) (by omega) (by omega) hRound hPhase hOutput hOutCta q hWord hLen he
    hMma hBefore hAccess
  exact probabilityOperandByteOfStore hX stage frag weights hk hByte hMma hDesc hOpCta hAddr
    rfl ⟨_,he⟩ hOperands hRead

end PTX.Kernels.TmlFa4Fwd.Softmax
