-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaRead
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! Semantic frame for async extensions that preserve existing Tensor Memory
sources and observations. Result transport is proved by structural induction. -/
namespace PTX.TcMma
noncomputable section
structure SemanticFrame (L : Launch) (X Y : Execution) : Prop where
  get : ∀i,Y.get i=X.get i
  operands : ∀i,Y.async.mmaOperands i=X.async.mmaOperands i
  history : Y.tmemHistory=X.tmemHistory
  pairing : Y.tmemPairing=X.tmemPairing
  happens : ∀i j,baseCausality L Y i j ↔ baseCausality L X i j
  observed : ∀i j acq ws,
    AsyncCopy.AsyncObserved Y i .mmaDone j acq ws ↔ AsyncCopy.AsyncObserved X i .mmaDone j acq ws
  mbarExec : ∀i j,MbarExec L Y i j ↔ MbarExec L X i j

variable {L : Launch} {A : List Assumption} {X Y : Execution}
namespace SemanticFrame
variable (f : SemanticFrame L X Y)
include f

theorem symm : SemanticFrame L Y X :=
  ⟨fun i => (f.get i).symm,fun i => (f.operands i).symm,f.history.symm,f.pairing.symm,
    fun i j => (f.happens i j).symm,fun i j acq ws => (f.observed i j acq ws).symm,
    fun i j => (f.mbarExec i j).symm⟩

theorem tcSame : TcSame L X Y := ⟨f.get,f.happens,f.mbarExec,f.observed⟩

theorem tcBefore (i j : EvId) : TcBefore L Y i j ↔ TcBefore L X i j := f.tcSame.tcBefore i j

theorem issue (i : EvId) (d : Nat) (s : OperandSpec) (acc : Bool) (mask : List Nat) :
    Y.MmaIssue i d s acc mask ↔ X.MmaIssue i d s acc mask := by
  simp only [Execution.MmaIssue,f.get]

theorem load (i : EvId) (d : Nat) (vals : List Value) (sh : TcShape) :
    Y.TLd i d vals sh ↔ X.TLd i d vals sh := by
  simp only [Execution.TLd,f.get]

theorem store (i : EvId) (cell : Cell) (v : Value) :
    StoreValue L Y i cell v ↔ StoreValue L X i cell v := by
  simp only [StoreValue,Execution.TSt,f.get]

theorem copy (i : EvId) (cell : Cell) (v : Value) :
    CpValue Y i cell v ↔ CpValue X i cell v := by
  simp only [CpValue,Execution.CpIssue,f.get,f.operands]

theorem shift (i : EvId) (cell : Cell) : ShiftCell Y i cell ↔ ShiftCell X i cell := by
  simp only [ShiftCell, Execution.ShiftIssue, f.get]

theorem shiftRead (i : EvId) (cell : Cell) :
    ShiftReadCell Y i cell ↔ ShiftReadCell X i cell := by
  simp only [ShiftReadCell, Execution.ShiftIssue, f.get]

theorem writer (i : EvId) (cell : Cell) :
    TmemWrite L Y i cell ↔ TmemWrite L X i cell := by
  simp only [TmemWrite,Execution.MmaCell,f.issue,StoreCell,Execution.TSt,CpCell,
    Execution.CpIssue,f.get,f.shift]

theorem done (i j : EvId) :
    DoneBefore L Y i j ↔ DoneBefore L X i j := f.tcSame.doneBefore i j

theorem completed (i j : EvId) :
    CompletedBefore L Y i j ↔ CompletedBefore L X i j := by
  simp only [CompletedBefore,WaitBefore,Execution.TLd,Execution.TSt,Execution.TcAsync,
    Execution.CpIssue,Execution.ShiftIssue,f.issue,f.get,f.tcBefore,f.done]

theorem before (i j : EvId) :
    Before L Y i j ↔ Before L X i j := by
  simp only [Before,f.done,Pipelined,f.tcBefore,f.issue]

theorem writeBefore (i j : EvId) :
    WriteBefore L Y i j ↔ WriteBefore L X i j := by
  simp only [WriteBefore,f.before,StoreDoneBefore,WaitBefore,Execution.TSt,Execution.TLd,Pipelined,
    Execution.CpIssue,f.get,f.tcBefore,f.issue]

theorem covers (r : Tmem.Pair.Requests) (owner : Nat) (e : EvId) (col : Nat) :
    Tmem.Pair.Covers L Y r owner e col ↔ Tmem.Pair.Covers L X r owner e col := by
  simp only [Tmem.Pair.Covers,Tmem.Pair.PairAllocBefore,f.happens,f.pairing]

theorem release (r : Tmem.Pair.Requests) (e : EvId) :
    Tmem.Pair.ReleaseOf L Y r e ↔ Tmem.Pair.ReleaseOf L X r e := by
  simp only [Tmem.Pair.ReleaseOf,Tmem.Pair.OwnRelease,f.get,f.history,f.pairing]

theorem readBefore (k : TmemRead) (e w : EvId) :
    ReadBefore L Y k e w ↔ ReadBefore L X k e w := by
  cases k <;>
    simp only [ReadBefore,f.done,Pipelined,f.tcBefore,f.issue,Execution.CpIssue,
      f.get,WaitBefore,Execution.TLd,Execution.TSt]

theorem sourceLive (source consumer : EvId) (cell : Cell) :
    SourceLive L Y source consumer cell ↔ SourceLive L X source consumer cell := by
  simp only [SourceLive,f.history,f.covers,f.release,f.completed,f.happens]

theorem readSource (k : TmemRead) (source e : EvId) (cell : Cell) :
    ReadSource L Y k source e cell ↔ ReadSource L X k source e cell := by
  simp only [ReadSource,f.writer,f.writeBefore,f.readBefore,f.sourceLive]

theorem result_map {i : EvId} {cell : Cell} {value : Value}
    (h : Result L A Y i cell value) : Result L A X i cell value := by
  induction h with
  | overwrite hi hp hr hv =>
    exact .overwrite ((f.issue ..).mp hi) hp (by simpa only [f.operands] using hr) hv
  | accumulate hi hp hr _ hs hv ih =>
    exact .accumulate ((f.issue ..).mp hi) hp (by simpa only [f.operands] using hr)
      ih ((f.readSource ..).mp hs) hv
  | accumulateStored hi hp hr hs ho hv =>
    exact .accumulateStored ((f.issue ..).mp hi) hp (by simpa only [f.operands] using hr)
      ((f.store ..).mp hs) ((f.readSource ..).mp ho) hv

theorem result (i : EvId) (cell : Cell) (v : Value) :
    Result L A Y i cell v ↔ Result L A X i cell v :=
  ⟨f.result_map,f.symm.result_map⟩

theorem shiftValue (A : List Assumption) (i : EvId) (cell : Cell) (v : Value) :
    ShiftValue L A Y i cell v ↔ ShiftValue L A X i cell v := by
  simp only [ShiftValue,ShiftSource,f.shift,f.shiftRead,f.readSource,f.result,f.store,f.copy]

theorem wrote (i : EvId) (cell : Cell) (v : Value) :
    Wrote L A Y i cell v ↔ Wrote L A X i cell v := by
  simp only [Wrote,f.result,f.store,f.copy,f.shiftValue]

theorem readOk : ReadOk L A Y ↔ ReadOk L A X := by
  simp only [ReadOk,LoadReadOk,AReadOk,LoadCell,f.load,f.readSource,f.wrote,f.operands,f.issue]

end SemanticFrame
end
end PTX.TcMma
