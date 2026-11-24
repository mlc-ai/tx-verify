-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRead
public import Lemmas.Step.ReadSource
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

/-- A maximal lane at a released Bias vector element records the actual shared read
and retains its trace cursor at the value-dependent continuation. -/
theorem biasWordReadOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) (hGuard : SyncGuarded l kernel X)
    {g pos base : Nat} (hg : g < l.threads) (repeated : Bool) (i : Fin 16)
    {before t : TState} {ending : Option TState}
    (hPc : t.pc = biasReadPc repeated i) (hFault : t.fault = none)
    (hBase : t.regs (biasReadSite repeated i).base = some (b32 base))
    (hAddr : base + (biasReadSite repeated i).offset < 2 ^ 32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before))
    (hTail : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ bytes, let state := afterLoad t (biasReadRegs repeated i) bytes
      X.get (g,pos) = some ⟨biasReadPc repeated i,
        .rd (biasReadAcc l g base repeated i t.sub) bytes⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some state) ∧
      Run kernel Assumptions.all l g state ((X.tr g).drop (pos+1)) ending ∧
      pos+1 ≤ (X.tr g).length ∧ (pos+1 = (X.tr g).length → Step.Released l X g) := by
  let acc := biasReadAcc l g base repeated i t.sub
  let advance (bytes : List (Option Byte)) := afterLoad t (biasReadRegs repeated i) bytes
  have hOut : out kernel Assumptions.all l g t = .ev (.read acc advance) :=
    biasReadTemplate repeated i hPc hFault hBase hAddr hAlign
  have hNext : Next kernel Assumptions.all l g before t (.read acc advance) := ⟨hLocal,hOut⟩
  have hLt : pos < (X.tr g).length := by
    by_contra! hLong
    have hAtEnd := Nat.le_antisymm hBound hLong
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hAtEnd; omega
    rw [List.take_of_length_le hLong] at hPrefix
    exact hMax.not_grows
      (Step.read_source_counted_extension hMax.1 hg hStarted (hRelease hAtEnd) hPrefix hLocal hOut
        (fun _ _ _ =>
          Assumptions.wf_snoc_nonGlobal hMax.1 (by simp [acc, biasReadAcc])) hGuard)
  rw [List.drop_eq_getElem_cons hLt] at hTail
  obtain ⟨_,⟨bytes,hLength,hEvent,hState⟩,hCont⟩ := hNext.continuing_event
    (by rintro ⟨_,_,_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hState
  have he : X.get (g,pos) = some ⟨t.pc,.rd acc bytes⟩ := by
    change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hLt,hEvent]
  refine ⟨bytes,hPc ▸ he,?_,hCont,by omega,?_⟩
  · rw [List.take_succ_eq_append_getElem hLt,hEvent]
    exact hPrefix.snoc hLocal ⟨_,hOut,bytes,hLength,rfl,rfl⟩
  · intro hEnd
    have hLast : (X.tr g).length-1 = pos := by omega
    refine Step.Released.of_get fun ev hv => ?_
    rw [hLast,he] at hv
    cases hv
    intro hBlocking
    cases hBlocking

end PTX.Kernels.TmlFa4Fwd.Softmax
