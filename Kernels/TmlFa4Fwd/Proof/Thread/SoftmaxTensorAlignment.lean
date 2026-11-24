-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTensorTrace
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxMetadataReads
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Tmem.TmemPairHistory
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Softmax

private theorem softmaxClassOnTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hWarp : warpIndex l g < 8) :
    ∀ e ∈ X.tr g, isTcColl e = isTcData e := by
  intro e he
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp he
  exact softmaxTensorEventClass hp hX hWarp hi

private theorem sameWarpTensorTraces {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : Complete l X) (hFrame : OutputFootprint p X)
    {g h : Nat} (hSoft : warpIndex l g < 8) (hWarp : SameWarp l g h)
    {i : Nat} {e : Event} (he : X.get (g,i) = some e) (hColl : isTcColl e = true) :
    softmaxTraceTokens (X.tr g) = softmaxTraceTokens (X.tr h) := by
  have hg := hWarp.1.1
  have hh := hWarp.1.2.1
  have hCta := hWarp.1.2.2
  have hRole : warpIndex l g = warpIndex l h := hWarp.2
  have hPeer := hRole ▸ hSoft
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g (laneOf l g) = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hBand := softmaxTensorCollectiveBand hp hX hSoft he hColl
  have hWork := softmaxWorkOfActiveEvent hp hX hg hSoft hLane (hFrame.metadataProtected hp).1
    (hSelf.symm ▸ he) (by omega) (by omega)
  obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hWork
  have hLeft := softmaxTensorTraceOfComplete hp hX hComplete hFrame hg hSoft hb hLo hHi
  have hRight := softmaxTensorTraceOfComplete hp hX hComplete hFrame hh hPeer hb
    (hCta ▸ hLo) (hCta ▸ hHi)
  dsimp only at hLeft hRight
  rw [← hCta,← (show (⟨warpIndex l g,hSoft⟩ : Fin 8) =
    ⟨warpIndex l h,hPeer⟩ from Fin.ext hRole)] at hRight
  exact hLeft.trans hRight.symm

private theorem traceFrozenAtExit {l : Launch} {m : Mem0} {X Y : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    (hY : Consistent l kernel Assumptions.all m Y) (hXY : X.le Y)
    {g j pc : Nat} (hg : g < l.threads) (he : X.get (g,j) = some ⟨pc,.exit⟩) :
    X.tr g = Y.tr g := by
  have hx := Execution.exit_last hX hg he
  have hy := Execution.exit_last hY hg (Execution.le_get hXY he)
  obtain ⟨tail,hTail⟩ := hXY.1 g
  have hLen := congrArg List.length hTail
  rw [List.length_append,← hx,← hy] at hLen
  have hNil : tail = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [hNil] using hTail

/-- Actual softmax tensor collectives have equal sites and operands at equal ordinals,
and an exiting peer has consumed every slot. This uses the existing output footprint
and completion of bounded maximal extensions. -/
theorem softmaxTensorAlignmentOfFootprintAndCompletion
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputIntentFootprint p Y)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y) :
    SoftmaxTensorAlignment l X := by
  obtain ⟨Y,hXY,hMax⟩ := maximalExtension hp hX
  have hY := hMax.1
  have hDone := hComplete Y hMax
  have hFoot := (hFrame Y hY).performed
  constructor
  · intro g h i j k e f hSoft hWarp he hf hi hj
    have hRole : warpIndex l g = warpIndex l h := hWarp.2
    have hPeer : warpIndex l h < 8 := hRole ▸ hSoft
    have hEY := Execution.le_get hXY he
    have hFY := Execution.le_get hXY hf
    have hIY := hi.mono hXY
    have hJY := hj.mono hXY
    obtain ⟨e',hE',hColl⟩ := hi.1
    obtain rfl := Option.some.inj (he.symm.trans hE')
    obtain ⟨f',hF',hFColl⟩ := hj.1
    obtain rfl := Option.some.inj (hf.symm.trans hF')
    have hSame := sameWarpTensorTraces hp hY hDone hFoot hSoft hWarp hEY hColl
    obtain ⟨a,ha,hAtA⟩ := softmaxTraceTokensAt
      (softmaxClassOnTrace hp hY hSoft) hEY hColl hIY.2
    obtain ⟨b,hb,hAtB⟩ := softmaxTraceTokensAt
      (softmaxClassOnTrace hp hY hPeer) hFY hFColl hJY.2
    rw [hSame] at hAtA
    have hEq := Option.some.inj (hAtA.symm.trans hAtB)
    have hSite := congrArg Prod.fst hEq
    have hSome := congrArg (fun op : Fin 4 => some op) (congrArg Prod.snd hEq)
    have hOp := ha.trans (hSome.trans hb.symm)
    exact ⟨hSite,softmaxTensorOperandsAgree hp hX hWarp hSoft he hf hColl hSite hOp⟩
  · intro g h i j k hSoft hWarp hi hShort
    have hIY := hi.mono hXY
    obtain ⟨e,he,hColl⟩ := hIY.1
    obtain ⟨⟨pc,hExit⟩,hCount⟩ := hShort
    have hTrace := traceFrozenAtExit hX hY hXY hWarp.1.2.1 hExit
    have hRole : warpIndex l g = warpIndex l h := hWarp.2
    have hPeer : warpIndex l h < 8 := hRole ▸ hSoft
    have hSame := sameWarpTensorTraces hp hY hDone hFoot hSoft hWarp he hColl
    obtain ⟨_,_,hAt⟩ := softmaxTraceTokensAt
      (softmaxClassOnTrace hp hY hSoft) he hColl hIY.2
    rw [hSame] at hAt
    have hk := (List.getElem?_eq_some_iff.mp hAt).1
    rw [softmaxTraceTokensCount (softmaxClassOnTrace hp hY hPeer),← hTrace] at hk
    exact (Nat.not_lt_of_ge hCount) hk

end PTX.Kernels.TmlFa4Fwd.Thread
