-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemScoreLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxOpeningScoreValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Proof Epilogue Thread.Scores

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    (hFrame : OutputFootprint p X) {batch : Nat} (hb : batch < p.batch) (q : Fin 4) {load : EvId}
    {a : Nat} {vals : List Value} (hLo : tilePrefix p batch*p.heads ≤ load.1/l.block)
    (hHi : load.1/l.block < tilePrefix p (batch+1)*p.heads)
    (he : X.get load = some ⟨scorePc .first q,.tc (.ld a vals .s32x32b)⟩) {wait : Nat}
    {openingStage : Fin 2} (hFirst : FirstScoreAcquire l X (load.1,wait) openingStage)
include hp hX hCuQ hFrame hb q hLo hHi he hFirst

/-- An actual opening score word is the selected launch QK dot on any consistent prefix. -/
theorem scoreLoadDotOfOpeningResult (word : Fin 32) :
    let coords := assignedCoordinates p batch (load.1/l.block)
    let firstQ := p.qOffset batch+256*coords.1+128*openingStage.val
    let firstK := 128*(PTX.Kernels.TmlFa4Fwd.Mma.trips p batch coords.1-1)
    vals[word.val]? = some (.float .f32
      (firstScoreDot p l load.1 batch coords.2 firstQ firstK q word)) := by
  obtain ⟨g,j⟩ := load
  let k := word.val
  obtain ⟨warp,hWarp,hAddr,hLen,_⟩ := scoreLoadAddress hp hX .first q he
  have hRole : Prologue.warpIndex l g/4 = openingStage.val := (hFirst.role hp hX).2
  have hWarpStage : stageOf warp = openingStage := Fin.ext (by change warp.val/4 = _; rwa [hWarp])
  rw [hWarpStage] at hAddr
  subst a
  let a := scoreAddress l g openingStage q
  have hIndex : k < vals.length := hLen.symm ▸ word.isLt
  let cell := tcDataCell l g .s32x32b a k
  obtain ⟨stage,hLoad⟩ := ScoreLoadCell.ofDecoded hp hX .first q he hIndex (cell := cell) rfl
  obtain ⟨_,_,hRole',_,_⟩ := hLoad.acquire hp hX
  have hStage : stage = openingStage := Fin.ext (hRole'.symm.trans hRole)
  subst stage
  have hGen := openingScoreLoadGeneration hp hX openingStage hRole q he
  obtain ⟨bank⟩ := observedScoreQkBank hp hX hCuQ hLoad
  exact bank.wordOfOpeningInputs hp hX hFrame hCuQ q word he hGen hb hLo hHi

/-- An actual opening score transfer returns finite FP32 words from its eight QK fragments. -/
theorem scoreLoadFloatsOfOpeningResult :
    ∀ k < 32, ∃ r, vals[k]? = some (.float .f32 r) := by
  intro k hk
  exact ⟨_,scoreLoadDotOfOpeningResult hp hX hCuQ hFrame hb q hLo hHi he hFirst ⟨k,hk⟩⟩

/-- An opening score transfer gets all its words from the initial eight QK fragments,
without a premise about other MMA operations or rescale stores. -/
theorem scoreLoadWordsOfOpeningResult :
    ∀ k < 32, (vals.getD k (b32 0)).bytes = 4 := by
  intro k hk
  obtain ⟨r,hWord⟩ := scoreLoadFloatsOfOpeningResult hp hX hCuQ hFrame hb q hLo hHi he hFirst k hk
  simp only [List.getD_eq_getElem?_getD,hWord,Option.getD_some]
  rfl
end

/-- Full word values for opening score loads recorded in the anchor warp. -/
@[no_expose] def OpeningScoreWords (l : Launch) (X : Execution) (anchor : Nat) : Prop :=
  ∀ q : Fin 4, ∀ load a vals, SameWarp l anchor load.1 →
    ∀ wait : Nat, ∀ stage : Fin 2, FirstScoreAcquire l X (load.1,wait) stage →
    X.get load = some ⟨scorePc .first q,.tc (.ld a vals .s32x32b)⟩ →
    ∀ k < 32, (vals.getD k (b32 0)).bytes = 4

theorem OpeningScoreWords.observed {l : Launch} {X : Execution} {g : Nat}
    (hWords : OpeningScoreWords l X g) (q : Fin 4) {load : EvId} {a : Nat} {vals : List Value}
    (hWarp : SameWarp l g load.1) {wait : Nat} {stage : Fin 2}
    (hFirst : FirstScoreAcquire l X (load.1,wait) stage)
    (he : X.get load = some ⟨scorePc .first q,.tc (.ld a vals .s32x32b)⟩) :
    ∀ k < 32, (vals.getD k (b32 0)).bytes = 4 :=
  hWords q load a vals hWarp wait stage hFirst he

theorem OpeningScoreWords.ofSelectedCta {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) : OpeningScoreWords l X g :=
  fun q _ _ _ hs _ _ hFirst he => scoreLoadWordsOfOpeningResult hp hX hCuQ hFrame hb q
    (hs.1.2.2 ▸ hLo) (hs.1.2.2 ▸ hHi) he hFirst

end PTX.Kernels.TmlFa4Fwd.Softmax
