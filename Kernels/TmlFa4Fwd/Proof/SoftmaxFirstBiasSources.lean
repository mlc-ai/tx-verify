-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadSource
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstInputs

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The first and second 64-element boxes belong to the same 128-element bias visit. -/
def biasVectorHalf (i : Fin 16) : Fin 2 :=
  ⟨i.val / 8, by have := i.isLt; omega⟩

/-- The first-visit bias word contains the two logical columns named by its selected box. -/
def firstBiasSourceWord (p : Params) (l : Launch) (g row head : Nat)
    (column : Fin 2 → Nat) (i : Fin 16) (word : Nat) : Value :=
  let absRow := row + (g % l.block) % 128
  let lowCol := column (biasVectorHalf i) + (8 * (i.val % 8) + 2 * word)
  biasLoadWord (biasBoxValue p absRow head lowCol) (biasBoxValue p absRow head (lowCol + 1))

/-- The observed selected copy for this half records the real TMA descriptor and acquire. -/
structure FirstBiasBox (p : Params) (l : Launch) (X : Execution) (stage : Fin 2)
    (g wait col row head : Nat) (half : Fin 2) (tensor : EvId) : Prop where
  cta : tensor.1 / l.block = g / l.block
  observed : AsyncCopy.AsyncObserved X tensor (.notify .load) (g, wait) true .cta
  spec : ∃ o barrier clusterAddress, X.tensor tensor = some o ∧
    o.spec = biasInputSpec p col row head ⟨.shared, g / l.block, biasBoxStart l stage half.val⟩
      barrier clusterAddress

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hX writes

/-- The selected copies provide the exact first Bias read values at the offsets from the
actual successful poll. The two writers are chosen at the observed acquire generation. -/
theorem firstBiasValuesOfBoxes (stage : Fin 2) {g wait row head : Nat} (column : Fin 2 → Nat)
    (hc : ∀ half, column half + 64 ≤ 1280) (hh : head < p.heads) (tensor : Fin 2 → EvId)
    (hBoxes : ∀ half, FirstBiasBox p l X stage g wait (column half) row head half (tensor half))
    (hOrder : ∀ i (word : Fin 4),
      BiasWordOrder p l X stage false i word g (wait + 1 + 4 * i.val + word.val)
        (tensor (biasVectorHalf i))) :
    ∀ i k, k < 4 → ∀ bs, X.get (g, wait + 1 + 4 * i.val + k) = some
      ⟨biasReadPc false i, .rd (biasReadAcc l g (biasVectorBase l g stage false i) false i k) bs⟩ →
      rebuild 3 bs = .ok (firstBiasSourceWord p l g row head column i k) := by
  intro i k hk bs hRead
  let half := biasVectorHalf i
  let word : Fin 4 := ⟨k, hk⟩
  obtain ⟨o, barrier, clusterAddress, hObserve, hSpec⟩ := (hBoxes half).spec
  exact biasReadWordOfBox hp hX writes stage false i word (hc half) hh hObserve hSpec hRead
    (by omega) (hBoxes half).cta (hBoxes half).observed (hOrder i word)

/-- Replay the actual first QK/Bias input sequence with the Bias words computed from
the selected tensor copies and their order relative to the observed reads. -/
theorem firstQkBiasInputsOfBoxes (stage : Fin 2) {g j row head : Nat} {t : TState}
    {F : List (Nat × Value)} (column : Fin 2 → Nat) (hc : ∀ half, column half + 64 ≤ 1280)
    (hh : head < p.heads) (ht : At t 3425 F) (hQkWait : (2769, b32 (waitLoc l g stage 1).addr) ∈ F)
    (hBiasWait : (2771, b32 (waitLoc l g stage 2).addr) ∈ F) (hPhase : (2770, b32 0) ∈ F)
    (hAddr0 : (2788, b32 (scoreAddress l g stage 0)) ∈ F)
    (hAddr2 : (2789, b32 (scoreAddress l g stage 2)) ∈ F)
    (hQkFrame : ∀ x ∈ F, x.1 ≠ 9751 ∧ firstScoreKeeps x.1)
    (hBiasFrame : ∀ x ∈ F, x.1 ≠ 9752 ∧ ∀ i, biasVectorKeeps false i x.1)
    (hBytes : ∀ pos (q : Fin 4) vals, X.get (g, pos) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l g stage q) vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (hBases : ∀ i, ((biasReadSite false i).base, b32 (biasVectorBase l g stage false i)) ∈ F)
    (hSources : ∀ wait, X.get (g, wait) =
      some ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ →
      ∃ tensor : Fin 2 → EvId,
        (∀ half, FirstBiasBox p l X stage g wait (column half) row head half (tensor half)) ∧
        (∀ i (word : Fin 4),
          BiasWordOrder p l X stage false i word g (wait + 1 + 4 * i.val + word.val)
            (tensor (biasVectorHalf i))))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ (qkFails biasFails : Nat) (u : TState) (scores : Fin 4 → List Value),
      let qkStart := j + qkFails + 1
      let biasWait := qkStart + 4
      let biasStart := biasWait + biasFails + 1
      (X.tr g).drop j =
        List.replicate qkFails ⟨3425, .wait (waitLoc l g stage 1) 0 false true .cta⟩ ++
          ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩ :: (X.tr g).drop qkStart ∧
      (X.tr g).drop biasWait =
        List.replicate biasFails ⟨3498, .wait (waitLoc l g stage 2) 0 false true .cta⟩ ++
          ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ :: (X.tr g).drop biasStart ∧
      At u 3581 F ∧ FirstScores l X stage g qkStart u scores ∧
      (∀ i, let words := firstBiasSourceWord p l g row head column i
        BiasWordReads l X false i g (biasStart + 4 * i.val)
          (biasVectorBase l g stage false i) words ∧ BiasUnpacked false i u words) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (biasStart + 64)) none := by
  have hCoord (i : Fin 16) := biasVectorAddressBounds hp g stage i
  refine firstQkBiasInputsTrace hp stage ht hQkWait hBiasWait hPhase hAddr0 hAddr2
    hQkFrame hBiasFrame hBytes (biasVectorBase l g stage false)
    (firstBiasSourceWord p l g row head column) (fun _ _ _ => biasLoadWordShape _ _) hBases
    (fun i => by rw [biasVectorBase_add]; exact (hCoord i).1)
    (fun i => by rw [biasVectorBase_add]; exact (hCoord i).2) ?_ hr
  intro wait hWait
  obtain ⟨tensor, hBoxes, hOrder⟩ := hSources wait hWait
  exact firstBiasValuesOfBoxes hp hX writes stage column hc hh tensor hBoxes hOrder

end
end PTX.Kernels.TmlFa4Fwd.Softmax
