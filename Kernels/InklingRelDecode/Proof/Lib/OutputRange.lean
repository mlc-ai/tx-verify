-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

variable {L : Launch} {mem0 : Mem0}

/-- **The output arrays are fixed by the launch**: two parameter sets of one launch have the same
output bases and sizes (`param_10`, `param_11`, `param_24`, `param_25`). -/
theorem out_pinned {P P' : Params} (h : Pre P L mem0) (h' : Pre P' L mem0) :
    P'.oBase = P.oBase ∧ P'.lseBase = P.lseBase ∧ oBytes P' = oBytes P ∧
      lseBytes P' = lseBytes P := by
  have key : ∀ {x y : Nat}, x < 2 ^ 64 → y < 2 ^ 64 →
      (some (BitVec.ofNat 64 x) : Option (BitVec 64)) = some (BitVec.ofNat 64 y) → x = y := by
    intro x y hx hy he
    have := congrArg BitVec.toNat (Option.some.inj he)
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have hs : P'.splits = P.splits := key (by have := h'.splitsRange; omega)
    (by have := h.splitsRange; omega) (h'.paramSplits.symm.trans h.paramSplits)
  have hn : P'.nTok = P.nTok := key (by have := h'.nTokRange; omega)
    (by have := h.nTokRange; omega) (h'.paramNTok.symm.trans h.paramNTok)
  have hob : oBytes P' = oBytes P := by simp only [oBytes, hs, hn]
  have hlb : lseBytes P' = lseBytes P := by simp only [lseBytes, hs, hn]
  have hpo : ∀ {R : Params}, Pre R L mem0 → 0 < oBytes R ∧ 0 < lseBytes R := by
    intro R hR
    have := hR.splitsPos
    have := hR.nTokPos
    unfold oBytes lseBytes heads headDim
    constructor <;> positivity
  have hoB : ∀ {R : Params}, Pre R L mem0 → R.oBase < 2 ^ 64 := fun hR => by
    have := hR.oRange; have := (hpo hR).1; omega
  have hlB : ∀ {R : Params}, Pre R L mem0 → R.lseBase < 2 ^ 64 := fun hR => by
    have := hR.lseRange; have := (hpo hR).2; omega
  exact ⟨key (hoB h') (hoB h) (h'.paramO.symm.trans h.paramO),
    key (hlB h') (hlB h) (h'.paramLse.symm.trans h.paramLse), hob, hlb⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
