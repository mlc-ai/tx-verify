-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcReadFinishMma
public import Lemmas.Tcgen05.TcMmaAReadUnique

@[expose] public section

/-! # Finishing an MMA keeps the Tensor Memory read rule when A may be in Tensor Memory

A proof tool. Completing an unfinished MMA `i` (`X.finishMma i values ra rb`) records its operands,
so its results gain value derivations. A Tensor Memory load or an MMA's A read that sees such a
value would gain a new obligation. The order and cell relations of the extension are those of
`X`; only the values written (`Wrote`) can differ, and only through `i`.

* A load's MMA source has an observed completion, so its derivation is one of `X`
  (`readOk_finishMma_shared`).
* An A source of an MMA `j` is ordered before `j` (`WriteBefore`). An MMA source is ordered by an
  observed completion or by the pipelined D-write order of MMAs with the same accumulator. The
  premise `ATmemApart` excludes the second: no MMA with the same accumulator as `j` writes a cell
  that `j` reads as A. The source then has an observed completion, and its derivation is one of
  `X` (`Result.of_finishMma_observed`). A shift's value comes from a source ordered before the
  shift. So the value of every A source in the extension is its value in `X`
  (`wrote_of_finishMma_aSource`).
* A source of an MMA other than `i` is then constrained by `X`. For `i` itself the caller chooses
  the recorded A bytes as the source values of `X` (`hval`), and the read rule holds
  (`readOk_finishMma_tmemA`). -/

namespace PTX.TcMma
open AsyncCopy
noncomputable section

/-- No MMA with the same accumulator as an MMA `j` writes a cell that `j` reads as operand A from
Tensor Memory. -/
def ATmemApart (X : Execution) : Prop :=
  ∀ j d s acc mask, X.MmaIssue j d s acc mask → ∀ index cell pos, aCell s index = some (cell, pos) →
    ∀ w d' s' acc' mask' row col, X.MmaIssue w d' s' acc' mask' → SameAccumulator d' s' d s →
      writeCell s' d' mask' row col ≠ some cell

variable {L : Launch} {A : List Assumption} {X : Execution} {i : EvId}
  {values : MmaOperands} {ra rb : Nat → Option Ref}
local notation "Y" => X.finishMma i values ra rb

/-- A write ordered before an MMA `j`, of a cell that `j` reads as A, left the same value in `X`
as in the extension. A shift's value is that of its source, which is ordered before the shift, a
consumer that is not an MMA. -/
theorem wrote_of_finishMma_aSource (hu : WarpIssuerUnique L X)
    (ha : ∀ n, ¬ Relation.TransGen (TcStep L X) n n) (hc : CommitOk X) (hap : ATmemApart X)
    {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) (hn : X.async.mmaDone i = false)
    {j : EvId} {dj : Nat} {sj : OperandSpec} {accj : Bool} {maskj : List Nat}
    (hj : X.MmaIssue j dj sj accj maskj) {index : Nat} {cell : Cell} {pos : Nat}
    (hcell : aCell sj index = some (cell, pos)) {source : EvId} {v : Value}
    (hb : WriteBefore L X source j) (hw : Wrote L A Y source cell v) :
    Wrote L A X source cell v := by
  rcases hw with hr | hst | hcp | ⟨src, from', ⟨hsc, hsrc, hrd, hrs⟩, hval⟩
  · obtain ⟨d', s', acc', mask', hsi⟩ := hr.actual_issue
    rcases hb.of_mma hsi with hd | ⟨-, -, d1, s1, a1, m1, d2, s2, a2, m2, hx, hy, hsame⟩
    · exact .inl (hr.of_finishMma_observed hu ha hc hn hd.tracked)
    · obtain ⟨rfl, rfl, -, -⟩ := mmaIssue_params hy hj
      exfalso
      cases hr with
      | overwrite issue position _ _ =>
        obtain ⟨rfl, rfl, -, rfl⟩ := mmaIssue_params hx issue
        exact hap j _ _ _ _ hj index cell pos hcell source _ _ _ _ _ _ hx hsame position
      | accumulate issue position _ _ _ _ =>
        obtain ⟨rfl, rfl, -, rfl⟩ := mmaIssue_params hx issue
        exact hap j _ _ _ _ hj index cell pos hcell source _ _ _ _ _ _ hx hsame position
      | accumulateStored issue position _ _ _ _ =>
        obtain ⟨rfl, rfl, -, rfl⟩ := mmaIssue_params hx issue
        exact hap j _ _ _ _ hj index cell pos hcell source _ _ _ _ _ _ hx hsame position
  · exact .inr (.inl hst)
  · exact .inr (.inr (.inl ((finishMma_cpValue hi).mp hcp)))
  · refine .inr (.inr (.inr ⟨src, from', ⟨hsc, hsrc, hrd, hrs⟩, ?_⟩))
    obtain ⟨t, hshift, -⟩ := hsc
    have hcons : ∀ d s acc mask, ¬ X.MmaIssue source d s acc mask :=
      fun d s acc mask hm => shift_not_mmaIssue hshift hm
    rcases hval with hr | hst | hcp
    · exact .inl (hr.of_finishMma_before hu ha hc hn hrs.2.2.1 hcons)
    · exact .inr (.inl hst)
    · exact .inr (.inr ((finishMma_cpValue hi).mp hcp))

/-- **Finishing an MMA keeps the Tensor Memory read rule**, when no MMA's A cell is written by
an MMA with the same accumulator and the finished MMA records, for each A byte with a source in
`X`, that source's byte (`hval`). -/
theorem readOk_finishMma_tmemA {K : Kernel} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X) (hu : WarpIssuerUnique L X)
    (hap : ATmemApart X) {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) (hn : X.async.mmaDone i = false)
    (hval : ∀ index cell pos source value,
      (∃ d s acc mask, X.MmaIssue i d s acc mask ∧ aCell s index = some (cell, pos)) →
      ReadSource L X .a source i cell → Wrote L A X source cell value →
      pos < value.bytes → values.a[index]? = some (some (value.byteAt pos))) :
    ReadOk L A Y := by
  have hac := tcStep_acyclic hX hg
  constructor
  · intro load address vals sh j source cell value hl hc hs hw
    have hcons : ∀ d s acc mask, ¬ X.MmaIssue load d s acc mask :=
      fun d s acc mask hm => tld_not_mmaIssue hl hm
    exact hX.tcRead.1 load address vals sh j source cell value hl hc hs
      (hw.of_finishMma hX hg hu hi hn hs.2.2.1 hcons)
  · intro mma index cell pos source value operands ha hs hw ho hp
    obtain ⟨dj, sj, accj, maskj, hj, hcell⟩ := ha
    have hx := wrote_of_finishMma_aSource hu hac hX.tcCommit hap hi hn hj hcell hs.2.2.1 hw
    by_cases hm : mma = i
    · subst mma
      have hv : operands = values := by simpa [Execution.finishMma] using ho.symm
      subst hv
      exact hval index cell pos source value ⟨dj, sj, accj, maskj, hj, hcell⟩ hs hx hp
    · have ho' : X.async.mmaOperands mma = some operands := by
        simpa [Execution.finishMma, hm] using ho
      exact hX.tcRead.2 mma index cell pos source value operands ⟨dj, sj, accj, maskj, hj, hcell⟩
        hs hx ho' hp

end
end PTX.TcMma
