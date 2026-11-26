-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
public import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # Tensor Memory writes and MMA reads are ordered, given the PV/rescale order

By column class (`writer_cases`), two writes of one cell are, in one CTA:

* two QK MMAs, or two PV MMAs with one D column: one MMA lane (`mmaOne`), so one thread with the
  same accumulator, pipelined in program order (`Before.of_mma_po`);
* two copies `k`: one MMA lane, one event (`mma_cp_once`);
* two stores of warpgroup 0 to one lane: one thread, pipelined (`StoreDoneBefore.of_po`);
* a PV MMA and a rescale store of warpgroup 0: the cross-role order `PvStoreOrder`
  (`Protocol/TmemRace/PvStore.lean`).

So the writes are ordered (`writes_safe`). An accumulator read is a write of the same MMA (zero
output masks), so it is ordered by the writes (`acc_order`); an A read of QK MMA `k` reads the
cells of copy `k` only, which precedes it in the lane's program order (`mma_cp_first`): the
pipelined copy→A-read pair. The kernel fires no shift. So the reads are ordered
(`reads_safe`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmRace

/-- **The PV/rescale order**: a PV MMA (D below column 256) and a `32x32b` store of one CTA are
ordered: the store completes before the MMA is issued, or the MMA's completion is observed
before the store. -/
def PvStoreOrder (L : Launch) (X : Execution) : Prop :=
  ∀ (x y : EvId) (pc pc' b : Nat) (s : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (a : Nat)
    (vals : List Value), X.get x = some ⟨pc, .tc (.mma b s acc mask)⟩ → b < 256 →
    X.get y = some ⟨pc', .tc (.st a vals .s32x32b)⟩ → x.1 / L.block = y.1 / L.block →
    TcMma.DoneBefore L X x y ∨ TcMma.StoreDoneBefore L X y x

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Two MMA-lane events of one CTA are of one thread. -/
theorem mma_same (hO : MmaOne L X) {x y : EvId} {pc pc' : Nat} {k k' : TcKind}
    (hx : X.get x = some ⟨pc, .tc k⟩) (hy : X.get y = some ⟨pc', .tc k'⟩) (hon : MmaOn L x.1 pc)
    (hon' : MmaOn L y.1 pc') (hc : x.1 / L.block = y.1 / L.block) : x.1 = y.1 :=
  hO hx hy (fun _ h => by cases h) (fun _ h => by cases h) hon hon' hc

/-- Two MMAs of one thread with the operands of one word and one D column are ordered. -/
theorem mma_order (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {x y : EvId}
    {pc pc' d : Nat} {s s' : TcMma.OperandSpec} {a a' : Bool} {aT aT' : Option Nat} {i : Nat}
    (hi : i = TmemRow.qkIdesc ∨ i = TmemRow.pvIdesc)
    (hx : X.get x = some ⟨pc, .tc (.mma d s a [0, 0, 0, 0])⟩)
    (hy : X.get y = some ⟨pc', .tc (.mma d s' a' [0, 0, 0, 0])⟩) (hs : TmemRow.MmaOps L x.1 s aT i)
    (hs' : TmemRow.MmaOps L y.1 s' aT' i) (hthr : x.1 = y.1) :
    x = y ∨ TcMma.WriteBefore L X x y ∨ TcMma.WriteBefore L X y x := by
  have hg : x.1 < L.threads := Frame.lt_of_get hX hx
  obtain ⟨hl, hh⟩ := ops_cta hp hg hi hs
  obtain ⟨hl', hh'⟩ := ops_cta hp (hthr ▸ hg) hi hs'
  obtain ⟨-, hd, -⟩ := hs
  obtain ⟨-, hd', -⟩ := hs'
  have hdd : s.descriptor = s'.descriptor := Option.some.inj (hd.symm.trans hd')
  have hacc : TcMma.SameAccumulator d s d s' :=
    ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl', hthr], by rw [hh, hh', hthr]⟩
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · exact .inr (.inl (.inl (TcMma.Before.of_mma_po ⟨_, hx⟩ ⟨_, hy⟩ hg hthr h hacc)))
  · exact .inl (Prod.ext hthr h)
  · have hacc' : TcMma.SameAccumulator d s' d s :=
      ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl', hthr], by rw [hh, hh', hthr]⟩
    exact .inr (.inr (.inl (TcMma.Before.of_mma_po ⟨_, hy⟩ ⟨_, hx⟩ (hthr ▸ hg) hthr.symm h
      hacc')))

/-- Two stores of one thread are ordered. -/
theorem st_order (hX : Consistent L kernel Assumptions.all m X) {x y : EvId} (hx : StW L X x)
    (hy : StW L X y) (hthr : x.1 = y.1) :
    x = y ∨ TcMma.WriteBefore L X x y ∨ TcMma.WriteBefore L X y x := by
  obtain ⟨pc, a, vals, hgx, -⟩ := hx
  obtain ⟨pc', a', vals', hgy, -⟩ := hy
  have hg : x.1 < L.threads := Frame.lt_of_get hX hgx
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · exact .inr (.inl (.inr (.inl (TcMma.StoreDoneBefore.of_po ⟨_, hgx⟩ ⟨_, hgy⟩ hg hthr h))))
  · exact .inl (Prod.ext hthr h)
  · exact .inr (.inr (.inr (.inl
      (TcMma.StoreDoneBefore.of_po ⟨_, hgy⟩ ⟨_, hgx⟩ (hthr ▸ hg) hthr.symm h))))

/-- A PV MMA and a store of one CTA are ordered (from `PvStoreOrder`). -/
theorem pv_st_order (hPS : PvStoreOrder L X) {x y : EvId} {b : Nat} (hx : PvW L X x b)
    (hb : b ≤ 128) (hy : StW L X y) (hc : x.1 / L.block = y.1 / L.block) :
    TcMma.WriteBefore L X x y ∨ TcMma.WriteBefore L X y x := by
  obtain ⟨pc, s, acc, hgx, -⟩ := hx
  obtain ⟨pc', a, vals, hgy, -⟩ := hy
  rcases hPS x y pc pc' b s acc _ a vals hgx (by omega) hgy hc with h | h
  · exact .inl (.inl (.inl h))
  · exact .inr (.inr (.inl h))

/-- An MMA's write ordered before another write orders its accumulator read before it. -/
theorem acc_order {r w : EvId} {pc d : Nat} {s : TcMma.OperandSpec} {a : Bool}
    {mask : List Nat} (hr : X.get r = some ⟨pc, .tc (.mma d s a mask)⟩)
    (h : TcMma.WriteBefore L X r w) : TcMma.ReadBefore L X .acc r w := by
  rcases h with (h | h) | ⟨⟨_, _, _, pc', h⟩, -⟩ | ⟨-, -, _, _, _, _, _, ⟨pc', h⟩, -⟩
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · rw [hr] at h
    cases h
  · rw [hr] at h
    cases h

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
include hp hX hFw hR hO hPS

/-- **Every two Tensor Memory writes of a cell are ordered.** -/
theorem writes_safe : TcMma.WritesSafe L X := by
  intro x y cell hx hy
  obtain ⟨hcx, cx⟩ := writer_cases hp hX hR hx
  obtain ⟨hcy, cy⟩ := writer_cases hp hX hR hy
  have hc : x.1 / L.block = y.1 / L.block := hcx.symm.trans hcy
  rcases cx with ⟨k, ⟨pc, s, hk, hgx, hon, hops⟩, h1, h2⟩ |
      ⟨b, ⟨pc, s, a, hgx, hon, hops⟩, hb, hb', h1, h2⟩ |
      ⟨k, ⟨pc, c, hk, hgx, hon, ha, -⟩, h1, h2⟩ | ⟨hsx, h1, hl⟩ <;>
    rcases cy with ⟨k', ⟨pc', s', hk', hgy, hon', hops'⟩, h1', h2'⟩ |
      ⟨b', ⟨pc', s', a', hgy, hon', hops'⟩, hb2, hb2', h1', h2'⟩ |
      ⟨k', ⟨pc', c', hk', hgy, hon', ha', -⟩, h1', h2'⟩ | ⟨hsy, h1', hl'⟩
  all_goals try (exfalso; omega)
  · exact mma_order hp hX (.inl rfl) hgx hgy hops hops' (mma_same hO hgx hgy hon hon' hc)
  · obtain rfl : b = b' := by omega
    exact mma_order hp hX (.inr rfl) hgx hgy hops hops' (mma_same hO hgx hgy hon hon' hc)
  · exact .inr (pv_st_order hPS ⟨pc, s, a, hgx, hon, hops⟩ hb hsy hc)
  · have ht := mma_same hO hgx hgy hon hon' hc
    obtain ⟨g, i⟩ := x
    obtain ⟨g', j⟩ := y
    simp only at ht
    subst ht
    obtain ⟨⟨-, r1, r2⟩, -⟩ := hon
    obtain ⟨⟨-, r1', r2'⟩, -⟩ := hon'
    have := mma_cp_once hp hX hFw hgx hgy ⟨r1, r2⟩ ⟨r1', r2'⟩ (by rw [ha, ha']; omega)
    exact .inl (by rw [this])
  · rcases pv_st_order hPS ⟨pc', s', a', hgy, hon', hops'⟩ hb2 hsx hc.symm with h | h
    · exact .inr (.inr h)
    · exact .inr (.inl h)
  · have hb := hp.block
    rw [hb] at hc
    exact st_order hX hsx hsy (by omega)

/-- **Every MMA read and shift read is ordered with every write of its cell.** -/
theorem reads_safe : TcMma.ReadsSafe L X := by
  refine TcMma.readsSafe_iff.mpr ⟨?_, ?_, ?_⟩
  · intro r w cell hr hw
    have hwr := acc_write hX hR hr
    obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, hc⟩ := hr
    rcases writes_safe hp hX hFw hR hO hPS r w cell hwr hw with h | h | h
    · exact .inl h
    · exact .inr (.inr (acc_order he h))
    · exact .inr (.inl h)
  · intro r w cell hr hw
    obtain ⟨d, s, acc, mask, index, b, ⟨pc, he⟩, hac⟩ := hr
    have hg := Frame.lt_of_get hX he
    obtain ⟨hcw, cw⟩ := writer_cases hp hX hR hw
    rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
    · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
    · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
        ⟨_, _, k, -, -, h, -, hops⟩ <;> cases h
      · obtain ⟨hcr, h1, h2⟩ := TmemRow.qk_aCell hk hops hac
        obtain ⟨hlo, hhi⟩ := ops_cta hp hg (.inl rfl) hops
        have hcc : r.1 / L.block = w.1 / L.block := by
          rcases hcr with h | h
          · rw [← hlo, ← h, hcw]
          · rw [← hhi, ← h, hcw]
        have hon : MmaOn L r.1 pc :=
          ⟨hat, by simp only [TmemRow.qkPc] at hpc; split at hpc <;> omega⟩
        rcases cw with ⟨k', -, h1', h2'⟩ | ⟨b', -, hb2, -, h1', h2'⟩ |
          ⟨k', ⟨pc', c, hk', hgw, hon', ha, hsh⟩, h1', h2'⟩ | ⟨-, h1', -⟩
        · omega
        · omega
        · obtain rfl : k' = k := by omega
          have ht := (mma_same hO he hgw hon hon' hcc).symm
          obtain ⟨⟨-, r1, r2⟩, -⟩ := hon
          obtain ⟨⟨-, r1', r2'⟩, -⟩ := hon'
          obtain ⟨g, i⟩ := r
          obtain ⟨g', j⟩ := w
          simp only at ht
          subst ht
          have hlt := mma_cp_first hp hX hFw hgw he ⟨r1', r2'⟩ ⟨r1, r2⟩
          obtain ⟨haT, -⟩ := hops
          refine .inr (.inl (.inr (.inr ⟨TcMma.sameWarp_self hg, .inl
            (TcMma.baseCausality_of_tc_po hgw rfl hlt (len_of_get he)), c, _, _, _, _, ⟨pc', hgw⟩,
            by rw [hsh]; decide, ⟨pc, he⟩, by rw [haT, ha]⟩)))
        · omega
      · obtain ⟨haT, -⟩ := hops
        simp [TcMma.aCell, haT] at hac
    · cases hc'
  · rintro r w cell ⟨sp, ⟨pc, he⟩, -⟩ -
    exact absurd rfl (no_shift_of_code hX code_noShift he sp)

end

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
