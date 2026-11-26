-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdxStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexByteVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.SgTid
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StoreVal

@[expose] public section

/-! # The validity bytes the index lane stores

A validity store of the index warp (pc `2474`, the main cache's blocks, or `2563`, the extra
cache's) writes the byte of an 8-bit word of the lane's block `r`: the lane `%tid.x % 4 = 0` of
quad `o = lane / 4` stores, as the third store of its block (`3 r + 2` stores before it), the
byte whose bit `i` is `slotValid` of position `64 r + 8 o + i` of the main cache (of the extra
cache, `64 (r - M) + 8 o + i`, `M` the main cache's blocks). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The quad's lane `g + i / 2` is in the CTA of `g`, its place in the byte is `i`. -/
private theorem vbit_pos (hp : Pre P L m) {g i : Nat} (hm4 : tidOf L g % 4 = 0) (hi : i < 8) :
    ctaidY L (g + i / 2) = ctaidY L g ∧ ctaidX L (g + i / 2) = ctaidX L g ∧
      ∀ b, 64 * b + Index.lane2 L (g + i / 2) + i % 2 = 64 * b + 8 * (tidOf L g % 32 / 4) + i := by
  have ht := tidOf_eq hp g
  have ht' := tidOf_eq hp (g + i / 2)
  have hc : ctaOf L (g + i / 2) = ctaOf L g := by simp only [ctaOf, hp.block]; omega
  refine ⟨by simp only [ctaidY, hc], by simp only [ctaidX, hc], fun b => ?_⟩
  simp only [Index.lane2]
  omega

private theorem vbit_main (hp : Pre P L m) {g i b : Nat} (hm4 : tidOf L g % 4 = 0) (hi : i < 8)
    (hb : b < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) :
    vbit P L (g + i / 2) b (i % 2) = true ↔
      slotValid P (ctaidY L g) (ctaidX L g) false (64 * b + 8 * (tidOf L g % 32 / 4) + i) := by
  obtain ⟨e1, e2, e3⟩ := vbit_pos hp hm4 hi
  simp only [vbit, e1, hb, ↓reduceIte, e2, e3, decide_eq_true_eq]

private theorem vbit_extra (hp : Pre P L m) {g i b : Nat} (hm4 : tidOf L g % 4 = 0) (hi : i < 8)
    (hb : FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ≤ b) :
    vbit P L (g + i / 2) b (i % 2) = true ↔
      slotValid P (ctaidY L g) (ctaidX L g) true
        (64 * (b - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
          8 * (tidOf L g % 32 / 4) + i) := by
  obtain ⟨e1, e2, e3⟩ := vbit_pos hp hm4 hi
  simp only [vbit, e1, show ¬ b < FlashMlaSparseDecodeH64.numOrigBlocks
    (P.topkLen (ctaidY L g)) from by omega, ↓reduceIte, e2, e3, decide_eq_true_eq]

/-- **The validity byte of an index lane's store**: block `r`, quad `o`, the validity of the
slots at the positions of the quad's eight. -/
theorem index_validByte (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.IndexAt L g pc)
    (hsz : a.size = 1) :
    (pc = 2474 ∨ pc = 2563) ∧ ∃ r z, ((X.tr g).take k).countP idxWr = 3 * r + 2 ∧
      tidOf L g % 4 = 0 ∧
      bs = (Value.bits 8 z).toBytes ∧
      (pc = 2474 → r < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ∧
        ∀ i < 8, (z.toNat.testBit i = true ↔
          slotValid P (ctaidY L g) (ctaidX L g) false (64 * r + 8 * (tidOf L g % 32 / 4) + i))) ∧
      (pc = 2563 → FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) ≤ r ∧
        ∀ i < 8, (z.toNat.testBit i = true ↔
          slotValid P (ctaidY L g) (ctaidX L g) true
            (64 * (r - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
              8 * (tidOf L g % 32 / 4) + i))) := by
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨hw, hr1, hr2⟩ := hat
  obtain ⟨d, n, rfl, hR, ⟨hpcE, hE⟩, -⟩ := index_state hJ hi hev hpcσ ⟨hr1, by dsimp only; omega⟩
  have hx := Frame.lt_of_get hX he
  have hw7 : warpOf L g = 7 := hw
  obtain ⟨hok, hel, hsk⟩ := ix_ok hp hX hσ _ n rfl
  obtain ⟨-, -, -, t1, o', hgood, hq, hes⟩ := ix_strictAt hp hX hFw he hσ
  obtain ⟨ins, hc', hf⟩ := Code.fired_of_good (thread_sound hp) hgood hes
  obtain ⟨hat', hinv⟩ := hgood
  have hS : ((X.tr g).take k).countP idxWr = n (.index .st) := by
    refine Eq.trans ?_ (state_count hσ (.index .st)).symm
    refine List.countP_congr fun e _ => ?_
    simp only [cls, Index.cls, Index.inRole, Index.kindOf, idxWr]
    cases e with | mk pc kd =>
      cases kd with
      | wait l q ok a sc => cases ok <;> simp
      | _ => simp
  have hsite : d.site = .bA ∨ d.site = .bB := by
    obtain ⟨site, el, ac, c⟩ := d
    dsimp only
    cases site <;> simp only [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
      Index.StoreEv] at hE <;> try (first | exact .inl rfl | exact .inr rfl)
    all_goals
      exfalso
      first
        | (simp at hE; done)
        | (rcases hE with ⟨a', bs', h, -, hs'⟩ | ⟨f, h⟩
           · obtain ⟨rfl, rfl⟩ := Kind.wr.inj h
             omega
           · cases h)
  have hm4 : tidOf L g % 4 = 0 := by
    have h1 := hsk hsite
    have h2 := sgB_tid hp g
    simp only [Index.sgB, h1, Bool.false_eq_true, ↓reduceIte] at h2
    simp only [tidOf]
    by_contra hne
    simp [hne] at h2
  obtain ⟨b, hst, hMo, hEo, hbits⟩ :=
    ix_byteBits hp hX hFw (noUbBefore_of_get hX he) hσ hx hw7 hsite hm4
  obtain ⟨a', ha'⟩ := Index.noUbq_byteVal d rfl hsite t1 ins _ o' hat' hinv.1 hc' hq hf
  have hbs : bs = (Value.bits 8 (truncBits 8 (Index.ixByteW L g d))).toBytes := (Kind.wr.inj ha').2
  have hpc : pc = 2474 ∨ pc = 2563 := by
    rcases hsite with h | h <;> rw [h] at hpcE <;> simp [IxSite.pc] at hpcE <;> omega
  refine ⟨hpc, b, truncBits 8 (Index.ixByteW L g d), by rw [hS, hst], hm4, hbs, fun h => ?_,
    fun h => ?_⟩
  · have hA : d.site = .bA := by
      rcases hsite with h' | h'
      · exact h'
      · rw [h'] at hpcE
        simp [IxSite.pc] at hpcE
        omega
    obtain ⟨hlt, -⟩ := hMo hA
    exact ⟨hlt, fun i hi => (by rw [hbits i hi]; exact vbit_main hp hm4 hi hlt)⟩
  · have hB : d.site = .bB := by
      rcases hsite with h' | h'
      · rw [h'] at hpcE
        simp [IxSite.pc] at hpcE
        omega
      · exact h'
    obtain ⟨hge, -⟩ := hEo hB
    exact ⟨hge, fun i hi => (by rw [hbits i hi]; exact vbit_extra hp hm4 hi hge)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
