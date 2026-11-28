-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Data
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.StoreIndex
import Kernels.InklingRelDecode.Proof.Prologue.Control.TripBound
import Lemmas.Flow.WordBound

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof Arith32

private theorem limit_eq (b : BitVec 64) (hb : b.toNat<2^32) :
    (Prologue.Control.positive b).toNat = if b.toNat < 2^31 then b.toNat else 0 := by
  simp only [Prologue.Control.positive,scmpi,PTX.compare,r32,truncBits,BitVec.toNat_ofNat,
    toSigned,Int.reducePow]
  generalize b.toNat = z at hb ⊢
  split_ifs <;> simp_all <;> omega

private theorem word_bound (v : BitVec 64) : (truncBits 32 v).toNat < 2^32 := by
  simp only [truncBits,BitVec.toNat_ofNat]; omega

theorem dataEntry_ok {Q L m g w d} (hp : Pre Q L m) (hg : g<L.threads)
    (words : Prologue.Control.Words d) : (dataEntry Q L g w d).Ok := by
  let split := (L.ctaidOf (g/L.block)).get .x
  let x := addi (Lib.word d.seq) 127
  let blocks := Prologue.Control.iters Q.splits split (Prologue.Control.div128 x)
  have hb : blocks.toNat < 2^32 := word_bound _
  refine ⟨hb,limit_eq blocks hb,words.1,word_bound _,?_,?_,
    Prologue.Control.key_range hp split (Lib.coordinate_bounds hp hg).1 x,?_⟩
  · change (shru _ 7).toNat < _
    change ((r32 _) >>> 7).toNat < _
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    unfold r32
    have := word_bound (Prologue.Control.positive (addi (Prologue.Control.past d) (-1023)))
    omega
  · change (andi _ (-128)).toNat < _
    exact lt_of_le_of_lt (toNat_andi_le ..) (by decide)
  · exact Lib.split_index_small hp (Lib.coordinate_bounds hp hg).1

theorem soft_initial_inv {Q L m g w d} (hp : Pre Q L m) (hg : g<L.threads)
    (words : Prologue.Control.Words d) :
    Softmax.Control.Inv (dataEntry Q L g w d) (g%L.block) {} := by
  refine ⟨dataEntry_ok hp hg words,?_,Nat.zero_le _,fun _ => rfl,?_,?_,?_,?_⟩
  · rw [hp.block]; omega
  · intro _ h; cases h
  · intro _ h; cases h
  · intro h; cases h
  · intro _ h; exact (h rfl).elim

end PTX.Kernels.InklingRelDecode.Proof
