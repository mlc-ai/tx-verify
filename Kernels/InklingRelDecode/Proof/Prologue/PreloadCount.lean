-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Rounds

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Geometry

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Arith32 Control

private theorem positive_nat (n : Nat) (h : n<2^31) : positive (W n) = W n := by
  have test : scmpi .gt .s (W n) 0 = decide (n>0) := scmp_gt_W h (by decide)
  simp only [positive,test,decide_eq_true_eq,r32_W (show n<2^32 by omega)]
  split
  · rfl
  · have hn : n=0 := by omega
    rw [hn]; rfl

private theorem div128_nat (n : Nat) (h : n<2^31) : div128 (W n) = W (n/128) := by
  unfold div128
  have sign : shrs (W n) 31 = W (n/2^31) := toNat_shrs_W h (k := 31) (by decide)
  rw [sign,Nat.div_eq_of_lt h]
  change shrs (add32 (W n) (W 0)) 7 = _
  rw [add32_W (by omega),Nat.add_zero]
  exact toNat_shrs_W h (k := 7) (by decide)

private theorem iters_nat {n s z : Nat} (hs : s<n) (h : n+z<2^31) :
    (positive (iters n s (W z))) = W ((z-s+(n-1))/n) := by
  have num : n-1-s+z < 2^31 := by omega
  have D (x : Nat) (hx : x<2^31) : intOf .s 32 (r32 (W x)) = x := by
    change toSigned 32 (r32 (W x)) = x
    rw [r32_W (by omega),toSigned_W hx]
  change positive (intBits 32 ((intOf .s 32 (r32 (add32 (add32 (W n) (not32 (W s)))
    (W z)))).tdiv (intOf .s 32 (r32 (W n))))) = _
  rw [not32_add_W hs (by omega),add32_W (by omega),D _ num,D n (by omega)]
  change positive (i32 (↑((n-1-s+z)/n) : Int)) = _
  have le := Nat.div_le_self (n-1-s+z) n
  rw [i32_W (by omega),positive_nat _ (by omega)]
  by_cases hz : s≤z
  · rw [show n-1-s+z = z-s+(n-1) by omega]
  · rw [Nat.div_eq_of_lt (show n-1-s+z<n by omega),
      Nat.div_eq_of_lt (show z-s+(n-1)<n by omega)]

/-- The second published word is the launch's iteration count, including an empty split. -/
theorem published_iters {Q L m g d} (hp : Pre Q L m) (hg : g<L.threads)
    (seq : d.seq = b32 (Q.seqK ((L.ctaidOf (g/L.block)).get .z))) :
    valueOf Q L g w d 487 =
      b32 (Lib.blocksOf Q L (g/L.block)) := by
  let r := (L.ctaidOf (g/L.block)).get .z
  let s := (L.ctaidOf (g/L.block)).get .x
  obtain ⟨hx,_,hr⟩ := Lib.coordinate_bounds hp hg
  change r<Q.b at hr
  change s<Q.splits at hx
  have seqBound := hp.seqRange r hr
  have splits := hp.splitsRange
  change Value.bits 32 (positive (iters Q.splits s (div128 (addi (Lib.word d.seq) 127)))) = _
  change d.seq = b32 (Q.seqK r) at seq
  have word : Lib.word (b32 (Q.seqK r)) = W (Q.seqK r) := r32_W (by omega)
  rw [seq,word]
  have add : addi (W (Q.seqK r)) 127 = W (Q.seqK r+127) :=
    addi_W (n := 127) (by decide) (by omega)
  rw [add,div128_nat _ (by omega),iters_nat hx (by omega)]
  rfl

/-- The split count computed by the instructions agrees with the interface's capped count
when the three words came from the request arrays. -/
theorem preload_count {Q L m g d} (hp : Pre Q L m) (hg : g<L.threads)
    (first : d.first = b32 (Q.qStart ((L.ctaidOf (g/L.block)).get .z)))
    (last : d.last = b32 (Q.qStart (((L.ctaidOf (g/L.block)).get .z)+1)))
    (seq : d.seq = b32 (Q.seqK ((L.ctaidOf (g/L.block)).get .z))) :
    min 3 (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d) =
      Iface.preloadCount Q L (g/L.block) := by
  let r := (L.ctaidOf (g/L.block)).get .z
  let s := (L.ctaidOf (g/L.block)).get .x
  change d.seq = b32 (Q.seqK r) at seq
  obtain ⟨hx,_,hr⟩ := Lib.coordinate_bounds hp hg
  change r<Q.b at hr
  change s<Q.splits at hx
  have bound := (Lib.qStart_mono hp (r := r+1) (r' := Q.b) (by omega) le_rfl).trans hp.cuEnd
  have tok := hp.nTokRange
  have len := hp.qLenSeq r hr
  have seqBound := hp.seqRange r hr
  have splits := hp.splitsRange
  have mono := hp.cuMono r hr
  have word (n : Nat) (h : n<2^32) : Lib.word (b32 n) = W n := r32_W h
  have sub (a b : Nat) (hab : b≤a) (ha : a<2^32) : subValue (b32 a) (b32 b) = b32 (a-b) := by
    change Value.bits 32 (sub32 (Lib.word (b32 a)) (Lib.word (b32 b))) = _
    rw [word _ ha,word _ (by omega),sub32_W hab ha]
    rfl
  have prior : past d = W (Q.past r) := by
    unfold past
    rw [first,last,seq,sub _ _ mono (by omega)]
    change Lib.word (subValue (b32 (Q.seqK r)) (b32 (Q.qLen r))) = _
    rw [sub _ _ len (by omega)]
    exact word _ (by omega)
  have old := Nat.sub_le (Q.seqK r) (Q.qLen r)
  change Q.past r ≤ _ at old
  have cap (z : Nat) : (z-s+(Q.splits-1))/Q.splits ≤ z+Q.splits :=
    (Nat.div_le_self _ _).trans (by omega)
  change min 3 (preload Q.splits s d) = _
  unfold preload
  have plus : addi (W (Q.seqK r)) 127 = W (Q.seqK r+127) :=
    addi_W (n := 127) (by decide) (by omega)
  rw [prior,seq,word _ (by omega),plus,
    div128_nat _ (by omega),div128_nat _ (by omega)]
  have bound1 := cap (Q.past r/128)
  have bound2 := cap ((Q.seqK r+127)/128)
  change min 3 (min32 (positive (iters Q.splits s (W (Q.past r/128))))
    (positive (iters Q.splits s (W ((Q.seqK r+127)/128))))).toNat = _
  rw [iters_nat hx (by omega),iters_nat hx (by omega),min32_W (by omega) (by omega),
    toNat_W (by omega)]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue
