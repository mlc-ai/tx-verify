-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerCall
public import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
public import Kernels.InklingRelDecode.Proof.Loader.MeasureNext
public import Kernels.InklingRelDecode.Proof.Mma.MeasureNext
public import Kernels.InklingRelDecode.Proof.Dispatch.Measure
import Kernels.InklingRelDecode.Proof.Common.LaunchLane

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

noncomputable def workerRank {Q L g w x} : (workerCode Q L g w x).D → Nat
  | .inl d => Dispatch.measure d
  | .inr ⟨.loader _,d⟩ => 8+Loader.measure d
  | .inr ⟨.mma _,d⟩ => 8+Mma.measure d

private theorem enter_le {Q L g w x} (d : Dispatch.D) :
    workerRank (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry d) ≤ Dispatch.measure d := by
  obtain ⟨s,r⟩ := d
  cases s <;> try exact Nat.le_refl _
  · change 8+(22*2^32+6)≤Dispatch.callBound+10
    decide +kernel
  · change 8+(30*(2^32+2)+2)≤Dispatch.callBound+10
    decide +kernel

private theorem return_le {Q L g w x i} (d : (workerFrag Q L g w x i).D) :
    workerRank (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) i d) ≤
      @workerRank Q L g w x (.inr ⟨i,d⟩) := by
  cases i <;> obtain ⟨s,rest⟩ := d <;> cases s <;> exact Nat.le_refl _

theorem worker_rank_next {Q L m X g k w x d dn n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),d⟩,n))) (hi : (workerCode Q L g w x).inv d)
    (move : (workerCode Q L g w x).next d ev=some (some dn)) :
    workerRank dn+ev.counts.toNat≤workerRank d := by
  have hg := lt_of_get hX he
  rcases d with d|⟨i,s⟩
  · change (Dispatch.next L g d ev).map _ = _ at move
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp move
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    have rank := Dispatch.measure_next (L := L) (g := g) (d := d) ?_ step
    · have reach := enter_le (Q := Q) (L := L) (g := g) (w := w) (x := x) sn
      have cnt : ev.counts.toNat≤1 := by cases ev.counts <;> decide
      change _≤Dispatch.measure d
      omega
    · intro read later a bs kind
      rw [dispatch_bytes hp hX words he hs read kind,ite_eq_right later]
      have hi : g%L.block/32<8 := by rw [hp.block]; omega
      let j : Fin 4 := ⟨g%L.block/32-4,by omega⟩
      exact Dispatch.role_target j false
  · change ((workerFrag Q L g w x i).next s ev).map _ = _ at move
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp move
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    apply Nat.le_trans (Nat.add_le_add_right (return_le sn) _)
    cases i with
    | loader r =>
      have ref := (reached_table hf hg (noUbBefore_of_get hX he) hs).2.2.1
      have hh : iterCount Q L (g/L.block)<2^31 := Lib.blocksOf_lt hp hg
      have dec := Loader.measure_count hh ref step
      change 8+Loader.measure sn+ev.counts.toNat≤8+Loader.measure s
      cases e : ev.counts <;> simp_all
    | mma r =>
      have dec := Mma.measure_next hi.1 step
      change 8+Mma.measure sn+ev.counts.toNat≤8+Mma.measure s
      omega

end PTX.Kernels.InklingRelDecode.Proof
