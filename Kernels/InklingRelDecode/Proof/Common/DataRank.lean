-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Prologue.Measure
public import Kernels.InklingRelDecode.Proof.Softmax.MeasureNext
public import Kernels.InklingRelDecode.Proof.Epilogue.MeasureNext
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

def softMaxRank := 91*2^31+156

def softRank {e L g} : (softCode e L g).D → Nat
  | .inl d => 75 + min softMaxRank (Softmax.measure e d)
  | .inr ⟨_,d⟩ => Epilogue.measure d

def dataRank {Q L g w} : (dataCode Q L g w).D → Nat
  | .inl d => 75 + softMaxRank + Prologue.measure d
  | .inr ⟨_,s⟩ => softRank s

private theorem soft_enter_le {e L g} (d : Softmax.Control.D) :
    softRank (Code.enter (Softmax.Control.code e L g)
      (fun _ : Unit => Epilogue.Control.code (epiEntry e (g%L.block)) L g) epiExit d) ≤
      75+min softMaxRank (Softmax.measure e d) := by
  unfold Code.enter epiExit
  split <;> first | exact Nat.le_refl _ |
    exact (Epilogue.measure_bound _).trans (Nat.le_add_right ..)

private theorem soft_rank_next {e L g s sn ev} (hi : (softCode e L g).inv s)
    (move : (softCode e L g).next s ev=some (some sn)) :
    softRank sn+ev.counts.toNat≤softRank s := by
  rcases s with d|⟨_,d⟩
  · obtain ⟨dn,step,rfl⟩ := Code.glue_inl_some move
    have le := Softmax.measure_next hi.1 step
    have cap : Softmax.measure e d ≤ softMaxRank := Softmax.measure_bound hi.1
    have reach := soft_enter_le (e := e) (L := L) (g := g) dn
    change _≤75+min softMaxRank (Softmax.measure e d)
    omega
  · obtain ⟨dn,step,rfl⟩ := Code.glue_inr_some move
    exact Epilogue.measure_next step

private theorem pro_enter_le {Q L g w} (d : Prologue.Control.D) :
    dataRank (Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
      (dataExit Q L g w) d) ≤ 75+softMaxRank+Prologue.measure d := by
  unfold Code.enter dataExit
  split
  · change 75+min _ _≤_
    omega
  · rfl

theorem data_rank_next {Q L g w s sn ev} (hi : (dataCode Q L g w).inv s)
    (move : (dataCode Q L g w).next s ev=some (some sn)) :
    dataRank sn+ev.counts.toNat≤dataRank s := by
  rcases s with d|⟨e,s⟩
  · obtain ⟨dn,step,rfl⟩ := Code.glue_inl_some move
    have le := Prologue.measure_next step
    have reach := pro_enter_le (Q := Q) (L := L) (g := g) (w := w) dn
    have cnt : ev.counts.toNat≤1 := by cases ev.counts <;> decide
    change _≤75+softMaxRank+Prologue.measure d
    omega
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some move
    exact soft_rank_next hi step

end PTX.Kernels.InklingRelDecode.Proof
