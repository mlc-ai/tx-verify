-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasRecorded
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasCredit
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.ReadRegion
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasHistory
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.FirstMask
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {t : Tile}

private theorem read_four_credit {i pc : Nat} {a : Fin 4 → Acc} {bs : Fin 4 → List (Option Byte)}
    (he : ∀ j : Fin 4, X.get (g,i+j.val) = some ⟨pc,.rd (a j) (bs j)⟩) (st : Nat) :
    Tm.sPolls L X g st (i+4) = Tm.sPolls L X g st i := by
  have step (j : Fin 4) : Tm.sPolls L X g st (i+j.val+1) = Tm.sPolls L X g st (i+j.val) := by
    obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.mp (he j)
    unfold Tm.sPolls
    rw [List.take_succ_eq_append_getElem hi,eq,okPolls_snoc]
    rfl
  exact (step 3).trans ((step 2).trans ((step 1).trans (step 0)))

/-- The carried bias registers at a P store, with the first round's mask applied. -/
theorem soft_stored_bias (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8)
    (loads : ∀ {id a vs}, X.TLd id a vs .s32x32b → F32s vs)
    (ht : tileOf p L (g/L.block) = some t) (hv : t.Valid p (Prologue.warpIndex L g/4) (rowIx L g))
    {i z q v k acc u e} (hs : softState p L X g i = some ⟨.pst (rdOf z) q,v,k,acc⟩)
    (he : X.get (g,i) = some e)
    (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1)
    (first : (u=0) ↔ z=false) (hu : u<t.n) (col : Fin 128) :
    let row := t.rowOf (Prologue.warpIndex L g/4) (rowIx L g)
    Data.loadedBias p L g v (rdOf z) col.val =
      if t.key u col.val < p.keyCount t.batch row then
        some (biasAt p t.batch t.head row (t.key u col.val)) else none := by
  intro row
  let b : Fin 16 := ⟨col.val/8,by have := col.isLt; omega⟩
  let key := t.key u col.val
  let target := if key < p.keyCount t.batch row then
    some (biasAt p t.batch t.head row key) else none
  let Q (i : Nat) (d : D) := Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1 →
    (if u=0 ∧ p.keyCount t.batch row ≤ key then none else Data.loadedBias p L g d.v .bias col.val)
      = target
  obtain ⟨cut,store,frame⟩ := bias_region z b (lz L g)
  have carried : Q i ⟨.pst (rdOf z) q,v,k,acc⟩ := by
    apply soft_region_induct hp _ _ cut Q _ (List.getElem?_eq_some_iff.mp he).1.le hs (store q)
    intro j d d' e' get old hn inside ih
    rcases ih with ⟨prev,ih⟩ | src
    · obtain ⟨body,off,other⟩ := frame _ prev
      obtain ⟨bk,br⟩ := Data.bias_frame hn body b other
      have eqb : (⟨col.val/8%16,Nat.mod_lt _ (by decide)⟩ : Fin 16) = b :=
        Fin.ext (Nat.mod_eq_of_lt b.isLt)
      intro cred
      have prevCred := (soft_credit_step hw get (softState_event hp hX get old) off).symm.trans cred
      simpa only [Data.loadedBias,bpf,eqb,bk,br] using ih prevCred
    · have site := beq_iff_eq.mp src
      obtain ⟨s,v0,k0,acc0⟩ := d
      change s = .bld z b at site
      subst s
      have last := bias_leaves_at_three hn (fun h => by
        rw [h] at inside; simp [readRegion] at inside)
      obtain ⟨base,pos,start,words⟩ := soft_bias_history hp hX get old
      have read (x : Fin 4) := words x.val (by have := x.isLt; omega)
      choose a bs reads using read
      have endpos : j+1 = base+4 := by omega
      intro cred
      have c0 := soft_bias_credit hp hX hf hw (reads 0) start
      have c4 := read_four_credit (L := L) reads (Prologue.warpIndex L g/4)
      rw [endpos,c4] at cred
      have ord : barOrd X g base (stageId (Prologue.warpIndex L g/4)) = u :=
        Nat.succ.inj (c0.symm.trans cred)
      obtain ⟨out,state,vals⟩ := soft_bias_recorded hp hX hf hw start reads ht hv
        (fun _ _ _ xs sh ld => by obtain rfl := (soft_ld hp hX hf hw ld).1; exact loads ld)
        (by rwa [ord])
      have step := softState_step hp get old hn
      rw [endpos,state] at step
      cases Option.some.inj step
      let x : Fin 4 := ⟨col.val%8/2,by omega⟩
      let y : Fin 2 := ⟨col.val%2,Nat.mod_lt _ (by decide)⟩
      have splitCol : 8*b.val+(2*x.val+y.val) = col.val := by dsimp [b,x,y]; omega
      simpa only [ord,splitCol] using vals x y
  have bias := carried credit
  cases z
  · obtain rfl := first.mpr rfl
    let c : Fin 4 := ⟨col.val/32,by have := col.isLt; omega⟩
    let x : Fin 32 := ⟨col.val%32,Nat.mod_lt _ (by decide)⟩
    have mask := soft_first_mask hp hX hw he hs ht hv c x
    have decomp : 32*c.val+x.val = col.val := by dsimp [c,x]; omega
    rw [decomp] at mask
    change Data.diagonal _ (col.val/32) (col.val%32) = decide (key < p.keyCount t.batch row) at mask
    change (if Data.diagonal _ _ _ then Data.loadedBias p L g v .bias _ else none) = target
    rw [mask]
    by_cases hk : key < p.keyCount t.batch row
    · simpa only [hk,decide_true,ite_true,not_le_of_gt hk,and_false,ite_false] using bias
    · simp only [hk,decide_false,Bool.false_eq_true,ite_false,target]
  · have later : u ≠ 0 := fun h => Bool.noConfusion (first.mp h)
    change Data.loadedBias p L g v .bias col.val = target
    simpa only [later,false_and,ite_false] using bias

end PTX.Kernels.TmlFa4Fwd.Proof.Values
