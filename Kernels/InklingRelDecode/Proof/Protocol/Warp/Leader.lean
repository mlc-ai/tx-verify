-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Lemmas.Order.ElectOrdinal

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
open PTX PTX.Flow

/-- The chosen producer wins all elections in its trace, also when that trace has none.
An observed election supplies the actual winning lane through its dependency on the mask. -/
theorem leader_wins {Q L m X c w} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hc : c<L.grid) (hw : w<8) :
    let y := KV.leader L X c w
    ElectLead L y (X.tr y) := by
  dsimp only
  let y := KV.leader L X c w
  obtain ⟨hy,cta,warp⟩ := KV.leader_warp (X := X) hp hc hw
  intro ev mem mask inst ld kind
  obtain ⟨j,he⟩ := elect_of_mem mem kind
  have member := (hX.elect.1 _ _ _ _ _ he).2.2
  obtain ⟨_,_,k,p,ld',rfl,partner⟩ := elect_ready hX he _ (elect_need_mem he member)
  let t := warpLane L y ld
  have hl : ld<32 := member.1
  have tid : laneOf L t=ld ∧ t/L.block=c ∧ t%L.block/32=w := by
    change y/L.block=c at cta
    change y%L.block/32=w at warp
    simp only [t,warpLane,laneOf,hp.block] at *
    omega
  have ht := (hX.elect.1 _ _ _ _ _ partner).1
  have same : SameWarp L y t := ⟨⟨hy,ht,cta.trans tid.2.1.symm⟩,warp.trans tid.2.2.symm⟩
  have eq := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ he partner same).2.2.1
  have elect : Elected (X.tr t) (laneOf L t) :=
    ⟨_,List.mem_of_getElem? (show (X.tr t)[k]?=_ from partner),mask,inst,
      congrArg (Kind.elect mask inst) (eq.symm.trans tid.1.symm)⟩
  have sel := KV.leader_eq hX ht elect
  rw [tid.2.1,tid.2.2] at sel
  exact tid.1.symm.trans (congrArg (laneOf L) sel.symm)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
