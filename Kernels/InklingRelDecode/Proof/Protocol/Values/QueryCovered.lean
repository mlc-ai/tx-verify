-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.Regions
import Kernels.InklingRelDecode.Proof.Common.Export.FirstBar
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Protocol.Shared.QueryFence
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryBefore

@[expose] public section

/-! # The query tile is covered by the prologue's query stores

Every lane of an MMA's CTA crosses the first barrier-one rendezvous (`first_arrival`) after all
its query stores (`query_before_sync`), and every byte of the tile is a byte of one store
(`qOff_onto`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every byte of the query tile of an MMA's CTA is covered by a query store.** -/
theorem query_covered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {h f pc dst s acc mask l}
    (mma : X.get (h,f) = some ⟨pc,.tc (.mma dst s acc mask)⟩) (inq : Iface.InQ L l)
    (cta : l.cta = h / L.block) :
    ∃ g k a bs, ∃ i : Fin 8, X.get (g,k) = some ⟨526+6*i.val,.wr a bs⟩ ∧ a.Covers l := by
  obtain ⟨-,range,-⟩ := Mma.Export.operands_all hp hX hf mma
  have flen : f < (X.tr h).length := (List.getElem?_eq_some_iff.mp mma).1
  have late := Export.after_initialization hp hX mma
    (fun _ => nofun) (by
      simp only [Export.afterInit]; simp; omega)
  obtain ⟨space,qlo,qhi⟩ := inq
  obtain ⟨t,i,w,b,ht,hi,hw,hb,eq⟩ := Lib.qOff_onto (off := l.addr - (L.sharedBase + 196608))
    (by omega)
  have blk : L.block = 256 := hp.block
  obtain ⟨g, gdiv, gmod⟩ : ∃ g, g / L.block = h / L.block ∧ g % L.block = t :=
    ⟨h / L.block * L.block + t, by rw [blk]; omega, by rw [blk]; omega⟩
  obtain ⟨u,p,sync,zero⟩ := Shared.first_arrival (g := g) hp hX flen
    (by omega) gdiv
  have lo := Export.first_barrier_pc hp hX sync zero
    (by omega)
  subst lo
  obtain ⟨v,-,a,bs,get,loc,size⟩ := Prologue.Export.query_before_sync hp hX sync ⟨i,hi⟩ ⟨w,hw⟩
  refine ⟨g,v,a,bs,⟨i,hi⟩,get,?_⟩
  have bound := (Lib.qSwz_spec t ht).1
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [loc, size, gmod, gdiv] <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
