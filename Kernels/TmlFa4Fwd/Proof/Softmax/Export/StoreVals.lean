-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Stores
public import Kernels.TmlFa4Fwd.Proof.SmWarp.PrefixReads
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataFiring
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAccSite
import Lemmas.Order.OrderBaseCausality

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i a : Nat} {vals : List Value}

theorem store_state {pc} (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    (he : X.get (g,i) = some ⟨pc,.tc (.st a vals .s32x32b)⟩)
    (hld : ∀ j < i, ∀ b xs sh, X.TLd (g,j) b xs sh → Values.F32s xs) :
    ∃ r q v k acc n, Frame.stateAt (threadD p L) X g i =
      some (some (.inr ⟨.softmax, (⟨.pst r q,v,k,acc⟩ : D)⟩,n)) := by
  obtain ⟨d,n,_,_,_, hc,_⟩ := role_state hp hX hFw hw he (.inr (.inl ⟨_,_,_,rfl⟩))
  obtain ⟨⟨site,v,k,acc⟩,hs,_⟩ := SmWarp.lift_state hp hc
    (SmWarp.alive_of_prefix_reads hp hX hw hb he hld)
  obtain ⟨r,q,eq⟩ := soft_st_site (SmWarp.data_event hp hX (SmWarp.storeSafe hp g) he hs).1.1
  change site = _ at eq
  subst site
  exact ⟨r,q,v,k,acc,n,hs⟩

theorem softStores_of_bias (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hb : SmWarp.BiasReadHandoff p L X) : Values.SoftStores L X := by
  rintro g i a vals _ hw ⟨pc,he⟩ hbefore w hm
  obtain ⟨r,q,v,k,acc,_,hs⟩ := store_state hp hX hFw hw hb he (by
    intro j hj b xs sh hl
    obtain rfl := (soft_ld hp hX hFw hw hl).1
    exact hbefore _ _ _ hl rfl (.single (.inl (.single (.inl
      (po_of_not_access (e := (g,j)) (f := (g,i)) rfl hj (len_of_get he) (by rw [he]; rfl)))))))
  obtain ⟨_,_,hat,hf⟩ := SmWarp.data_firing hp hX he hs
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hm
  exact ⟨_,_,(Data.store_fired hp g v r q k acc hat hf rfl).2 j hj⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
