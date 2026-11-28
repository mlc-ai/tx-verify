-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.CommitBudget
import Kernels.InklingRelDecode.Proof.Loader.Export.PacketIndex
import Kernels.InklingRelDecode.Proof.Loader.Export.Count
import Lemmas.Protocol.CountNth
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow MbarRow


/-- Count events by their distinct packet site and slot visit. The trace may end in the
middle of the packet, and the first recurrent block need not use slot zero. -/
theorem packet_budget {Q L m X g k e s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (words : RoleBytes L X) (warp : g%L.block/32=6)
    (he : X.get (g,k)=some e) (f : Event → Bool) (endUse : f e) (pcs : List Nat)
    (subset : ∀ p ∈ pcs, p ∈ [2378,2389,2391,2394,2396,2404,2406,2410,2412])
    (shape : ∀ {j v}, X.get (g,j)=some v → f v →
      let n := pollRound 2374 ((X.tr g).take j)
      v.pc ∈ pcs ∧ (∀ z, v.kind≠.ub z) ∧ v.counts ∧ 0<n ∧
        (Iface.preloadCount Q L (g/L.block)+n-1)%3=s.val) :
    ((X.tr g).take k).countP f+1 ≤ pcs.toFinset.card *
      okPolls (Ring.empty.obj L (g/L.block) s) ((X.tr g).take k) := by
  classical
  let n (j : Nat) := pollRound 2374 ((X.tr g).take j)
  let pre := Iface.preloadCount Q L (g/L.block)
  let ordinal (j : Nat) := (pre+n j+2-s.val)/3-(pre+2-s.val)/3-1
  let used := (Finset.range (k+1)).filter fun j => ((X.tr g)[j]?).any f
  let pc (j : Nat) := ((X.tr g)[j]?.map Event.pc).getD 0
  have info {j : Nat} (mem : j ∈ used) : ∃ v, X.get (g,j)=some v ∧ f v ∧ pc j=v.pc ∧ j≤k := by
    obtain ⟨lt,ok⟩ := Finset.mem_filter.mp mem
    cases get : (X.tr g)[j]? with
    | none => rw [get] at ok; cases ok
    | some v =>
      rw [get] at ok
      exact ⟨v,get,ok,by simp [pc,get],Nat.le_of_lt_succ (Finset.mem_range.mp lt)⟩
  have upper : used.card ≤ (pcs.toFinset ×ˢ Finset.range (visits pre (n k) s)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (pc j,ordinal j))
    · intro j hj
      obtain ⟨v,get,use,site,le⟩ := info hj
      obtain ⟨hit,_,_,pos,slot⟩ := shape get use
      apply Finset.mem_product.mpr
      refine ⟨List.mem_toFinset.mpr (show pc j ∈ pcs from site.symm ▸ hit),Finset.mem_range.mpr ?_⟩
      change 0<n j at pos
      change (pre+n j-1)%3=s.val at slot
      have mono : n j≤n k := countP_take_mono _ _ le
      change ordinal j < visits pre (n k) s
      unfold ordinal visits
      have := s.isLt
      omega
    · intro j hj i hi eq
      obtain ⟨v,get,use,site,_⟩ := info hj
      obtain ⟨w,get',use',site',_⟩ := info hi
      obtain ⟨hit,nu,counts,pos,slot⟩ := shape get use
      obtain ⟨_,nu',counts',pos',slot'⟩ := shape get' use'
      obtain ⟨pcEq,ordEq⟩ := Prod.mk.inj eq
      apply Loader.Export.packet_unique hp hX hf words warp get get' (subset _ hit)
        (site.symm.trans (pcEq.trans site')) nu nu' counts counts'
      change 0<n j at pos
      change 0<n i at pos'
      change (pre+n j-1)%3=s.val at slot
      change (pre+n i-1)%3=s.val at slot'
      change ordinal j=ordinal i at ordEq
      unfold ordinal at ordEq
      change n j=n i
      have := s.isLt
      omega
  have card := MbarRing.Slot.countP_take_card (X.tr g) f (k+1)
  change _=used.card at card
  rw [←card,countP_take_succ he endUse,Finset.card_product,Finset.card_range] at upper
  rw [poll_count (r := .empty) rows (Frame.lt_of_get hX he) warp s k]
  exact upper

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
