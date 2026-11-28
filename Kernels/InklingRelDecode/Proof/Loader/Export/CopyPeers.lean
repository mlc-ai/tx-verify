-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Loader.Export.Coll
import Kernels.InklingRelDecode.Proof.Loader.Export.NoElection
import Kernels.InklingRelDecode.Proof.Loader.Export.Count
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
import Lemmas.Flow.NthEv

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Frame

/-- Before a copy, every peer passed the empty poll for this packet. Its
full-mask election in the same round precedes the copy in dependency order. -/
public theorem copy_peers {Q L m X g k pc a sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (warp : g%L.block/32=6)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue a sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) {h} (hw : SameWarp L g h) :
    ∃ j, j<(X.tr h).length ∧ pollRound 2374 ((X.tr h).take j)=pollRound 2374 ((X.tr g).take k) ∧
      Relation.TransGen (DepStep L kernel X) (.thread (h,j),false) (.thread (g,k),false) := by
  have bounds : ∀ p ∈ [2389,2391,2394,2396,2404,2406,2410,2412], 2344<p ∧ p<2422 := by decide
  obtain ⟨w,x,r,d,n,hs,pos⟩ := loader_state hp hX hf he (by simp)
    (bounds _ site).1 (bounds _ site).2
  have bal := loader_balance hp hX hf (lt_of_get hX he) warp (noUbBefore_of_get hX he) hs
  have ord : n .elect=((X.tr g).take k).countP isElectEv := fcount hs _
  have round : n (.poll 2374)=pollRound 2374 ((X.tr g).take k) := fcount hs _
  have ranges (s : Site) : s.pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412] → owed s<4 := by
    cases s <;> repeat' first | decide +kernel | (rename_i i; revert i)
  have debt := ranges d.site (pos ▸ site)
  have posRound := (packet_credit hp hX hf warp he (by
    change pc ∈ _; exact List.mem_cons_of_mem _ site) (.inr ⟨_,_,rfl⟩)).1
  let r := pollRound 2374 ((X.tr g).take k)
  obtain ⟨u,uk,⟨p,kd⟩,get,kind,num⟩ := exists_nth isElectEv (X.tr g)
    (show 4*(r-1)<((X.tr g).take k).countP isElectEv from by dsimp [r]; omega)
  cases kd <;> try contradiction
  rename_i mask inst ld
  obtain ⟨_,peers⟩ := electionPeers hp hX hf warp get
  obtain ⟨j,peer,same⟩ := peers h hw
  have eq := election_round hp hX hf (hw.2 ▸ warp) peer
  exact ⟨j,(List.getElem?_eq_some_iff.mp peer).1,by rw [same,num] at eq; dsimp [r] at eq; omega,
    elect_depStep (e := (h,j)) (f := (g,u)) hX (sameWarp_symm hw) peer get uk
      (List.getElem?_eq_some_iff.mp he).1⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
