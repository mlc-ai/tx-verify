-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchAgree
public import Kernels.InklingRelDecode.Proof.Softmax.Export.PhysicalBar
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadOrdinal
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

private theorem first_sync {Q L m X g j} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.IsBarrier (g,j) 0 (some 128) 2251)
    (score : pollRound 1257 ((X.tr g).take (j+1))=2) :
    barOrdinal X g j=entryOrdinal Q L (g/L.block)+3 := by
  change X.get (g,j)=some ⟨2251,.bar 0 (some 128) .sync⟩ at get
  change ((X.tr g).take (j+1)).countP _=2 at score
  rw [List.take_add_one,show (X.tr g)[j]?=_ from get,List.countP_append] at score
  change pollRound 1257 ((X.tr g).take j)+0=2 at score
  have n := round_barriers hp hX hf get (by simp) (by decide) (by decide)
    (n := 5) (by rw [Nat.add_zero] at score; rw [score]; rfl)
  have low := before_rescale hp hX get (by omega)
  have eq := physical_bar hp hX get (by simp) (by decide) (by decide)
  dsimp only at eq
  unfold barOrdinal
  omega

private theorem half_first {Q L m X g j p c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.IsBarrier (g,j) 0 c p) (site : p∈BarRow.halfZeroSites)
    (ord : barOrdinal X g j=entryOrdinal Q L (g/L.block)+3) : p=2251 := by
  have bounds : ∀ q ∈ BarRow.halfZeroSites,
      (180≤q ∧ q<574) ∨ q∈[999,1012,2241,2251,2326] := by decide
  rcases bounds _ site with pre|soft
  · have low := Prologue.Export.preload_ordinal_bound hp hX get pre.1 pre.2
    change barOrdinal X g j≤entryOrdinal Q L (g/L.block) at low
    omega
  have range : 574<p ∧ p<2331 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
    omega
  change X.get (g,j)=some ⟨p,.bar 0 c .sync⟩ at get
  have eq := physical_bar hp hX get (by simp) range.1 range.2
  change barOrdinal X g j=_ at eq
  have low := before_rescale hp hX get (by omega)
  rw [low,Nat.add_zero] at eq
  have fixed : mandatory ((X.tr g).take j)=3 := by omega
  let r := pollRound 1257 ((X.tr g).take j)
  have mismatch (u : Nat) (atP : mandatoryAt p r=some u) : u=5 := by
    have v := round_barriers hp hX hf get (by simp) range.1 range.2 atP
    omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
  rcases soft with rfl|rfl|rfl|rfl|rfl
  · have := mismatch (4*(r-1)+2) rfl; omega
  · have := mismatch (4*(r-1)+3) rfl; omega
  · have := mismatch (4*(r-1)) rfl; omega
  · rfl
  · have := mismatch (4*(r-1)+2) rfl; omega

/-- The first scratch read (the second successful score wait) identifies a
publishing generation for every data warp in its CTA. -/
theorem first_publication {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩) (round : pollRound 1257 ((X.tr g).take k)=2) :
    let n := entryOrdinal Q L (g/L.block)+3
    barOrdinal X g k=n+1 ∧ PublishesAt L X (g/L.block) n := by
  obtain ⟨j,rfl,sync⟩ := Softmax.Export.read_sync hp hX read
  have epoch := first_sync hp hX hf sync round
  constructor
  · unfold barOrdinal
    rw [List.take_add_one,show (X.tr g)[j]?=_ from sync,List.countP_append]
    exact congrArg (·+1) epoch
  intro h i p c cta low peer ord
  obtain ⟨_,one|full|half⟩ := Lib.recorded_bar hX hp.block peer
  · cases one.1
  · obtain rfl := full.2.1
    have lg := data_site hp hX read (by simp) (by dsimp; decide) (by dsimp; decide)
    have clash := peer_target hp hX peer sync (List.getElem?_eq_some_iff.mp read).1
      low lg cta (ord.trans epoch.symm)
      (show CtaBarrier.target L.block none=.ok 8 by rw [hp.block]; rfl)
      (show CtaBarrier.target L.block (some 128)=.ok 4 by rw [hp.block]; rfl)
    contradiction
  · exact half_first hp hX hf peer half.2.2 (cta ▸ ord)

/-- Across all four Softmax warps, first-round readers of a single slot
receive identical bytes when their stores agree. -/
theorem scratch_first_agree {Q L m X g k a bs h j d ys}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : StoreAgree L X (entryOrdinal Q L (g/L.block)+3))
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩)
    (peer : X.get (h,j)=some ⟨2252,.rd d ys⟩) (cta : g/L.block=h/L.block)
    (slot : g%L.block%4=h%L.block%4) (round : pollRound 1257 ((X.tr g).take k)=2)
    (round' : pollRound 1257 ((X.tr h).take j)=2) : bs=ys := by
  obtain ⟨ord,pub⟩ := first_publication hp hX hf read round
  obtain ⟨ord',_⟩ := first_publication hp hX hf peer round'
  exact scratch_reads_agree hp hX agree read peer cta slot ord (cta ▸ ord') pub

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
