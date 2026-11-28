-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchFirst
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadOrdinal
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchSample
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Lib.BarZero
public import Lemmas.Flow.OrdinalCount
import Lemmas.Kernel.Safety.TableU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

/-- In every round a peer at the reader's publishing generation has the
identical site and score count whenever both prefixes have crossed the same
number of optional rendezvous. This identifies the induction on branch choices. -/
theorem scratch_peer_round {Q L m X g j a bs h i p c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (read : X.get (g,j+1)=some ⟨2252,.rd a bs⟩)
    (peer : X.IsBarrier (h,i) 0 c p) (cta : h/L.block=g/L.block) (lh : h%L.block<128)
    (ord : barOrdinal X h i=barOrdinal X g j)
    (visits : ((X.tr h).take i).countP (fun e => e.pc==2326)=
      ((X.tr g).take j).countP (fun e => e.pc==2326)) :
    p=2251 ∧ pollRound 1257 ((X.tr h).take i)=pollRound 1257 ((X.tr g).take j) := by
  obtain ⟨j',jj,get⟩ := Softmax.Export.read_sync hp hX read
  have eq : j'=j := by omega
  subst j'
  let r := pollRound 1257 ((X.tr g).take j)
  let t := pollRound 1257 ((X.tr h).take i)
  have fixG := round_barriers hp hX hf get (by simp) (by decide) (by decide)
    (n := 4*(r-1)+1) rfl
  have physG := physical_bar hp hX get (by simp) (by decide) (by decide)
  change barOrdinal X g j=_ at physG
  obtain ⟨_,one|full|half⟩ := Lib.recorded_bar hX hp.block peer
  · cases one.1
  · obtain rfl := full.2.1
    have lg := Softmax.Export.data_site hp hX read (by simp) (by dsimp; decide) (by dsimp; decide)
    have clash := peer_target hp hX peer get (List.getElem?_eq_some_iff.mp read).1
      lh lg cta ord
      (show CtaBarrier.target L.block none=.ok 8 by rw [hp.block]; rfl)
      (show CtaBarrier.target L.block (some 128)=.ok 4 by rw [hp.block]; rfl)
    contradiction
  have casesPC : ∀ q ∈ BarRow.halfZeroSites,
      (180≤q ∧ q<574) ∨ q∈[999,1012,2241,2251,2326] := by decide
  rcases casesPC _ half.2.2 with pre|soft
  · have low := Prologue.Export.preload_ordinal_bound hp hX peer pre.1 pre.2
    change barOrdinal X h i≤entryOrdinal Q L (h/L.block) at low
    rw [cta] at low
    omega
  have range : 574<p ∧ p<2331 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
    omega
  change X.get (h,i)=some ⟨p,.bar 0 c .sync⟩ at peer
  have physH := physical_bar hp hX peer (by simp) range.1 range.2
  change barOrdinal X h i=_ at physH
  rw [cta,visits] at physH
  have matchPos (u : Nat) (pos : mandatoryAt p t=some u) :
      u=4*(r-1)+1 ∧ 2≤r := by
    have fixed := round_barriers hp hX hf peer (by simp) range.1 range.2 pos
    omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
  rcases soft with rfl|rfl|rfl|rfl|rfl
  · have := matchPos (4*(t-1)+2) rfl; omega
  · have := matchPos (4*(t-1)+3) rfl; omega
  · have := matchPos (4*(t-1)) rfl; omega
  · have := matchPos (4*(t-1)+1) rfl
    exact ⟨rfl,show t=r by omega⟩
  · have := matchPos (4*(t-1)+2) rfl; omega

/-- The optional barrier is counted among actual barrier-zero events. Including
the event kind in the test makes the containment true even for synthetic events. -/
def rescaleBar (e : Event) := Execution.isBarId 0 e && e.pc==2326

public theorem count_rescale_nu {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (nu : Frame.NoUbBefore X g k) :
    ((X.tr g).take k).countP (fun x => x.pc==2326)=((X.tr g).take k).countP rescaleBar := by
  apply List.countP_congr
  intro x mem
  obtain ⟨j,jlt,atJ⟩ := List.mem_iff_getElem.mp mem
  have jk : j<k := by simp only [List.length_take] at jlt; omega
  have full : X.get (g,j)=some x := by
    change (X.tr g)[j]?=some x
    rw [←List.getElem?_take_of_lt jk]
    exact List.getElem?_eq_some_iff.mpr ⟨jlt,atJ⟩
  by_cases pos : x.pc=2326
  · have bar := Lib.zero_event hX hp.block full (nu j jk x full)
    rw [pos] at bar
    exact (by simp [rescaleBar,pos,bar,show Lib.zeroSite 2326=true by decide])
  · simp [rescaleBar,pos]

public theorem count_rescale {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some e) :
    ((X.tr g).take k).countP (fun x => x.pc==2326)=((X.tr g).take k).countP rescaleBar :=
  count_rescale_nu hp hX (Frame.noUbBefore_of_get hX get)

/-- If earlier generations agree on which ones were optional, the generation
immediately before this read publishes scratch in every participating lane.
Only strictly earlier generations occur in the induction hypothesis. -/
theorem scratch_next_publication {Q L m X g j a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (read : X.get (g,j+1)=some ⟨2252,.rd a bs⟩)
    (earlier : ∀ h, h/L.block=g/L.block → h%L.block<128 → ∀ n<barOrdinal X g j,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar g n) :
    PublishesAt L X (g/L.block) (barOrdinal X g j) := by
  intro h i p c cta lh peer ord
  obtain ⟨j',jj,get⟩ := Softmax.Export.read_sync hp hX read
  have eq : j'=j := by omega
  subst j'
  apply (scratch_peer_round hp hX hf read peer cta lh ord ?_).1
  rw [count_rescale hp hX peer,count_rescale hp hX get]
  have sub (z : Event) (test : rescaleBar z=true) : Execution.isBarId 0 z=true :=
    (Bool.and_eq_true_iff.mp test).1
  rw [countP_ordinal sub,countP_ordinal sub]
  change (List.range (barOrdinal X h i)).countP _=(List.range (barOrdinal X g j)).countP _
  rw [ord]
  exact List.countP_congr fun n mem => by rw [earlier h cta lh n (List.mem_range.mp mem)]

/-- Each observed byte of the first read is sourced at a store in the same
logical score round. No race-freedom assumption is required for provenance. -/
theorem first_round_source {Q L m X g k a bs b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩) (round : pollRound 1257 ((X.tr g).take k)=2)
    (byte : b<a.size) : ∃ h u dst ys,
      ScratchByte L X g k b a bs (entryOrdinal Q L (g/L.block)+3) h u dst ys ∧
      pollRound 1257 ((X.tr h).take u)=2 := by
  obtain ⟨ord,pub⟩ := first_publication hp hX hf read round
  obtain ⟨h,u,dst,ys,src⟩ := scratch_sample hp hX read ord pub byte
  refine ⟨h,u,dst,ys,src,?_⟩
  have bar := physical_bar hp hX src.store (by simp) (by dsimp; decide) (by dsimp; decide)
  change barOrdinal X h u=_ at bar
  have same := src.epoch
  unfold barOrdinal at same
  rw [List.take_add_one,show (X.tr h)[u]?=_ from src.store,List.countP_append] at same
  change barOrdinal X h u+0=entryOrdinal Q L (g/L.block)+3 at same
  rw [src.cta] at bar
  have low := before_rescale hp hX src.store (by omega)
  let r := pollRound 1257 ((X.tr h).take u)
  have pos := round_barriers hp hX hf src.store (by simp) (by dsimp; decide) (by dsimp; decide)
    (n := 4*(r-1)+1) rfl
  change r=2
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
