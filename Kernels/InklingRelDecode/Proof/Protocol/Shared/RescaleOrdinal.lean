-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchLater
public import Kernels.InklingRelDecode.Proof.Softmax.Export.ReadRound
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData

import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

private theorem mandatory_step {es : List Event} {i : Nat} {e : Event}
    (get : es[i]?=some e) (pc : e.pc=2251) :
    mandatory (es.take (i+1))=mandatory (es.take i)+1 := by
  unfold mandatory
  rw [List.take_add_one,get]
  simp [pc]
  omega

private theorem mandatory_mono' (es : List Event) {j k : Nat} (le : j≤k) :
    mandatory (es.take j)≤mandatory (es.take k) := by
  unfold mandatory
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (countP_take_mono _ es le)
    (countP_take_mono _ es le)) (countP_take_mono _ es le)) (countP_take_mono _ es le)

private theorem position_2251 {Q L m X g i c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,i)=some ⟨2251,.bar 0 c .sync⟩) :
    mandatory ((X.tr g).take i)+2=4*(pollRound 1257 ((X.tr g).take i)-1)+1 :=
  round_barriers hp hX hf get (fun _ => nofun) (by show 574<2251; decide)
    (by show 2251<2331; decide) (by simp [mandatoryAt])

/-- In one lane, two publishing syncs in the same score round are one event. -/
theorem sync_unique {Q L m X g i i' c c'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (one : X.get (g,i)=some ⟨2251,.bar 0 c .sync⟩) (two : X.get (g,i')=some ⟨2251,.bar 0 c' .sync⟩)
    (round : pollRound 1257 ((X.tr g).take i)=pollRound 1257 ((X.tr g).take i')) : i=i' := by
  have a := position_2251 hp hX hf one
  have b := position_2251 hp hX hf two
  rw [round] at a
  have step {i i' c} (one : X.get (g,i)=some ⟨2251,.bar 0 c .sync⟩) (lt : i < i')
      (eq : mandatory ((X.tr g).take i)=mandatory ((X.tr g).take i')) : False := by
    have s := mandatory_step (es := X.tr g) (i := i) one rfl
    have m := mandatory_mono' (X.tr g) (show i+1 ≤ i' from lt)
    omega
  rcases Nat.lt_trichotomy i i' with lt|eq|gt
  · exact (step one lt (by omega)).elim
  · exact eq
  · exact (step two gt (by omega)).elim

private theorem bar_count {X : Execution} {g u pc c} {md : BarMode}
    (get : X.get (g,u)=some ⟨pc,.bar 0 c md⟩) :
    ((X.tr g).take (u+1)).countP (Execution.isBarId 0)=
      ((X.tr g).take u).countP (Execution.isBarId 0)+1 := by
  have : (X.tr g)[u]?=some ⟨pc,.bar 0 c md⟩ := get
  rw [List.take_add_one,this,List.countP_append]
  simp [Execution.isBarId]

private theorem bar_round {X : Execution} {g u pc c} {md : BarMode}
    (get : X.get (g,u)=some ⟨pc,.bar 0 c md⟩) :
    pollRound 1257 ((X.tr g).take (u+1))=pollRound 1257 ((X.tr g).take u) := by
  have : (X.tr g)[u]?=some ⟨pc,.bar 0 c md⟩ := get
  unfold pollRound
  rw [List.take_add_one,this,List.countP_append]
  simp [okPollAt]

/-- The publishing sync, the scratch read and the two decision shuffles of a lane lie in one
barrier-zero ordinal. -/
theorem decision_sync {Q L m X g k a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ⟨2255,.shfl .bfly a b c recv ok⟩) :
    ∃ j u ac bs, k=j+2 ∧ X.get (g,j)=some ⟨2252,.rd ac bs⟩ ∧ u+1=j ∧
      X.get (g,u)=some ⟨2251,.bar 0 (some 128) .sync⟩ ∧
      barOrdinal X g j=barOrdinal X g u+1 ∧ barOrdinal X g k=barOrdinal X g j := by
  obtain ⟨j,ac,bs,p,ok1,rfl,rd,sh,-,-,-⟩ := rescale_data hp hX get
  obtain ⟨u,eq,sync⟩ := read_sync hp hX rd
  refine ⟨j,u,ac,bs,rfl,rd,eq,sync,?_,?_⟩
  · rw [←eq]
    exact bar_count sync
  · have a1 : (X.tr g)[j]?=some ⟨2252,.rd ac bs⟩ := rd
    have a2 : (X.tr g)[j+1]?=some ⟨2253,.shfl .bfly (Lib.loadWord bs) 2 31 p ok1⟩ := sh
    unfold barOrdinal
    rw [List.take_add_one,List.take_add_one,a1,a2]
    simp [List.countP_append,Execution.isBarId]

/-- Rescale visits agree below a barrier ordinal: the counts of the optional rendezvous before two
events at the same ordinal are equal. -/
theorem visits_equal {Q L m X g j h i e e'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,j)=some e) (peer : X.get (h,i)=some e')
    (cta : h/L.block=g/L.block) (lh : h%L.block<128)
    (ord : barOrdinal X h i=barOrdinal X g j)
    (earlier : ∀ h, h/L.block=g/L.block → h%L.block<128 → ∀ n<barOrdinal X g j,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar g n) :
    ((X.tr h).take i).countP (fun e => e.pc==2326)=
      ((X.tr g).take j).countP (fun e => e.pc==2326) := by
  rw [count_rescale hp hX peer,count_rescale hp hX get]
  have sub (z : Event) (test : rescaleBar z=true) : Execution.isBarId 0 z=true :=
    (Bool.and_eq_true_iff.mp test).1
  rw [countP_ordinal sub,countP_ordinal sub]
  change (List.range (barOrdinal X h i)).countP _=(List.range (barOrdinal X g j)).countP _
  rw [ord]
  exact List.countP_congr fun n mem => by rw [earlier h cta lh n (List.mem_range.mp mem)]

/-- A scratch read of a data lane with the same number of earlier shuffles as the read of the
lane `x` has the same barrier-zero ordinal. -/
theorem read_ordinal {Q L m X x j u ac bs q jq a' bs'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (read : X.get (x,j)=some ⟨2252,.rd ac bs⟩) (hu : u+1=j)
    (sync : X.get (x,u)=some ⟨2251,.bar 0 (some 128) .sync⟩)
    (earlier : ∀ h, h/L.block=x/L.block → h%L.block<128 → ∀ n<barOrdinal X x u,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar x n)
    (lx : x%L.block<128) (lq : q%L.block<128) (cta : q/L.block=x/L.block)
    (read' : X.get (q,jq)=some ⟨2252,.rd a' bs'⟩)
    (count : ((X.tr q).take jq).countP Execution.isShfl=((X.tr x).take j).countP Execution.isShfl) :
    barOrdinal X q jq=barOrdinal X x j := by
  subst hu
  have bump : barOrdinal X x (u+1)=barOrdinal X x u+1 := bar_count sync
  have len := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨iE,pE,cE,bar,ordE⟩ := data_arrival hp hX sync len lx lq cta (fun k p ex => by
    have := scratch_exit_ordinal hp hX read ex lx lq cta.symm
    omega)
  have barE : X.get (q,iE)=some ⟨pE,.bar 0 cE .sync⟩ := bar
  obtain ⟨pe,round⟩ := scratch_peer_round hp hX hf read bar cta lq ordE
    (visits_equal hp hX sync barE cta lq ordE earlier)
  subst pe
  obtain ⟨jq0,hj,syncq⟩ := read_sync hp hX read'
  subst hj
  have same := read_round hp hX hf read read' cta.symm count.symm
  rw [bar_round sync] at same
  rw [bar_round syncq] at same
  have idx := sync_unique hp hX hf barE syncq (by rw [round,same])
  subst idx
  have bq : barOrdinal X q (iE+1)=barOrdinal X q iE+1 := bar_count syncq
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
