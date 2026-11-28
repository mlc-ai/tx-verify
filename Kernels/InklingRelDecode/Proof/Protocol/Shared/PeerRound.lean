-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
public import Kernels.InklingRelDecode.Proof.Softmax.Export.BarPolls
public import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadOrdinal
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

private theorem bar_keeps {X : Execution} {g u pc c} {md : BarMode} (key : Nat)
    (get : X.get (g,u)=some ⟨pc,.bar 0 c md⟩) :
    pollRound key ((X.tr g).take (u+1))=pollRound key ((X.tr g).take u) := by
  have : (X.tr g)[u]?=some ⟨pc,.bar 0 c md⟩ := get
  unfold pollRound
  rw [List.take_add_one,this,List.countP_append]
  simp [okPollAt]

private theorem half_sites : ∀ q ∈ BarRow.halfZeroSites,
    (180≤q ∧ q<574) ∨ q∈[999,1012,2241,2251,2326] := by decide

/-- A data lane at the barrier-zero ordinal of lane zero's last rendezvous of a round is at that
rendezvous of the same round. -/
private theorem same_round {Q L m X x y ix iy n cx cy pcY} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (uni : Uniform L X (x/L.block) n) (lx : x%L.block<128) (ly : y%L.block<128)
    (cta : y/L.block=x/L.block) (passed : ix+1<(X.tr x).length)
    (bx : X.get (x,ix)=some ⟨1012,.bar 0 cx .sync⟩) (ordx : barOrdinal X x ix=n)
    (byy : X.get (y,iy)=some ⟨pcY,.bar 0 cy .sync⟩) (ordy : barOrdinal X y iy=n) :
    pcY=1012 ∧ pollRound 1257 ((X.tr y).take iy)=pollRound 1257 ((X.tr x).take ix) := by
  have lo : 574<1012 := by decide
  have hi : 1012<2331 := by decide
  have visits := visits_equal hp hX bx byy cta ly (by omega)
    (fun h ch lh n' lt => uni h x ch lh rfl lx n' (by omega))
  have px := physical_bar hp hX bx (by simp) lo hi
  have rx : mandatory ((X.tr x).take ix)+2=4*(pollRound 1257 ((X.tr x).take ix)-1)+3 :=
    round_barriers hp hX hf bx (fun _ => nofun) lo hi (by simp [mandatoryAt])
  have posx := bar_polls hp hX hf bx (by simp)
  simp only [barOrdinal] at ordx ordy
  have half : pcY∈BarRow.halfZeroSites := by
    rcases same_kind hp hX byy bx passed lx ly cta (by simp only [barOrdinal]; omega) with
      ⟨-,none,-,bad⟩|⟨hh,-⟩
    · exact absurd bad (by decide)
    · exact hh
  rcases half_sites pcY half with pro|soft
  · have bound := Prologue.Export.preload_ordinal_bound hp hX (show X.IsBarrier (y,iy) 0 cy pcY
      from byy) pro.1 pro.2
    rw [cta] at bound
    simp only [entryOrdinal] at px
    omega
  have range : 574<pcY ∧ pcY<2331 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
    omega
  have py := physical_bar hp hX byy (by simp) range.1 range.2
  rw [cta] at py
  have ry (t : Nat) (site : mandatoryAt pcY (pollRound 1257 ((X.tr y).take iy))=some t) :
      mandatory ((X.tr y).take iy)+2=t :=
    round_barriers hp hX hf byy (fun _ => nofun) range.1 range.2 site
  simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
  simp only [entryOrdinal] at px py
  rcases soft with rfl|rfl|rfl|rfl|rfl
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)+2) (by simp [mandatoryAt])
    omega
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)+3) (by simp [mandatoryAt])
    have posy := bar_polls hp hX hf byy (by simp)
    exact ⟨rfl,by omega⟩
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)) (by simp [mandatoryAt])
    omega
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)+1) (by simp [mandatoryAt])
    omega
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)+2) (by simp [mandatoryAt])
    omega

/-- **A publication of lane zero is preceded, in every data lane of the CTA that is still running
or has finished, by the same round's polls.** The lane's rendezvous at the ordinal of lane zero's
last mandatory rendezvous of the round is in the same round. -/
public theorem peer_polls {Q L m X x g i l tx cnt rel sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (safe : ¬Race L X)
    (arr : X.get (x,i)=some ⟨1013,.arrive l tx cnt rel sc⟩) (lx : x%L.block<128)
    (lg : g%L.block<128) (cta : g/L.block=x/L.block) :
    let n := ((X.tr x).take i).countP (fun e : Event => e.pc==1013)
    n+1≤pollRound 1257 (X.tr g) ∧ n≤pollRound 2239 (X.tr g) := by
  obtain ⟨u,c,hu,bar⟩ := arrive_source hp hX arr
  obtain ⟨pn,ps⟩ := arrival_polls hp hX hf arr
  have len : i<(X.tr x).length := (List.getElem?_eq_some_iff.mp arr).1
  subst hu
  have uni := rescale_agree hp hX hf safe bar (fun _ => nofun) rfl rfl lx
  obtain ⟨j,p,c',barG,ord⟩ := data_arrival hp hX (show X.IsBarrier (x,u) 0 c 1012 from bar) len
    lx lg cta (fun k p ex => exit_ordinal hp hX bar (fun _ => nofun) rfl rfl ex lx lg cta.symm)
  have barG' : X.get (g,j)=some ⟨p,.bar 0 c' .sync⟩ := barG
  obtain ⟨rfl,round⟩ := same_round hp hX hf uni lx lg cta len bar rfl barG' ord
  rw [←bar_keeps 1257 bar] at round
  rw [ps] at round
  have posG := bar_polls hp hX hf barG' (by simp)
  have lenG : j≤(X.tr g).length := (List.getElem?_eq_some_iff.mp barG').1.le
  have a := Flow.countP_take_mono (okPollAt 1257) (X.tr g) lenG
  have b := Flow.countP_take_mono (okPollAt 2239) (X.tr g) lenG
  rw [List.take_length] at a b
  change pollRound 1257 _≤pollRound 1257 (X.tr g) at a
  change pollRound 2239 _≤pollRound 2239 (X.tr g) at b
  dsimp only
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
