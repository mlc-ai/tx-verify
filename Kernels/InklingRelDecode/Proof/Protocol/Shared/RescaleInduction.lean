-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleAgree
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC
public import Kernels.InklingRelDecode.Proof.Iface.BarRows.Base
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadOrdinal
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

/-- The data lanes of one CTA have the same optional rendezvous at every barrier ordinal
below `n`. -/
def Uniform (L : Launch) (X : Execution) (c n : Nat) : Prop :=
  ∀ a b, a/L.block=c → a%L.block<128 → b/L.block=c → b%L.block<128 → ∀ n' < n,
    ordEv X (Execution.isBarId 0) rescaleBar a n'=ordEv X (Execution.isBarId 0) rescaleBar b n'

private theorem ordEv_bar {X : Execution} {g i pc c} {md : BarMode}
    (get : X.get (g,i)=some ⟨pc,.bar 0 c md⟩) :
    ordEv X (Execution.isBarId 0) rescaleBar g (barOrdinal X g i)=(pc==2326) := by
  rw [show barOrdinal X g i=((X.tr g).take i).countP (Execution.isBarId 0) from rfl,
    ordEv_eq get (by simp [Execution.isBarId])]
  simp [rescaleBar,Execution.isBarId]

private theorem soft_or_pro : ∀ q ∈ BarRow.halfZeroSites,
    (180≤q ∧ q<574) ∨ q∈[999,1012,2241,2251,2326] := by decide

/-- A data lane at the same barrier ordinal as a lane at the optional rendezvous is at it too. -/
theorem rescale_follow_by {Q L m X x y ix iy n cx cy pcY} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : ∀ m<n, StoreAgree L X m) (uni : Uniform L X (x/L.block) n)
    (lx : x%L.block<128) (ly : y%L.block<128)
    (cta : y/L.block=x/L.block)
    (bx : X.get (x,ix)=some ⟨2326,.bar 0 cx .sync⟩) (ordx : barOrdinal X x ix=n)
    (byy : X.get (y,iy)=some ⟨pcY,.bar 0 cy .sync⟩) (half : pcY∈BarRow.halfZeroSites)
    (ordy : barOrdinal X y iy=n) : pcY=2326 := by
  obtain ⟨kx,a,b',c',recv,ok,hk,gx,skipF,cnt⟩ := rescale_source hp hX bx
  obtain ⟨j,u,ac,bs,rfl,rd,hu,sync,o1,o2⟩ := decision_sync hp hX gx
  have earlierX : ∀ h, h/L.block=x/L.block → h%L.block<128 → ∀ n' < barOrdinal X x ix,
      ordEv X (Execution.isBarId 0) rescaleBar h n'=ordEv X (Execution.isBarId 0) rescaleBar x n' :=
    fun h ch lh n' lt => uni h x ch lh rfl lx n' (by omega)
  have visits := visits_equal hp hX bx byy cta ly (by omega) earlierX
  have lo : 574<2326 := by decide
  have hi : 2326<2331 := by decide
  have px := physical_bar hp hX bx (by simp) lo hi
  have mx := rescale_mandatory hp hX bx rfl (by simp)
  have rx : mandatory ((X.tr x).take ix)+2=4*(pollRound 1257 ((X.tr x).take ix)-1)+2 :=
    round_barriers hp hX hf bx (fun _ => nofun) lo hi (by simp [mandatoryAt])
  change barOrdinal X x ix=_ at px
  simp only [barOrdinal] at *
  rcases soft_or_pro pcY half with pro|soft
  · have bound := Prologue.Export.preload_ordinal_bound hp hX (show X.IsBarrier (y,iy) 0 cy pcY
      from byy) pro.1 pro.2
    rw [cta] at bound
    simp only [entryOrdinal] at px
    omega
  have range : 574<pcY ∧ pcY<2331 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
    omega
  have py := physical_bar hp hX byy (by simp) range.1 range.2
  change barOrdinal X y iy=_ at py
  rw [cta] at py
  simp only [barOrdinal] at py
  have ry (t : Nat) (site : mandatoryAt pcY (pollRound 1257 ((X.tr y).take iy))=some t) :
      mandatory ((X.tr y).take iy)+2=t :=
    round_barriers hp hX hf byy (fun _ => nofun) range.1 range.2 site
  simp only [List.mem_cons,List.not_mem_nil,or_false] at soft
  rcases soft with rfl|rfl|rfl|rfl|rfl
  · have Meq : mandatory ((X.tr y).take iy)=mandatory ((X.tr x).take ix) := by
      simp only [entryOrdinal] at px py
      omega
    exfalso
    rcases bar20_source hp hX byy with ⟨ky,a2,b2,c2,r2,ok2,hky,gy,skipT,cnty⟩|
      ⟨u2,e,hu2,gu,isbar,pce,cnt2,-⟩|zero
    · have agree := decision_agree_by hp hX hf
        (fun m lt => agree m (by simp only [barOrdinal] at lt; omega)) gx gy lx ly cta
        (by simp only [barOrdinal]; omega)
        (fun h ch lh n' lt => uni h x ch lh rfl lx n' (by simp only [barOrdinal] at lt; omega))
        (fun h ch lh n' lt => uni h y (ch.trans cta) lh cta ly n' (by
          simp only [barOrdinal] at lt; omega))
      rw [skipF,skipT] at agree
      exact Bool.noConfusion agree
    · have a1 := ordEv_eq gu isbar (q := rescaleBar)
      have a2 : rescaleBar e=true := by simp [rescaleBar,isbar,pce]
      have b1 := ordEv_bar sync
      have key := uni y x cta ly rfl lx (barOrdinal X x u) (by simp only [barOrdinal]; omega)
      rw [a2] at a1
      rw [b1] at key
      have : ((X.tr y).take u2).countP (Execution.isBarId 0)=barOrdinal X x u := by
        simp only [barOrdinal]
        omega
      rw [this] at a1
      rw [a1] at key
      simp at key
    · omega
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)+3) (by simp [mandatoryAt])
    simp only [entryOrdinal] at px py
    omega
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)) (by simp [mandatoryAt])
    simp only [entryOrdinal] at px py
    omega
  · have := ry (4*(pollRound 1257 ((X.tr y).take iy)-1)+1) (by simp [mandatoryAt])
    simp only [entryOrdinal] at px py
    omega
  · rfl

private theorem full_not_rescale : ∀ q ∈ BarRow.fullZeroSites, q≠2326 := by decide

/-- A barrier-zero arrival at one ordinal is full for every data lane, or counted for every
data lane, once one of them has passed it. -/
theorem same_kind {Q L m X g h i j pa pb ca cb} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (one : X.IsBarrier (h,j) 0 cb pb) (last : X.IsBarrier (g,i) 0 ca pa)
    (passed : i+1<(X.tr g).length) (lg : g%L.block<128) (lh : h%L.block<128)
    (cta : h/L.block=g/L.block) (ord : barOrdinal X h j=barOrdinal X g i) :
    (cb=none ∧ ca=none ∧ pb∈BarRow.fullZeroSites ∧ pa∈BarRow.fullZeroSites) ∨
    (pb∈BarRow.halfZeroSites ∧ pa∈BarRow.halfZeroSites) := by
  obtain ⟨_,one'|f1|h1⟩ := Lib.recorded_bar hX hp.block one
  · cases one'.1
  all_goals obtain ⟨_,one''|f2|h2⟩ := Lib.recorded_bar hX hp.block last
  all_goals try cases one''.1
  · exact .inl ⟨f1.2.1,f2.2.1,f1.2.2,f2.2.2⟩
  · have cn : ca=some 128 := by simpa [BarRow.recCnt,hp.block] using h2.2.1
    subst cn
    have clash := peer_target hp hX one last passed lh lg cta ord
      (show CtaBarrier.target L.block cb=.ok 8 by rw [f1.2.1,hp.block]; rfl)
      (show CtaBarrier.target L.block (some 128)=.ok 4 by rw [hp.block]; rfl)
    contradiction
  · have cn : cb=some 128 := by simpa [BarRow.recCnt,hp.block] using h1.2.1
    subst cn
    have clash := peer_target hp hX one last passed lh lg cta ord
      (show CtaBarrier.target L.block (some 128)=.ok 4 by rw [hp.block]; rfl)
      (show CtaBarrier.target L.block ca=.ok 8 by rw [f2.2.1,hp.block]; rfl)
    contradiction
  · exact .inr ⟨h1.2.2,h2.2.2⟩

/-- **The data lanes of a CTA agree on every optional rendezvous before a scratch read.** The
induction is over barrier-zero ordinals: the decisions of one round are the same function of
the four published words, the published words are the same by race freedom, and the decision
fixes whether the next ordinal is the optional one. -/
theorem rescale_agree_by {Q L m X g j e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : ∀ m<barOrdinal X g j, StoreAgree L X m) (get : X.get (g,j)=some e)
    (nu : ∀ f, e.kind≠.ub f) (early : Lib.afterFinal e.pc=0)
    (other : Lib.finalSync e.pc=false) (lg : g%L.block<128) :
    Uniform L X (g/L.block) (barOrdinal X g j) := by
  suffices ∀ N, N ≤ barOrdinal X g j → Uniform L X (g/L.block) N from this _ le_rfl
  intro N
  induction N with
  | zero =>
    intro _ x y _ _ _ _ n' lt
    omega
  | succ N ih =>
    intro hN
    have uni := ih (by omega)
    have key : ∀ h, h/L.block=g/L.block → h%L.block<128 →
        ordEv X (Execution.isBarId 0) rescaleBar h N=
          ordEv X (Execution.isBarId 0) rescaleBar g N := by
      intro h ch lh
      obtain ⟨iA,pA,cA,mdA,ilt,eA,ordA⟩ := Frame.nth_bar (X:=X) (g:=g) (f:=j) (q:=N) (id:=0) hN
      obtain ⟨rfl,-⟩ := Lib.recorded_bar hX hp.block eA
      have len : j<(X.tr g).length := (List.getElem?_eq_some_iff.mp get).1
      have passed : iA+1<(X.tr g).length := by omega
      have hN' : N+1≤((X.tr g).take j).countP (Execution.isBarId 0) := hN
      have ordA'' : ((X.tr g).take iA).countP (Execution.isBarId 0)=N := ordA
      obtain ⟨iH,pH,cH,barH,ordH⟩ := data_arrival hp hX (show X.IsBarrier (g,iA) 0 cA pA from eA)
        passed lg lh ch (fun k p ex => by
          have := exit_ordinal hp hX get nu early other ex lg lh ch.symm
          simp only [barOrdinal] at this ⊢
          omega)
      have eH : X.get (h,iH)=some ⟨pH,.bar 0 cH .sync⟩ := barH
      have fA := ordEv_bar eA
      have fH := ordEv_bar eH
      have ordA' : barOrdinal X g iA=N := ordA
      rw [ordA'] at fA
      rw [ordH,ordA'] at fH
      rw [fH,fA]
      rcases same_kind hp hX barH (show X.IsBarrier (g,iA) 0 cA pA from eA) passed lg lh ch ordH
        with ⟨-,-,fh,fa⟩|⟨hh,ha⟩
      · simp [full_not_rescale _ fh,full_not_rescale _ fa]
      · have uniH : Uniform L X (h/L.block) N := by rw [ch]; exact uni
        by_cases a2326 : pA=2326
        · subst a2326
          have := rescale_follow_by hp hX hf (fun m lt => agree m (by omega)) uni lg lh ch eA
            ordA' eH hh (ordH.trans ordA')
          rw [this]
        · by_cases h2326 : pH=2326
          · subst h2326
            have := rescale_follow_by hp hX hf (fun m lt => agree m (by omega)) uniH lh lg
              ch.symm eH (ordH.trans ordA') eA ha ordA'
            exact absurd this a2326
          · simp [a2326,h2326]
    intro x y hx lx hy ly n' lt
    by_cases below : n'<N
    · exact uni x y hx lx hy ly n' below
    · have : n'=N := by omega
      subst this
      rw [key x (hx.trans rfl) lx,key y hy ly]

theorem decision_agree {Q L m X x y kx ky ax bx cx rx okx ay by' cy ry oky}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (safe : ¬Race L X)
    (gx : X.get (x,kx)=some ⟨2255,.shfl .bfly ax bx cx rx okx⟩)
    (gy : X.get (y,ky)=some ⟨2255,.shfl .bfly ay by' cy ry oky⟩)
    (lx : x%L.block<128) (ly : y%L.block<128) (cta : y/L.block=x/L.block)
    (ord : barOrdinal X y ky=barOrdinal X x kx)
    (earlierX : ∀ h, h/L.block=x/L.block → h%L.block<128 → ∀ n<barOrdinal X x kx - 1,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar x n)
    (earlierY : ∀ h, h/L.block=y/L.block → h%L.block<128 → ∀ n<barOrdinal X y ky - 1,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar y n) :
    Lib.rescaleSkip L ax rx=Lib.rescaleSkip L ay ry :=
  decision_agree_by hp hX hf (fun _ _ => StoreAgree.of_safe hX safe) gx gy lx ly cta ord
    earlierX earlierY

theorem rescale_follow {Q L m X x y ix iy n cx cy pcY} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (safe : ¬Race L X)
    (uni : Uniform L X (x/L.block) n) (lx : x%L.block<128) (ly : y%L.block<128)
    (cta : y/L.block=x/L.block)
    (bx : X.get (x,ix)=some ⟨2326,.bar 0 cx .sync⟩) (ordx : barOrdinal X x ix=n)
    (byy : X.get (y,iy)=some ⟨pcY,.bar 0 cy .sync⟩) (half : pcY∈BarRow.halfZeroSites)
    (ordy : barOrdinal X y iy=n) : pcY=2326 :=
  rescale_follow_by hp hX hf (fun _ _ => StoreAgree.of_safe hX safe) uni lx ly cta bx ordx byy
    half ordy

theorem rescale_agree {Q L m X g j e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (safe : ¬Race L X)
    (get : X.get (g,j)=some e) (nu : ∀ f, e.kind≠.ub f) (early : Lib.afterFinal e.pc=0)
    (other : Lib.finalSync e.pc=false) (lg : g%L.block<128) :
    Uniform L X (g/L.block) (barOrdinal X g j) :=
  rescale_agree_by hp hX hf (fun _ _ => StoreAgree.of_safe hX safe) get nu early other lg

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
