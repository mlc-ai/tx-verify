-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
public import Kernels.InklingRelDecode.Proof.Protocol.KV.PollCount
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Lemmas.Protocol.SingleTmaRing.Order
import Kernels.InklingRelDecode.Proof.Protocol.KV.CommitBudget
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Mma.Export.EmptyCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Lib.KvCover
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Flow.NthEv
import Lemmas.Protocol.NotifyBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow AsyncCopy

/-- **No commit to one slot's empty barrier lies between an MMA that reads the slot and the next
commit** when the MMA's PV ordinal is within two of the commit's. -/
private theorem commits_stable {Q L m X g jc kR sp c} {σ : Fin 3} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (get : X.get (g,jc) = some ⟨2546,.tc (.commit sp)⟩) (hmb : sp.mbar = KV.Ring.empty.obj L c σ)
    (lt : kR < jc)
    (ord : pollRound 2510 ((X.tr g).take jc) ≤ pollRound 2510 ((X.tr g).take kR)+2) :
    ((X.tr g).take kR).countP (commitsTo (KV.Ring.empty.obj L c σ)) =
      ((X.tr g).take jc).countP (commitsTo (KV.Ring.empty.obj L c σ)) := by
  have warp := Mma.Export.commit_warp hp hX hf get
  obtain ⟨-,-,slot⟩ := KV.slot_of_commit hp hX hf get hmb
  have mono := countP_take_mono (commitsTo (KV.Ring.empty.obj L c σ)) (X.tr g) lt.le
  by_contra ne
  obtain ⟨c',lt',x,hx,hc,cnt⟩ := exists_nth (commitsTo (KV.Ring.empty.obj L c σ)) (X.tr g)
    (show ((X.tr g).take kR).countP (commitsTo (KV.Ring.empty.obj L c σ)) <
      ((X.tr g).take jc).countP (commitsTo (KV.Ring.empty.obj L c σ)) by omega)
  have after : kR ≤ c' := by
    by_contra before
    have step := countP_take_mono (commitsTo (KV.Ring.empty.obj L c σ)) (X.tr g)
      (show c'+1 ≤ kR by omega)
    rw [show ((X.tr g).take (c'+1)).countP _ = _ from countP_take_succ (X := X) hx hc] at step
    omega
  obtain ⟨sp',kind,hm'⟩ := MbarRing.Notify.commit_of_commitsTo hc
  obtain ⟨pc,kd⟩ := x
  change kd = _ at kind
  subst kind
  have get' : X.get (g,c') = some ⟨pc,.tc (.commit sp')⟩ := hx
  obtain ⟨rfl,-,slot'⟩ := KV.slot_of_commit hp hX hf get' hm'
  have le : pollRound 2510 ((X.tr g).take c') ≤ pollRound 2510 ((X.tr g).take jc) :=
    countP_take_mono (okPollAt 2510) (X.tr g) lt'.le
  have ge : pollRound 2510 ((X.tr g).take kR) ≤ pollRound 2510 ((X.tr g).take c') :=
    countP_take_mono (okPollAt 2510) (X.tr g) after
  have distinct : pollRound 2510 ((X.tr g).take c') ≠ pollRound 2510 ((X.tr g).take jc) := by
    intro same
    exact absurd (Mma.Export.empty_unique hp hX hf words warp get' get same) (by omega)
  have := σ.isLt
  have pos := (Mma.Export.empty_poll_bounds hp hX hf warp get').1
  omega

/-- **The MMA lane's reads of a released use cover its slot**: the premise `hcover` of
`SingleTmaRing.copies_chain` for slot `σ` of CTA `c`, at byte `l`. -/
theorem hcover {Q L m X c} {σ : Fin 3} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (rows : MbarRows Q L X) (hu : NoUbOutside L X) {l : Loc} (hsp : l.space = .shared)
    (hlc : l.cta = c) (hl : Iface.InSlot L σ.val l.addr) (u : Nat) :
    ∀ jc pc sp, X.get (((KV.decl Q L X c).slot σ).cm,jc) = some ⟨pc,.tc (.commit sp)⟩ →
      sp.mbar = ((KV.decl Q L X c).slot σ).empty →
      ((X.tr ((KV.decl Q L X c).slot σ).cm).take jc).countP
        (commitsTo ((KV.decl Q L X c).slot σ).empty) = u →
      ∃ kR isB idx, X.TcAsync (((KV.decl Q L X c).slot σ).cm,kR) ∧
        SingleTmaRing.readUse X ((KV.decl Q L X c).slot σ) (((KV.decl Q L X c).slot σ).cm,kR) = u ∧
        u+1 ≤ okPolls ((KV.decl Q L X c).slot σ).full
          ((X.tr ((KV.decl Q L X c).slot σ).cm).take kR) ∧
        AsyncCovers X (((KV.decl Q L X c).slot σ).cm,kR) (.mmaRead isB idx) l ∧
        ∀ w ws, AsyncObserved X (((KV.decl Q L X c).slot σ).cm,kR) .mmaDone w true ws →
          X.AsyncPresent (((KV.decl Q L X c).slot σ).cm,kR) (.mmaRead isB idx) := by
  intro jc pc sp get hmb hcnt
  change X.get (KV.leader L X c 7,jc) = _ at get
  change sp.mbar = KV.Ring.empty.obj L c σ at hmb
  change ((X.tr (KV.leader L X c 7)).take jc).countP (commitsTo (KV.Ring.empty.obj L c σ)) = u
    at hcnt
  obtain ⟨hpc,hcta,hslot⟩ := KV.slot_of_commit hp hX hf get hmb
  subst hpc
  have warp := Mma.Export.commit_warp hp hX hf get
  have hg := Frame.lt_of_get hX get
  have key := Mma.Export.commit_covers hp hX hf words hu get
  obtain ⟨base,a,hb,ha,hsum⟩ : ∃ base a, (base = L.sharedBase+32768*σ.val ∨
      base = L.sharedBase+98304+32768*σ.val) ∧ a<32768 ∧ base+a = l.addr := by
    unfold Iface.InSlot at hl
    rcases hl with ⟨lo,hi⟩|⟨lo,hi⟩
    · exact ⟨_,l.addr-(L.sharedBase+32768*σ.val),.inl rfl,by omega,by omega⟩
    · exact ⟨_,l.addr-(L.sharedBase+98304+32768*σ.val),.inr rfl,by omega,by omega⟩
  obtain ⟨kR,lt,pc',dst,s,acc,mask,idx,get',hbl,ord⟩ := key base (by
    rw [hslot]; exact hb) a ha
  have hloc : (⟨.shared,KV.leader L X c 7/L.block,base+a⟩ : Loc) = l := by
    rcases l with ⟨s1,c1,a1⟩
    simp only at hsp hlc hsum ⊢
    simp only [Loc.mk.injEq]
    exact ⟨hsp.symm,hcta.trans hlc.symm,hsum⟩
  rw [hloc] at hbl
  have stable := commits_stable hp hX hf words get hmb lt ord
  obtain ⟨-,-,σ',hbyte,T,n,le,ltn,slotn,bound⟩ := Mma.Export.read_slot hp hX hf words get'
  obtain ⟨-,hs'⟩ := hbyte idx l hbl
  obtain rfl : σ' = σ := Fin.ext (Iface.inSlot_unique σ'.isLt σ.isLt hs' hl)
  have credit := KV.read_credit hp hX hf words rows hg warp hcta bound le ltn slotn
  have hMI : X.MmaIssue (KV.leader L X c 7,kR) dst s acc mask := ⟨pc',get'⟩
  have hbl' : s.byteLoc (if true then .b else .a) idx = some l := by simpa using hbl
  refine ⟨kR,true,idx,.inl ⟨dst,s,acc,mask,pc',get'⟩,?_,?_,Lib.covers_of_byteLoc hMI hbl',
    fun w ws hob => observed_mmaRead hX hMI hbl' hob⟩
  · exact stable.trans hcnt
  · rw [← hcnt,← stable]
    exact credit

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
