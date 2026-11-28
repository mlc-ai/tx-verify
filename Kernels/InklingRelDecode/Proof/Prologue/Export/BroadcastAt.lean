-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Where
public import Lemmas.Kernel.Safety.TableU
import Kernels.InklingRelDecode.Proof.Prologue.Sites
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
import Kernels.InklingRelDecode.Proof.Prologue.BarrierCount
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Kernels.InklingRelDecode.Flow.Code.Part003
import Lemmas.Flow.GlueStep
import Kernels.InklingRelDecode.Proof.Prologue.CopyFoot
import Kernels.InklingRelDecode.Proof.Prologue.ShapeCopy
public import Kernels.InklingRelDecode.Proof.Iface.PreloadBox
public import Kernels.InklingRelDecode.Proof.Lib.RawArith

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Frame PTX.Proof Control

/-- The block whose broadcast the site still uses. -/
private def holds : Site → Option (Fin 3)
  | .pel b _ | .ptc b _ | .pb b 2 | .pb b 3 | .pb b 4 | .lb b 1 => some b
  | _ => none

private theorem holds_query (tid : Nat) (d : D) (group : Nat) :
    holds (querySite tid d group) = none := by
  unfold querySite
  split_ifs <;> rfl

private theorem holds_init (i : Fin 12) : holds (afterInit i) = none := by
  unfold afterInit
  split <;> rfl

private theorem holds_copy (d : D) (tid n : Nat) (b : Fin 3) (j : Fin 4) {b'}
    (h : holds (afterCopy d tid n b j) = some b') : b' = b := by
  fin_cases j <;> simp only [afterCopy] at h
  all_goals try (first | (cases h; rfl))
  all_goals (split_ifs at h <;> first | (rw [holds_query] at h; cases h) | cases h)

private def payload (ev : Event) (old : Value) : Value :=
  match ev.kind with
  | .shfl _ _ _ _ recv _ => recv
  | _ => old

private theorem holds_after_query (tid : Nat) (d : D) (j : Fin 64) :
    holds (afterQuery d tid j) = none := by
  unfold afterQuery
  split_ifs <;> first | rfl | exact holds_query ..

private theorem holds_after_store (i : Fin 8) (j : Fin 4) :
    holds (Control.afterStore i j) = none := by
  unfold Control.afterStore
  split_ifs <;> rfl

set_option hygiene false in
local macro "hold_close" : tactic => `(tactic| (
  simp only [Control.next] at move
  try (repeat' split at move)
  all_goals try (cases move; done)
  all_goals try (obtain rfl := Option.some.inj (Option.some.inj move))
  all_goals dsimp only at h ⊢
  all_goals first
    | (obtain rfl := holds_copy _ _ _ _ _ h; exact .inl ⟨rfl,rfl⟩)
    | (simp only [holds] at h; contradiction)
    | (rw [holds_query] at h; cases h)
    | (rw [holds_init] at h; cases h)
    | (rw [holds_after_query] at h; cases h)
    | (rw [holds_after_store] at h; cases h)
    | (simp only [holds, Option.some.injEq] at h; subst h; exact .inl ⟨rfl,rfl⟩)))

/-- A step keeps the block and its broadcast, or is the broadcast itself. -/
private theorem hold_next {Q L g d dn ev} (move : Control.next Q L g d ev=some (some dn)) {b}
    (h : holds dn.site=some b) :
    (holds d.site=some b ∧ dn.broadcast=d.broadcast) ∨
      (d.site=.psh b ∧ dn.broadcast=payload ev d.broadcast) := by
  obtain ⟨s,f,l,q,e,bc⟩ := d
  cases s
  case pb b' j => fin_cases j <;> hold_close
  case lb b' j => fin_cases j <;> hold_close
  case psh b' =>
    simp only [Control.next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    dsimp only at h ⊢
    simp only [holds, Option.some.injEq] at h
    subst h
    exact .inr ⟨rfl,rfl⟩
  all_goals hold_close

private theorem psh_site (s : Site) (h : s.pc ∈ [202,244,286]) : ∃ b, s = .psh b := by
  revert h
  cases s <;> first | exact fun _ => ⟨_,rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

/-- **A prologue broadcast sends the warp index**: the event at a broadcast site is an index
shuffle of lane zero of the operand `warp`. -/
public theorem psh_shape {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ev) (clean : ∀ f, ev.kind≠.ub f) (site : ev.pc ∈ [202,244,286]) :
    ∃ recv ok, ev=⟨ev.pc,.shfl .idx (b32 (g%L.block/32)) 0 31 recv ok⟩ := by
  have hg := Frame.lt_of_get hX get
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
  have region : 27<ev.pc ∧ ev.pc<574 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,d,n,rfl⟩ := (pos ▸ state_role s).prologue region.1 region.2
  change ev.pc=d.site.pc at pos
  obtain ⟨b,hb⟩ := psh_site d.site (pos ▸ site)
  obtain ⟨t,ins,o,hat,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs
    clean
  change (code Q L g w).AtD d t at hat
  change kernel.code[d.site.pc]?=some ins at hc
  change Fires d.site.pc _ _ _ at fire
  have isShfl : Execution.isShfl ev=true := by
    rw [Lib.shfl_event hX get clean]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    rcases site with h|h|h <;> simp [h,Lib.shflPcs]
  obtain ⟨pc,kind⟩ := ev
  obtain ⟨mode,a,b',c,recv,ok,rfl⟩ : ∃ mode a b' c recv ok, kind=.shfl mode a b' c recv ok := by
    cases kind <;> simp [Execution.isShfl] at isShfl
    exact ⟨_,_,_,_,_,_,rfl⟩
  change pc=d.site.pc at pos
  subst pos
  obtain ⟨hpc,sub,acc,fault,regs⟩ := hat
  have reg := holds_mem regs (mem_factsFrom (val := valueOf Q L g w d)
    (by rw [hb]; fin_cases b <;> decide +kernel : 464 ∈ ctlLive d.site.pc))
  have word : valueOf Q L g w d 464=b32 (g%L.block/32) := rfl
  rw [word] at reg
  rw [hb] at hc fire
  fin_cases b
  all_goals first
    | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_202)
       obtain ⟨val,m,bv,cv⟩ := Lib.shfl_operand (n := 0) rfl rfl fire rfl
       rw [reg] at val
       cases Option.some.inj val
       cases m; cases bv; cases cv
       exact ⟨_,_,rfl⟩)
    | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_244)
       obtain ⟨val,m,bv,cv⟩ := Lib.shfl_operand (n := 0) rfl rfl fire rfl
       rw [reg] at val
       cases Option.some.inj val
       cases m; cases bv; cases cv
       exact ⟨_,_,rfl⟩)
    | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_286)
       obtain ⟨val,m,bv,cv⟩ := Lib.shfl_operand (n := 0) rfl rfl fire rfl
       rw [reg] at val
       cases Option.some.inj val
       cases m; cases bv; cases cv
       exact ⟨_,_,rfl⟩)

private def bcastInv (X : Execution) {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue _),.inl d⟩,_) => ∀ b, holds d.site=some b →
      ∃ a ok j, X.get (g,j)=some ⟨pshPc b,.shfl .idx a 0 31 d.broadcast ok⟩ ∧
        ((X.tr g).take j).countP Execution.isShfl=1+b.val
  | _ => True

private theorem start_at {Q L g n} (X : Execution) (s : Startup.D) :
    bcastInv (Q := Q) (L := L) (g := g) X
      (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,v,w⟩ := s
  cases s <;> try trivial
  rename_i r
  cases r with
  | dp => exact fun b hb => by simp [holds] at hb
  | worker => trivial

private theorem pro_at {Q L g w n} (X : Execution) (s : Control.D)
    (z : ∀ b, holds s.site=some b → ∃ a ok j, X.get (g,j)=some ⟨pshPc b,.shfl .idx a 0 31
      s.broadcast ok⟩ ∧ ((X.tr g).take j).countP Execution.isShfl=1+b.val) :
    bcastInv (Q := Q) (L := L) (g := g) X (.inr ⟨.inl (.prologue w),
      Code.enter (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
        (dataExit Q L g w) s⟩,n) := by
  obtain ⟨s,a,b,c,d,e⟩ := s
  cases s <;> first | exact z | trivial

private theorem bcast_at {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (proState w d n))) (nu : NoUbBefore X g k) :
    ∀ b, holds d.site=some b → ∃ a ok j, X.get (g,j)=some ⟨pshPc b,.shfl .idx a 0 31
      d.broadcast ok⟩ ∧ ((X.tr g).take j).countP Execution.isShfl=1+b.val := by
  have main : bcastInv X (proState (Q := Q) (L := L) (g := g) w d n) := by
    apply reference_induction (P := bcastInv X) (start_at X _) _ hk hs (prefix_ub_zero hs nu)
    rintro j ⟨old,n⟩ ev ⟨sn,nn⟩ get prev clean ih move
    have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
    obtain ⟨step,rfl⟩ := Code.counted_next_some move
    rcases old with s|⟨r,d⟩
    · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
      exact start_at X _
    obtain ⟨next,sub,rfl⟩ := Code.glue_inr_some step
    rcases r with r|r
    · cases r with
      | dispatch => trivial
      | prologue w =>
        rcases d with s|⟨ent,s|⟨_,s⟩⟩
        · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some sub
          apply pro_at
          intro b hb
          rcases hold_next go hb with ⟨old,same⟩|⟨site,pay⟩
          · obtain ⟨a,ok,i,get',cnt⟩ := ih b old
            exact ⟨a,ok,i,same ▸ get',cnt⟩
          · change ev.pc=s.site.pc at pc
            rw [site] at pc
            obtain ⟨recv,ok,hev⟩ := psh_shape hp hX get clean (by
              rw [pc]; fin_cases b <;> decide)
            have pcv : ev.pc=pshPc b := pc
            have e2 : ev=⟨pshPc b,.shfl .idx (b32 (g%L.block/32)) 0 31 recv ok⟩ := by
              rw [←pcv]; exact hev
            have bc : dn.broadcast=recv := by rw [pay, e2]; rfl
            refine ⟨b32 (g%L.block/32),ok,j,?_,?_⟩
            · rw [bc, ←e2]; exact get
            · have := shfl_prologue hp hX (List.getElem?_eq_some_iff.mp get).1.le prev
                (Frame.noUbBefore_of_get hX get)
              rw [site] at this
              have count : n .shfl=((X.tr g).take j).countP Execution.isShfl := fcount prev _
              rw [←count, this]
              rfl
        · obtain ⟨_,_,rfl⟩ := Code.glue_inr_some sub
          trivial
        · obtain ⟨_,_,rfl⟩ := Code.glue_inr_some sub
          trivial
    · cases sub
  exact main

/-- **A preload copy uses the broadcast of its block**: the word in the thread's state at a copy
site of block `b` is what the thread's `(1+b)`-th shuffle, the broadcast at `pshPc b`, received. -/
private theorem bcast_copy {Q L m X g k w d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some (proState w d n))) (nu : NoUbBefore X g k)
    (b : Fin 3) (j : Fin 4) (site : d.site=.ptc b j) :
    ∃ a ok i, X.get (g,i)=some ⟨pshPc b,.shfl .idx a 0 31 d.broadcast ok⟩ ∧
      ((X.tr g).take i).countP Execution.isShfl=1+b.val :=
  bcast_at hp hX hk hs nu b (by rw [site]; rfl)

private theorem copy_site (s : Site) (h : s.pc ∈ Iface.preloadSites) : ∃ b j, s=.ptc b j := by
  revert h
  cases s <;> first | exact fun _ => ⟨_,_,rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

/-- **A preload copy's box is fixed by its site and the broadcast it received**: the copy of the
site at `pc` writes only the 8192-byte box at the half tile selected by the low bit of the word
that its thread's index shuffle (one of the three broadcast sites) received. -/
public theorem preload_box {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩) (site : pc ∈ Iface.preloadSites) :
    ∃ p0 a ok i recv, p0 ∈ [202,244,286] ∧ X.get (g,i)=some ⟨p0,.shfl .idx a 0 31 recv ok⟩ ∧
      ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
        L.sharedBase+16384*((Lib.word recv).toNat%2)+Iface.preloadOff pc ≤ l.addr ∧
        l.addr<L.sharedBase+16384*((Lib.word recv).toNat%2)+Iface.preloadOff pc+8192 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc=_ at pos
  have region : 27<pc ∧ pc<574 := by
    simp only [Iface.preloadSites,List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,d,n,rfl⟩ := (pos ▸ state_role s).prologue region.1 region.2
  change pc=d.site.pc at pos
  obtain ⟨b,j,kind⟩ := copy_site d.site (pos ▸ site)
  obtain ⟨_,_,_,hat,_,fetch,step⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  obtain ⟨-,-,-,box,-⟩ := preload_footprint hp hat b j kind fetch step rfl
  obtain ⟨a,ok,i,get,_⟩ := bcast_copy hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
    (Frame.noUbBefore_of_get hX he) b j kind
  refine ⟨pshPc b,a,ok,i,d.broadcast,by fin_cases b <;> decide,get,fun byte => ?_⟩
  rw [pos]
  exact box byte

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
