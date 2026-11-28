-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.DataStart
public import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
public import Kernels.InklingRelDecode.Proof.Common.WorkerIdle
public import Kernels.InklingRelDecode.Proof.Dispatch.Rounds
public import Kernels.InklingRelDecode.Proof.Lib.WorkerBarSchedule
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.GlueStep

@[expose] public section

/-! # The pc of a worker lane's rendezvous, by its ordinal

A worker thread runs the startup, then one or two dispatch rounds. Its rendezvous are
`Lib.workerBar`: the barrier-zero count of a worker state is two plus the final sync behind it,
and the barrier-one count is the publication phase, so their sum is the ordinal. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Proof

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private def inv : (thread Q L g).D → Prop
  | (.inl s,n) => LaunchCounts n (Startup.barriers s.site)
  | (.inr ⟨.inl (.dispatch _ _),.inl s⟩,n) =>
    Dispatch.Allowed s ∧ n (.bar 0) = 2 + Dispatch.finalDone s
  | (.inr ⟨.inl (.dispatch _ _),.inr ⟨.loader r,_⟩⟩,n) => r = 0 ∧ n (.bar 0) = 2
  | (.inr ⟨.inl (.dispatch _ _),.inr ⟨.mma r,_⟩⟩,n) => r = 0 ∧ n (.bar 0) = 2
  | (.inr ⟨.inr _,_⟩,_) => False
  | _ => True

private theorem dispatch_zero (s : Dispatch.Site) :
    Lib.zeroSite s.pc = decide (s.pc = 2853) := by
  cases s <;> decide +kernel

private theorem loader_zero (s : Loader.Site) : Lib.zeroSite s.pc = false := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_zero (s : Mma.Site) : Lib.zeroSite s.pc = false := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem bar_bump {k n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ev)
    (nu : ∀ f, ev.kind≠.ub f) :
    Code.bump cls n ev (.bar 0)=n (.bar 0)+(Lib.zeroSite ev.pc).toNat := by
  have kind := Lib.zero_event hX hp.block get nu
  change n _+(if cls (.bar 0) ev then 1 else 0)=_
  rw [cls_bar0,kind]
  cases Lib.zeroSite ev.pc <;> rfl

private theorem start_inv (s : Startup.D) (n : Cls → Nat)
    (h : LaunchCounts n (Startup.barriers s.site)) :
    inv (Q := Q) (L := L) (g := g) (Code.enter (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> try exact h
  rename_i r
  cases r with
  | dp => trivial
  | worker => exact ⟨Dispatch.allowed_init,h.first⟩

private theorem step_inv {k s sn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k=some (some s))
    (clean : ∀ f, ev.kind≠.ub f) (old : inv s) (hn : (thread Q L g).next s ev=some (some sn)) :
    inv sn := by
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨step,rfl⟩ := Code.counted_next_some hn
  rcases s with s|⟨r,d⟩
  · obtain ⟨_,go,rfl⟩ := Code.glue_inl_some step
    exact start_inv _ _ (launch_counts_step old (start_ev hp hX he hs clean) go)
  obtain ⟨next,sub,rfl⟩ := Code.glue_inr_some step
  rcases r with r|r
  · cases r with
    | prologue => trivial
    | dispatch w x =>
      rcases d with d|⟨i,d⟩
      · change (Dispatch.next L g d ev).map _ = _ at sub
        obtain ⟨_,move,h⟩ := Option.map_eq_some_iff.mp sub
        obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
        have ⟨low,_⟩ := worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
        change 128≤g%L.block at low
        have lt : g%L.block<256 := by rw [hp.block]; omega
        have al := Dispatch.allowed_next (by omega) (by omega)
          (fun _ _ read kind => dispatch_bytes hp hX words he hs read kind) old.1 move
        change ev.pc=d.site.pc at pc
        have hz : (Code.bump cls n ev) (.bar 0) = 2+Dispatch.finalDone sn := by
          rw [bar_bump hp hX he clean,pc,dispatch_zero,old.2,Dispatch.finalDone_next move]
          by_cases c : d.site.pc=2853
          · simp [c]; omega
          · simp [c]
        obtain ⟨st,rd⟩ := sn
        cases st <;> first
          | exact ⟨al,hz⟩
          | (rcases al with ⟨hr,hm⟩|⟨hr,hm⟩
             · exact ⟨hr,by simpa [Dispatch.finalDone] using hz⟩
             · simp [Dispatch.round1] at hm)
      · change ((workerFrag Q L g w x i).next d ev).map _ = _ at sub
        obtain ⟨_,_,h⟩ := Option.map_eq_some_iff.mp sub
        obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
        have hz : (Code.bump cls n ev) (.bar 0) = 2 := by
          rw [bar_bump hp hX he clean]
          cases i <;> (change ev.pc=d.site.pc at pc; rw [pc]) <;> [rw [loader_zero]; rw [mma_zero]]
          all_goals simp [old.2]
        cases i <;> obtain ⟨site,rest⟩ := sn <;> cases site <;> first
          | exact ⟨old.1,hz⟩
          | (obtain rfl := old.1
             exact ⟨Dispatch.allowed_back,by simpa [Dispatch.finalDone] using hz⟩)
  · cases sub

private theorem inv_reach {j s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (hj : j≤(X.tr g).length) (hs : stateAt (thread Q L) X g j=some (some s))
    (nu : NoUbBefore X g j) : inv s :=
  reference_induction (P := inv) (start_inv _ _ launch_counts_init)
    (fun he hs clean ih hn => step_inv hp hX words he hs clean ih hn) hj hs (prefix_ub_zero hs nu)

private theorem start_bar (s : Startup.Site)
    (h : s.pc ∈ Lib.barOneSites ∨ Lib.zeroSite s.pc = true) : s = .bar0 ∨ s = .bar1 := by
  cases s <;> first | (left; rfl) | (right; rfl) | (exfalso; revert h; decide) |
    (rename_i r; cases r <;> (exfalso; revert h; decide))

private theorem dispatch_pc (d : Dispatch.D) (w : Nat) (al : Dispatch.Allowed d)
    (idle : (d.site=.idleDec ∨ d.site=.idleSync ∨ d.site=.idleSyncAgain ∨ d.site=.idleInc) → w<6)
    (bar : d.site.pc ∈ Lib.barOneSites ∨ Lib.zeroSite d.site.pc = true) :
    d.site.pc = Lib.workerBar w (2+Dispatch.finalDone d+Dispatch.publicationPhase d) := by
  obtain ⟨st,r⟩ := d
  rcases al with ⟨hr,hm⟩|⟨hr,hm⟩ <;> simp only at hr <;> subst hr <;>
    simp [Dispatch.round0,Dispatch.round1] at hm <;>
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [Dispatch.finalDone,Dispatch.publicationPhase,Dispatch.publicationOffset,
      Lib.workerBar_fixed,Lib.workerBar_idle,Dispatch.Site.pc,Lib.barOneSites,Lib.zeroSite,
      BarRow.fullZeroSites,BarRow.halfZeroSites]

private theorem loader_pc (s : Loader.Site)
    (bar : s.pc ∈ Lib.barOneSites ∨ Lib.zeroSite s.pc = true) :
    s.pc = Lib.workerBar 6 (2+Loader.publicationPhase s) := by
  revert bar
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_pc (s : Mma.Site)
    (bar : s.pc ∈ Lib.barOneSites ∨ Lib.zeroSite s.pc = true) :
    s.pc = Lib.workerBar 7 (2+Mma.publicationPhase s) := by
  revert bar
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **A worker state at a rendezvous is at the pc the schedule gives its ordinal.** -/
theorem worker_bar_state {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (nu : NoUbBefore X g k)
    (lw : 128≤g%L.block)
    (bar : (thread Q L g).pc s ∈ Lib.barOneSites ∨ Lib.zeroSite ((thread Q L g).pc s)=true) :
    (thread Q L g).pc s=Lib.workerBar (g%L.block/32) (s.2 (.bar 0)+publication s) := by
  have iv := inv_reach hp hX words hk hs nu
  obtain ⟨s,n⟩ := s
  rcases s with st|⟨r,d⟩
  · change LaunchCounts n (Startup.barriers st.site) at iv
    change st.site.pc ∈ _ ∨ Lib.zeroSite st.site.pc=true at bar
    change st.site.pc=Lib.workerBar _ (n (.bar 0)+0)
    rw [iv.first]
    have fixed := Lib.workerBar_fixed (g%L.block/32)
    rcases start_bar st.site bar with h|h <;> rw [h] <;> simp [Startup.barriers,fixed] <;> rfl
  rcases r with r|r
  · cases r with
    | prologue w =>
      have := data_warp hp hX hk hs
      omega
    | dispatch w x =>
      rcases d with d|⟨i,d⟩
      · obtain ⟨idle,-,-⟩ := idle_warp hp hX words hk hs
        have h := dispatch_pc d (g%L.block/32) iv.1 (fun h => idle h) bar
        change d.site.pc=Lib.workerBar _ (n (.bar 0)+Dispatch.publicationPhase d)
        rw [iv.2]
        exact h
      · have called := worker_called hp hX words hk hs
        cases i with
        | loader r0 =>
          obtain ⟨hw,-⟩ := called
          rw [hw]
          change d.site.pc=Lib.workerBar 6 (n (.bar 0)+(3*r0+Loader.publicationPhase d.site))
          rw [iv.2,iv.1]
          simpa using loader_pc d.site bar
        | mma r0 =>
          obtain ⟨hw,-⟩ := called
          rw [hw]
          change d.site.pc=Lib.workerBar 7 (n (.bar 0)+(3*r0+Mma.publicationPhase d.site))
          rw [iv.2,iv.1]
          simpa using mma_pc d.site bar
  · exact iv.elim

private theorem start_final (s : Startup.Site) : Lib.finalSync s.pc = false := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem dispatch_final_site (s : Dispatch.Site) (h : Lib.finalSync s.pc = true) :
    s = .exitSync := by
  cases s <;> first | rfl | (exfalso; revert h; decide)

/-- **A worker state at the final rendezvous has made only the two startup rendezvous of
barrier 0.** -/
theorem worker_final_count {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (nu : NoUbBefore X g k)
    (lw : 128≤g%L.block) (h : Lib.finalSync ((thread Q L g).pc s) = true) :
    s.2 (.bar 0) = 2 := by
  have iv := inv_reach hp hX words hk hs nu
  obtain ⟨s,n⟩ := s
  rcases s with st|⟨r,d⟩
  · exact absurd h (by simp [show Lib.finalSync st.site.pc = false from start_final st.site])
  rcases r with r|r
  · cases r with
    | prologue w =>
      have := data_warp hp hX hk hs
      omega
    | dispatch w x =>
      rcases d with d|⟨i,d⟩
      · have e := dispatch_final_site d.site h
        change n (.bar 0) = 2
        rw [iv.2]
        simp [Dispatch.finalDone, e]
      · cases i with
        | loader r0 => exact iv.2
        | mma r0 => exact iv.2
  · exact iv.elim

/-- **The rounds a worker state is in**: a dispatch state is an allowed one, a role state is the
first round's. -/
theorem worker_rounds {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (hk : k≤(X.tr g).length)
    (hs : stateAt (thread Q L) X g k=some (some s)) (nu : NoUbBefore X g k) :
    (∀ w x d n, s = (.inr ⟨.inl (.dispatch w x), .inl d⟩, n) → Dispatch.Allowed d) ∧
    (∀ w x r d n, s = (.inr ⟨.inl (.dispatch w x), .inr ⟨.loader r, d⟩⟩, n) → r = 0) ∧
    (∀ w x r d n, s = (.inr ⟨.inl (.dispatch w x), .inr ⟨.mma r, d⟩⟩, n) → r = 0) := by
  have iv := inv_reach hp hX words hk hs nu
  refine ⟨fun w x d n h => ?_, fun w x r d n h => ?_, fun w x r d n h => ?_⟩ <;> subst h
  · exact iv.1
  · exact iv.1
  · exact iv.1

end

end PTX.Kernels.InklingRelDecode.Proof
