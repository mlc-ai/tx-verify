-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerRefStep
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Proof

private theorem not_poll {p ev} (h : ev.pc≠p) : okPollAt p ev=false := by
  obtain ⟨pc,kind⟩ := ev
  cases kind <;> try rfl
  rename_i yes _ _
  cases yes <;> simp_all [okPollAt]

private theorem not_at {p : Nat} {ev : Event} (h : ev.pc≠p) : (ev.pc == p) = false := by
  simpa using h

theorem bump_no_polls {n ev} (old : noWorkerPolls n) (a : ev.pc≠2374) (b : ev.pc≠2462)
    (c : ev.pc≠2510) (d : ev.pc≠2550) (e : ev.pc≠2551) : noWorkerPolls (Code.bump cls n ev) := by
  simpa only [noWorkerPolls,Code.bump,cls,not_poll a,not_poll b,not_poll c,not_at d,not_at e,
    Bool.false_eq_true,↓reduceIte,Nat.add_zero] using old

private theorem keep_poll {n ev p} (h : ev.pc≠p) : Code.bump cls n ev (.poll p)=n (.poll p) := by
  simp only [Code.bump,cls,not_poll h,Bool.false_eq_true,↓reduceIte,Nat.add_zero]

private theorem keep_at {n ev p} (h : ev.pc≠p) : Code.bump cls n ev (.atPc p)=n (.atPc p) := by
  simp only [Code.bump,cls,not_at h,Bool.false_eq_true,↓reduceIte,Nat.add_zero]

private theorem on_entry {Q L g w x n} (d : Dispatch.D)
    (ref : DispatchRef (g%L.block/32) (Iface.preloadCount Q L (g/L.block))
      (iterCount Q L (g/L.block)) d n) (which : Dispatch.Called (g%L.block/32) d) :
    workerInv Q L g w x (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry d) n := by
  obtain ⟨s,r⟩ := d
  cases s <;> try exact ref
  · obtain ⟨warp,rr⟩ := which.1 rfl
    obtain ⟨p,_,_,_⟩ := ref.2.2.1 rr
    exact ⟨warp,Loader.ref_init ..,p,Loader.pageRef_init _,rr⟩
  · obtain ⟨warp,rr⟩ := which.2 rfl
    obtain ⟨_,p,q,f⟩ := ref.2.2.1 rr
    exact ⟨warp,Mma.initial_ref _,p,q,f,rr⟩

private theorem back_ref {Q L g w x n} {r : Nat} (hr : r = 0)
    (late : (g%L.block/32 = 6 → n (.poll 2374) = iterCount Q L (g/L.block) -
      Iface.preloadCount Q L (g/L.block)) ∧ (g%L.block/32 = 7 →
      n (.poll 2462) = Mma.runCount (iterCount Q L (g/L.block)) ∧
      n (.poll 2510) = Mma.runCount (iterCount Q L (g/L.block)) ∧
      n (.atPc 2550) + n (.atPc 2551) = 2)) :
    workerInv Q L g w x (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry ⟨.head,r+1⟩) n := by
  subst hr
  exact on_entry _ ⟨Dispatch.allowed_back,fun _ h => absurd h (by simp),
    fun h => absurd h (by simp),fun _ => late⟩ ⟨nofun,nofun⟩

private theorem on_return {Q L g w x n i} (s : (workerFrag Q L g w x i).D)
    (ok : workerInv Q L g w x (.inr ⟨i,s⟩) n) :
    workerInv Q L g w x (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) i s) n := by
  cases i with
  | loader r =>
    unfold Code.backEnter workerBack
    by_cases hs : s.site=.dispatch
    · simp only [hs,↓reduceIte]
      obtain ⟨warp,_,polls,_,r0⟩ := ok
      refine back_ref r0 ⟨fun _ => ?_,fun w7 => by omega⟩
      simp only [polls,Loader.polls,hs]
    · simpa only [hs,↓reduceIte] using ok
  | mma r =>
    unfold Code.backEnter workerBack
    by_cases hs : s.site=.dispatch
    · simp only [hs,↓reduceIte]
      obtain ⟨warp,ref,first,second,fin,r0⟩ := ok
      have lim := Mma.ref_count ref (by simp [hs,Mma.Site.hasCount])
      refine back_ref r0 ⟨fun w6 => by omega,fun _ => ⟨?_,?_,?_⟩⟩
      · simp only [first,Mma.polls,hs,lim]
      · simp only [second,Mma.polls,hs,lim]
      · simpa only [hs,Mma.Site.fin] using fin
    · simpa only [hs,↓reduceIte] using ok

theorem ref_worker_next {Q L m X g k w x d n ev dn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (pair : CountBytes Q L X) (he : X.get (g,k)=some ev) (hu : ∀ f, ev.kind≠.ub f)
    (hs : stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.dispatch w x),d⟩,n)))
    (old : workerInv Q L g w x d n) (move : (workerCode Q L g w x).next d ev=some (some dn)) :
    workerInv Q L g w x dn (Code.bump cls n ev) := by
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  rcases d with d|⟨i,s⟩
  · change (Dispatch.next L g d ev).map _ = _ at move
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp move
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    change ev.pc=d.site.pc at pc
    obtain ⟨al,bz,start,late⟩ := old
    obtain ⟨al',bz'⟩ := dispatch_ref hp hX words he hs al bz step
    have clear : ∀ s : Dispatch.Site, s.pc≠2374 ∧ s.pc≠2462 ∧ s.pc≠2510 ∧ s.pc≠2550 ∧
        s.pc≠2551 := by
      intro s; cases s <;> decide
    obtain ⟨a,b,c,e,f⟩ := clear d.site
    refine on_entry _ ⟨al',bz',fun z => ?_,fun nz => ?_⟩ (dispatch_called hp hX words he hs step)
    · have le := Dispatch.round_mono step
      exact bump_no_polls (start (by omega)) (pc ▸ a) (pc ▸ b) (pc ▸ c) (pc ▸ e) (pc ▸ f)
    · have keep : d.round ≠ 0 ∨ ¬(g%L.block/32 = 6 ∨ g%L.block/32 = 7) := by
        by_cases w : g%L.block/32 = 6 ∨ g%L.block/32 = 7
        · left
          intro z
          exact nz (Dispatch.busy_round bz w z step)
        · right; exact w
      rcases keep with k | k
      · obtain ⟨l6,l7⟩ := late k
        refine ⟨fun w => ?_,fun w => ?_⟩
        · rw [keep_poll (pc ▸ a)]; exact l6 w
        · obtain ⟨p,q,f'⟩ := l7 w
          rw [keep_poll (pc ▸ b),keep_poll (pc ▸ c),keep_at (pc ▸ e),keep_at (pc ▸ f)]
          exact ⟨p,q,f'⟩
      · exact ⟨fun w => absurd (Or.inl w) k,fun w => absurd (Or.inr w) k⟩
  · change ((workerFrag Q L g w x i).next s ev).map _ = _ at move
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp move
    obtain ⟨sn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
    exact on_return _ (worker_ref_step hp hX pair he hu hs old step)

end PTX.Kernels.InklingRelDecode.Proof
