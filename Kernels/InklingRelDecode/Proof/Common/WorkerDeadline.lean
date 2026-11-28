-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.PreElect
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Mma.Time
import all Kernels.InklingRelDecode.Proof.Common.Time
import all Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.GlueStep
import Kernels.InklingRelDecode.Proof.Common.Deadline

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Sched

/-- A worker awaiting its issue is in the first dispatch or in its producer role. -/
private def pendingWorker (ld : Loader.D → Prop) (ma : Mma.D → Prop) {Q L g w x} :
    (workerCode Q L g w x).D → Prop
  | .inl d => dispatchBefore d
  | .inr ⟨.loader _,d⟩ => ld d
  | .inr ⟨.mma _,d⟩ => ma d

private def pendingIssue (ld : Loader.D → Prop) (ma : Mma.D → Prop) {Q L g} :
    (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),d⟩,_) => pendingWorker ld ma d
  | _ => True

private theorem entered {ld ma Q L g} (s : Startup.D) (n : Cls → Nat) :
    pendingIssue ld ma (Code.enter (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> try trivial
  rename_i r
  cases r <;> first | trivial | exact ⟨rfl,.inl rfl⟩

private theorem first {Q L m X g k w x d n e dn ld ma} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X)
    (workers : g%L.block/32=6 ∨ g%L.block/32=7)
    (startL : g%L.block/32=6 → ld {}) (startM : g%L.block/32=7 → ma {})
    (he : X.get (g,k)=some e) (hs : stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) (early : dispatchBefore d)
    (step : Dispatch.next L g d e=some (some dn)) :
    pendingWorker ld ma (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry dn) := by
  obtain ⟨s,r⟩ := d
  obtain ⟨rfl,h|h|h⟩ := early
  · cases h; cases step; exact ⟨rfl,.inr (.inl rfl)⟩
  · cases h; cases step; exact ⟨rfl,.inr (.inr rfl)⟩
  · cases h
    simp only [Dispatch.next] at step
    split at step <;> try contradiction
    rename_i a bs kind
    have bytes := dispatch_bytes hp hX words he hs rfl kind
    rcases workers with warp|warp <;> rw [warp] at bytes
    · rw [show Dispatch.readTarget bs=some .loaderEntry from bytes ▸
        Dispatch.role_target (2 : Fin 4) true] at step
      cases step; exact startL warp
    · rw [show Dispatch.readTarget bs=some .mmaEntry from bytes ▸
        Dispatch.role_target (3 : Fin 4) true] at step
      cases step; exact startM warp

/-- A role proves preservation only on its own transitions. The final-state argument
covers startup, dispatch, the live end of the trace and an observed exit. -/
theorem worker_deadline {Q L m X g bound} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (words : RoleBytes L X) (hu : NoUbLane X g)
    (hg : g<L.threads) (workers : g%L.block/32=6 ∨ g%L.block/32=7) (large : 284<bound)
    (ld : Loader.D → Prop) (ma : Mma.D → Prop)
    (startL : g%L.block/32=6 → ld {}) (startM : g%L.block/32=7 → ma {})
    (clockL : ∀ d, ld d → Loader.time d≤bound) (clockM : ∀ d, ma d → Mma.time d≤bound)
    (seenL : ∀ {w x r d n k e}, X.get (g,k)=some e →
      stateAt (thread Q L) X g k=some (some (workerState w x (.loader r) d n)) →
      ld d → Loader.time d≠bound)
    (seenM : ∀ {w x r d n k e}, X.get (g,k)=some e →
      stateAt (thread Q L) X g k=some (some (workerState w x (.mma r) d n)) →
      ma d → Mma.time d≠bound)
    (stepL : ∀ {w x r d n k e dn}, X.get (g,k)=some e →
      stateAt (thread Q L) X g k=some (some (workerState w x (.loader r) d n)) →
      (∀ f, e.kind≠.ub f) → ld d → Loader.next L g d e=some (some dn) →
      ld dn ∧ dn.site≠.dispatch)
    (stepM : ∀ {w x r d n k e dn}, X.get (g,k)=some e →
      stateAt (thread Q L) X g k=some (some (workerState w x (.mma r) d n)) →
      (∀ f, e.kind≠.ub f) → ma d → Mma.next L g d e=some (some dn) →
      ma dn ∧ dn.site≠.dispatch) :
    threadTime (schedule Q L) X g≤bound ∧ ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  have clean (j : Nat) : NoUbBefore X g j := hu.before j
  have atState {k st} (hk : k≤(X.tr g).length) (hs : stateAt (thread Q L) X g k=some (some st)) :
      (schedule Q L).time g st≤bound ∧ (thread Q L g).pc st≠2855 ∧
        (k<(X.tr g).length → (schedule Q L).time g st<bound) := by
    have inv : pendingIssue ld ma st := by
      apply reference_induction (pendingIssue ld ma) _ _ hk hs (prefix_ub_zero hs (clean k))
      · apply entered
      · rintro j ⟨s,n⟩ e ⟨sn,nn⟩ he prev nu old move
        obtain ⟨sub,_⟩ := Code.counted_next_some move
        rcases s with s|⟨r,s⟩
        · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub; apply entered
        · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
          rcases r with (r|r)
          · cases r with
            | prologue => trivial
            | dispatch w x =>
              rcases s with d|⟨i,d⟩
              · obtain ⟨_,go,h⟩ := Option.map_eq_some_iff.mp step
                obtain ⟨dn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
                exact first hp hX words workers startL startM he prev old go
              · cases i <;> obtain ⟨_,go,h⟩ := Option.map_eq_some_iff.mp step
                all_goals obtain ⟨dn,rfl,rfl⟩ := Option.map_eq_some_iff.mp h
                case loader => obtain ⟨next,stay⟩ := stepL he prev nu old go
                               simp only [Code.backEnter,workerBack,stay,↓reduceIte]; exact next
                case mma => obtain ⟨next,stay⟩ := stepM he prev nu old go
                            simp only [Code.backEnter,workerBack,stay,↓reduceIte]; exact next
          · trivial
    obtain ⟨s,n⟩ := st
    rcases s with s|⟨r,d⟩
    · obtain ⟨s,t,x,w⟩ := s
      change startupClock _≤bound ∧ s.pc≠2855 ∧ (_ → startupClock _<bound)
      cases s
      case' enter r => cases r
      all_goals exact ⟨by dsimp only [startupClock]; omega,by decide,
        by dsimp only [startupClock]; omega⟩
    · rcases r with (r|r)
      · cases r with
        | prologue => have low := data_warp hp hX hk hs; omega
        | dispatch w x =>
          rcases d with s|⟨i,s⟩
          · obtain ⟨s,r⟩ := s
            obtain ⟨rfl,h|h|h⟩ := inv <;> cases h
            all_goals refine ⟨?_,?_,?_⟩
            all_goals first | (change (2337:Nat)≠2855; decide) | (change (2338:Nat)≠2855; decide) |
              (change (2340:Nat)≠2855; decide) |
              (simp only [schedule,siteClock,workerClock,dispatchClock,Lib.Slots.publish,
                ite_true]; omega)
          · cases i
            case loader =>
              refine ⟨clockL s inv,?_,fun len => ?_⟩
              · change s.site.pc≠2855
                generalize s.site=z
                cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
              · exact Nat.lt_of_le_of_ne (clockL s inv)
                  (seenL (List.getElem?_eq_getElem len) hs inv)
            case mma =>
              refine ⟨clockM s inv,?_,fun len => ?_⟩
              · change s.site.pc≠2855
                generalize s.site=z
                cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
              · exact Nat.lt_of_le_of_ne (clockM s inv)
                  (seenM (List.getElem?_eq_getElem len) hs inv)
      · exact (launch_lane hp hX hk hs).elim
  exact deadline_of_states hp hX hg atState

end PTX.Kernels.InklingRelDecode.Proof
