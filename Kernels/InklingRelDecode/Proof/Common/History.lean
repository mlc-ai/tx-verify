-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
public import Lemmas.Kernel.Safety.StateInvU
public import Lemmas.Flow.ElectLead
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

private def historyTable (Q : Params) (L : Launch) : RoleTable (thread Q L) where
  J := guardedTable Q L
  Ev g d e := e.pc = (thread Q L g).pc d

private theorem historyShape {Q L} : (historyTable Q L).ShapeOkU (fun g => g < L.threads) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ fire _ => EventFrame.fires_source_pc fire⟩

/-- A step invariant of the dispatcher and its calls. It may use the event PC and the
new ledger, and starts at dispatch independently of earlier startup counts. -/
theorem worker_history {Q L m X g k w x} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g < L.threads)
    (P : (workerCode Q L g w x).D → (Cls → Nat) → Prop)
    (entry : ∀ n, P (workerCode Q L g w x).init n)
    (step : ∀ d n e d', workerInv Q L g w x d n → e.pc = (workerCode Q L g w x).pc d →
      P d n → (workerCode Q L g w x).next d e = some (some d') →
      workerInv Q L g w x d' (Code.bump cls n e) → P d' (Code.bump cls n e))
    {d n} (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dispatch w x),d⟩,n))) : P d n := by
  apply RoleTable.roleInvU (T' := historyTable Q L) (fun g hg => thread_sound hp hg) hX
    historyShape (show (historyTable Q L).Followed X _ from hf) hg (.inl (.dispatch w x))
    (I := fun d n => n .ub=0 → P d n) (fun _ _ => entry _) (fun _ _ _ _ _ _ _ _ _ => entry _)
    _ k d n nu hs (prefix_ub_zero hs nu)
  intro d n e d' hi pc prev hn hnext zero
  have before := zero_before_bump zero
  exact step d n e d' (hi before).2 pc (prev before) hn (hnext zero).2

/-- Lift a per-invocation role invariant through the worker call and return. -/
theorem call_history {Q L m X g k w x} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    (I : ∀ r, (workerFrag Q L g w x r).D → (Cls → Nat) → Prop)
    (start : ∀ r n, I r (workerFrag Q L g w x r).init n)
    (step : ∀ r d n e d', workerInv Q L g w x (.inr ⟨r,d⟩) n →
      e.pc = (workerFrag Q L g w x r).pc d → I r d n →
      (workerFrag Q L g w x r).next d e = some (some d') → I r d' (Code.bump cls n e))
    {r d n} (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x r d n))) : I r d n := by
  let P : (workerCode Q L g w x).D → (Cls → Nat) → Prop := fun d n =>
    match d with | .inl _ => True | .inr ⟨i,s⟩ => I i s n
  apply worker_history hp hX hf hg P (fun _ => trivial) _ nu hs
  rintro (v | ⟨i,s⟩) n e d' hi pc prev hn _
  · change (Dispatch.next L g v e).map _ = _ at hn
    cases hz : Dispatch.next L g v e with
    | none => simp [hz] at hn
    | some op =>
      cases op with
      | none => simp [hz] at hn
      | some v' =>
        simp only [hz,Option.map_some,Option.some.injEq] at hn
        subst d'
        unfold Code.enter
        split <;> first | apply start | trivial
  · change (((workerFrag Q L g w x i).next s e).map _) = _ at hn
    cases hz : (workerFrag Q L g w x i).next s e with
    | none => simp [hz] at hn
    | some op =>
      cases op with
      | none => simp [hz] at hn
      | some s' =>
        simp only [hz,Option.map_some,Option.some.injEq] at hn
        subst d'
        have hh := step i s n e s' hi pc prev hz
        change P (Code.backEnter _ _ workerEntry _ i s') _
        unfold Code.backEnter
        split
        · unfold Code.enter
          split <;> first | apply start | trivial
        · exact hh

/-- Per-worker forms of the call invariant, for use inside the two role directories. -/
theorem mma_history {Q L m X g k w x round} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    (I : Mma.D → (Cls → Nat) → Prop) (start : ∀ n, I {} n)
    (step : ∀ d n e d', e.pc = d.site.pc → I d n →
      Mma.next L g d e = some (some d') → I d' (Code.bump cls n e))
    {d n} (hu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x (.mma round) d n))) :
    I d n := by
  let P : ∀ r, (workerFrag Q L g w x r).D → (Cls → Nat) → Prop
    | .mma _,s,n => I s n
    | .loader _,_,_ => True
  apply call_history hp hX hf hg P _ _ hu hs
  · rintro (r | r) n
    · trivial
    · exact start _
  · rintro (r | r) s n e s' _ pc h hn
    · trivial
    · exact step s n e s' pc h hn

theorem loader_history {Q L m X g k w x round} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    (I : Loader.D → (Cls → Nat) → Prop) (start : ∀ n, I {} n)
    (step : ∀ d n e d', e.pc = d.site.pc → I d n →
      Loader.next L g d e = some (some d') → I d' (Code.bump cls n e))
    {d n} (hu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x (.loader round) d n))) :
    I d n := by
  let P : ∀ r, (workerFrag Q L g w x r).D → (Cls → Nat) → Prop
    | .mma _,_,_ => True
    | .loader _,s,n => I s n
  apply call_history hp hX hf hg P _ _ hu hs
  · rintro (r | r) n
    · exact start _
    · trivial
  · rintro (r | r) s n e s' _ pc h hn
    · exact step s n e s' pc h hn
    · trivial

theorem mma_state {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (lo : 2422 < e.pc) (hi : e.pc < 2557) :
    ∃ w x round, ∃ (d : Mma.D), ∃ n, stateAt (thread Q L) X g k =
      some (some (workerState w x (.mma round) d n)) ∧ e.pc = d.site.pc := by
  obtain ⟨w,x,r,d,n,hs,_⟩ := worker_event hp hX hf he hu (by omega) (by omega) (by omega)
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  cases r with
  | mma => exact ⟨_,_,_,_,_,hs,pc⟩
  | loader =>
    change e.pc = d.site.pc at pc
    have h : ∀ s : Loader.Site, ¬ (2422 < s.pc ∧ s.pc < 2557) := by
      intro s
      cases s <;> first | decide | (rename_i p; fin_cases p <;> decide) |
        (rename_i p b; fin_cases p <;> cases b <;> decide)
    exact (h _ ⟨pc ▸ lo,pc ▸ hi⟩).elim

theorem loader_state {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (lo : 2344 < e.pc) (hi : e.pc < 2422) :
    ∃ w x round, ∃ (d : Loader.D), ∃ n, stateAt (thread Q L) X g k =
      some (some (workerState w x (.loader round) d n)) ∧ e.pc = d.site.pc := by
  obtain ⟨w,x,r,d,n,hs,_⟩ := worker_event hp hX hf he hu (by omega) (by omega) (by omega)
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  cases r with
  | loader => exact ⟨_,_,_,_,_,hs,pc⟩
  | mma =>
    change e.pc = d.site.pc at pc
    have h : ∀ s : Mma.Site, ¬ (2344 < s.pc ∧ s.pc < 2422) := by
      intro s
      cases s <;> first | decide | (rename_i p; fin_cases p <;> decide)
    exact (h _ ⟨pc ▸ lo,pc ▸ hi⟩).elim

theorem elected_of_count {Q L g k X d} {lane}
    (hs : Frame.stateAt (thread Q L) X g k = some (some d)) (h : 0 < d.2 (.winner lane)) :
    Elected ((X.tr g).take k) lane := by
  rw [fcount hs] at h
  obtain ⟨e,hm,hk⟩ := List.countP_pos_iff.mp h
  refine ⟨e,hm,?_⟩
  cases he : e.kind <;> simp [cls,he] at hk
  subst lane
  exact ⟨_,_,rfl⟩

/-- The warp restriction established on entry to the Prologue persists in every
subsequent data-role state, including the final-poll handoff. -/
theorem data_lane {Q L m X g k w e s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.prologue w),.inr ⟨e,s⟩⟩,n))) :
    g%L.block<128 := by
  let I : (dataCode Q L g w).D → (Cls → Nat) → Prop
    | .inl _,_ => True
    | .inr _,_ => g%L.block<128
  apply RoleTable.roleInvU (T' := historyTable Q L) (fun g hg => thread_sound hp hg) hX
    historyShape (show (historyTable Q L).Followed X _ from hf) hg (.inl (.prologue w))
    (I := fun d n => n .ub=0 → I d n) (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial)
    _ k _ _ nu hs (prefix_ub_zero hs nu)
  rintro (v|⟨i,v⟩) n e d' hi _ prev _ _ zero
  · have h := (hi (zero_before_bump zero)).2.1
    cases d' <;> trivial
  · have h := prev (zero_before_bump zero)
    cases d' <;> trivial

end PTX.Kernels.InklingRelDecode.Proof
