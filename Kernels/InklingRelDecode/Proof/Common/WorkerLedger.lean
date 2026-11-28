-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.History
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

/-- The instruction and its ordinary event, available in local count-preservation proofs. -/
def SourceAt (L : Launch) (g pc : Nat) (e : Event) : Prop :=
  ∃ (t : TState) (ins : Instr) (o : Option TState), kernel.code[pc]? = some ins ∧
    Fires pc (eventTmpl Assumptions.all L g t ins.op) e o ∧ ∀ f, e.kind ≠ .ub f

private def sourceTable (Q : Params) (L : Launch) : RoleTable (thread Q L) where
  J := guardedTable Q L
  Ev g d e := SourceAt L g ((thread Q L g).pc d) e

private theorem sourceShape {Q L} : (sourceTable Q L).ShapeOkU (fun g => g < L.threads) :=
  ⟨fun _ _ _ t ins _ o _ _ _ hc fire hu => ⟨t,ins,o,hc,fire,hu⟩⟩

/-- A ledger rooted before startup. Its dispatch predicate sees the counts left by
the startup shuffle and the preceding calls, including on returns to dispatch. -/
structure WorkerLedger (Q : Params) (L : Launch) where
  startup : Nat → Startup.D → (Cls → Nat) → Prop
  worker : ∀ g w x, (workerCode Q L g w x).D → (Cls → Nat) → Prop
  init : ∀ g, startup g (Startup.init L g) (fun _ => 0)
  first : ∀ g d n e d', startup g d n → SourceAt L g d.site.pc e →
    Startup.succ L g d e = some (some d') → startup g d' (Code.bump cls n e)
  entry : ∀ g d n, startup g d n → d.site = .enter .worker →
    worker g d.w d.x (workerCode Q L g d.w d.x).init n
  step : ∀ g w x d n e d', worker g w x d n → workerInv Q L g w x d n →
    SourceAt L g ((workerCode Q L g w x).pc d) e →
    (workerCode Q L g w x).next d e = some (some d') → workerInv Q L g w x d' (Code.bump cls n e) →
    worker g w x d' (Code.bump cls n e)

def WorkerLedger.holds {Q L g} (H : WorkerLedger Q L) :
    (thread Q L g).D → Prop
  | (.inl s,n) => H.startup g s n
  | (.inr ⟨.inl (.dispatch w x),d⟩,n) => H.worker g w x d n
  | _ => True

private theorem WorkerLedger.enter {Q L g} (H : WorkerLedger Q L) {d n}
    (h : H.startup g d n) : H.holds (Code.enter (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc) (Code.gatedExit Startup.enterOf (sel L g))
      d,n) := by
  obtain ⟨site,tm,x,w⟩ := d
  cases site <;> try exact h
  rename_i r
  cases r with
  | dp => trivial
  | worker => exact H.entry g _ _ h rfl

theorem WorkerLedger.at_holds {Q L m X g} (H : WorkerLedger Q L) (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    {σ k} (nu : NoUbBefore X g k) (hs : stateAt (thread Q L) X g k = some (some σ)) :
    H.holds σ := by
  apply RoleTable.stateInvU (T := sourceTable Q L) (fun g hg => thread_sound hp hg) hX
    sourceShape (show (sourceTable Q L).Followed X _ from hf) (P := fun i s =>
      s.2 .ub=0 → @WorkerLedger.holds Q L i H s) hg _ _ k _ nu hs (prefix_ub_zero hs nu)
  · exact fun _ => H.enter (H.init g)
  · rintro ⟨s,n⟩ e ⟨s',n'⟩ hj _ src ih hn hj' zero
    obtain ⟨next,count⟩ := Code.counted_next_some hn
    change n' = Code.bump cls n e at count
    subst n'
    have before := zero_before_bump zero
    have prev := ih before
    rcases s with d | ⟨r,d⟩
    · change (Startup.succ L g d e).map _ = _ at next
      cases hv : Startup.succ L g d e with
      | none => simp [hv] at next
      | some opt =>
        cases opt with
        | none => simp [hv] at next
        | some d' =>
          simp only [hv,Option.map_some,Option.some.injEq] at next
          subst s'
          exact H.enter (H.first g _ _ _ _ prev src hv)
    · rcases r with r|r
      · cases r with
        | dispatch w x =>
          change ((workerCode Q L g w x).next d e).map _ = _ at next
          obtain ⟨_, fired, pair⟩ := Option.map_eq_some_iff.mp next
          obtain ⟨d',rfl,rfl⟩ := Option.map_eq_some_iff.mp pair
          exact H.step g _ _ _ _ _ _ prev (hj before).2 src fired (hj' zero).2
        | prologue =>
          change ((dataCode Q L g _).next d e).map _ = _ at next
          obtain ⟨_, h, eq⟩ := Option.map_eq_some_iff.mp next
          obtain ⟨_,_,eq⟩ := Option.map_eq_some_iff.mp eq
          cases eq; trivial
      · cases r <;> cases next

theorem WorkerLedger.at_worker {Q L m X g} (H : WorkerLedger Q L) (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    {w x d n k} (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dispatch w x),d⟩,n))) :
    H.worker g w x d n :=
  H.at_holds hp hX hf hg nu hs

theorem WorkerLedger.at_startup {Q L m X g} (H : WorkerLedger Q L) (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    {d n k} (nu : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k = some (some (.inl d,n))) : H.startup g d n :=
  H.at_holds hp hX hf hg nu hs

end PTX.Kernels.InklingRelDecode.Proof
