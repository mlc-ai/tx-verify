-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
public import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Common.WorkerCall
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Frame PTX.Flow

/-- No MMA step has been issued: the ledger counts none at the QK and the PV pcs. -/
def QkZero (n : Cls → Nat) : Prop :=
  ∀ j : Fin 8, n (.atPc (Mma.qkPc j)) = 0 ∧ n (.atPc (Mma.pvPc j)) = 0

private def mmaLocal {Q L g} (I : Mma.D → (Cls → Nat) → Prop) : (thread Q L g).D → Prop
  | (.inl _,n) => QkZero n
  | (.inr ⟨.inl (.dispatch _ _),.inl s⟩,n) => s.round = 0 → QkZero n
  | (.inr ⟨.inl (.dispatch _ _),.inr ⟨.mma _,d⟩⟩,n) => I d n
  | _ => True

private theorem enter_local {Q L g} (I : Mma.D → (Cls → Nat) → Prop) (s : Startup.D)
    (n : Cls → Nat) (hz : QkZero n) : mmaLocal (Q := Q) (L := L) (g := g) I
      (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> try exact hz
  rename_i r
  cases r with
  | dp => trivial
  | worker => exact fun _ => hz

private theorem entry_mma {v : Dispatch.D} {r : Nat} (h : workerEntry v = some (.mma r)) :
    v.site = .mmaEntry := by
  unfold workerEntry at h
  cases hs : v.site <;> simp [hs] at h ⊢

/-- The startup and the dispatch machine never fire at a QK or a PV pc. -/
private theorem keep_zero {Q L g} {d : (thread Q L g).D} {ev : Event} {n : Cls → Nat}
    (pc : ev.pc = (thread Q L g).pc d) (hd : ∀ w x r s n, d ≠ workerState w x r s n)
    (hz : QkZero n) : QkZero (Code.bump cls n ev) := by
  have never : ∀ p : Nat, 2344 < p → p < 2557 → p ≠ 2422 → ev.pc ≠ p := by
    intro p h1 h2 h3 h
    obtain ⟨w,x,r,s,m,e⟩ := (state_role d).worker (pc ▸ h ▸ h1) (pc ▸ h ▸ h2) (pc ▸ h ▸ h3)
    exact hd _ _ _ _ _ e
  intro j
  have rq : 2344 < Mma.qkPc j ∧ Mma.qkPc j < 2557 ∧ Mma.qkPc j ≠ 2422 := by
    fin_cases j <;> decide
  have rp : 2344 < Mma.pvPc j ∧ Mma.pvPc j < 2557 ∧ Mma.pvPc j ≠ 2422 := by
    fin_cases j <;> decide
  have nq := never _ rq.1 rq.2.1 rq.2.2
  have np := never _ rp.1 rp.2.1 rp.2.2
  simp only [Code.bump, cls, (hz j).1, (hz j).2]
  simp [nq, np, beq_false_of_ne]

/-- **A position-level invariant of the MMA lane**: the step sees the event at the position of
the state (its ledger counts `.all`). -/
theorem mma_history_at {Q L m X g w x round} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (I : Mma.D → (Cls → Nat) → Prop) (start : ∀ n, QkZero n → I {} n)
    (step : ∀ k d n e d', X.get (g,k) = some e → (∀ f, e.kind ≠ .ub f) → n .all = k →
      e.pc = d.site.pc → Mma.Inv d → pollRound 2462 ((X.tr g).take k) = (Mma.polls d).1 →
      pollRound 2510 ((X.tr g).take k) = (Mma.polls d).2 →
      (∃ t ins o, kernel.code[d.site.pc]? = some ins ∧
        Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) → I d n →
      Mma.next L g d e = some (some d') → I d' (Code.bump cls n e))
    {k d n} (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x (.mma round) d n)))
    (zero : n .ub = 0) : I d n := by
  have old : mmaLocal (Q := Q) (L := L) (g := g) I (workerState w x (.mma round) d n) := by
    apply reference_induction (mmaLocal I) _ _ hk hs zero
    · exact enter_local I _ _ (fun _ => ⟨rfl, rfl⟩)
    · rintro j ⟨s,c⟩ ev ⟨sn,cn⟩ get prev hu ih move
      obtain ⟨sub,count⟩ := Code.counted_next_some move
      change cn=Code.bump cls c ev at count
      subst cn
      rcases s with s|⟨r,s⟩
      · have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev hu
        obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub
        exact enter_local I _ _ (keep_zero pc (fun _ _ _ _ _ => nofun) ih)
      · obtain ⟨_,fired,rfl⟩ := Code.glue_inr_some sub
        rcases r with (r|r)
        · cases r with
          | prologue => trivial
          | dispatch w' x' =>
            rcases s with d|⟨i,d⟩
            · change (Dispatch.next L g d ev).map _ = _ at fired
              cases hz : Dispatch.next L g d ev with
              | none => simp [hz] at fired
              | some op =>
                cases op with
                | none => simp [hz] at fired
                | some v' =>
                  simp only [hz,Option.map_some,Option.some.injEq] at fired
                  subst fired
                  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev hu
                  have rm := Dispatch.round_mono hz
                  have zb : v'.round = 0 → QkZero (Code.bump cls c ev) := fun h =>
                    keep_zero pc (fun _ _ _ _ _ => nofun) (ih (by omega))
                  have called := dispatch_called hp hX words get prev hz
                  unfold Code.enter
                  split <;> first | exact zb |
                    (rename_i i hi; cases i <;> first |
                      exact start _ (zb (called.2 (entry_mma hi)).2) | trivial)
            · have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get prev hu
              change ((workerFrag Q L g w' x' i).next d ev).map _ = _ at fired
              cases hz : (workerFrag Q L g w' x' i).next d ev with
              | none => simp [hz] at fired
              | some op =>
                cases op with
                | none => simp [hz] at fired
                | some s' =>
                  simp only [hz,Option.map_some,Option.some.injEq] at fired
                  subst fired
                  have back : ∀ (hh : mmaLocal (Q := Q) (L := L) (g := g) I
                      (Sum.inr ⟨Sum.inl (Role.dispatch w' x'), Sum.inr ⟨i, s'⟩⟩,
                        Code.bump cls c ev)),
                      mmaLocal (Q := Q) (L := L) (g := g) I
                        (Sum.inr ⟨Sum.inl (Role.dispatch w' x'),
                          (Dispatch.code L g (startRegs Q L g w' x') x' 0).backEnter
                            (workerFrag Q L g w' x') workerEntry (workerBack Q L g w' x') i s'⟩,
                          Code.bump cls c ev) := by
                    intro hh
                    have bb : ∀ p, workerBack Q L g w' x' i s' = some p →
                        p.round ≠ 0 ∧ p.site = .head := by
                      intro p h
                      cases i <;> (unfold workerBack at h; split at h <;> simp at h <;>
                        (obtain ⟨-, rfl⟩ := h; simp))
                    unfold Code.backEnter
                    split
                    · rename_i p hb
                      obtain ⟨hr, hs0⟩ := bb p hb
                      unfold Code.enter
                      simp only [workerEntry, hs0]
                      exact fun h => absurd h hr
                    · exact hh
                  apply back
                  cases i with
                  | loader _ => trivial
                  | mma _ =>
                    change ev.pc=d.site.pc at pc
                    have hg := Frame.lt_of_get hX get
                    have nu := noUbBefore_of_get hX get
                    obtain ⟨hi,_,_,hq,hp',-⟩ := reached_table hf hg nu prev
                    obtain ⟨t,ins,o,_,_,hc,ff⟩ := Frame.fired_siteU
                      (fun g hg => thread_sound hp hg) hX get prev hu
                    change kernel.code[d.site.pc]? = some ins at hc
                    change Fires d.site.pc _ ev o at ff
                    exact step j d c ev s' get hu (by
                      have h := fcount prev .all
                      have len : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp get).1
                      simp only [cls,List.countP_true,List.length_take] at h
                      omega) pc hi.1 ((fcount prev (.poll 2462)).symm.trans hq)
                      ((fcount prev (.poll 2510)).symm.trans hp')
                      ⟨t,ins,o,hc,ff⟩ ih hz
        · trivial
  exact old

end PTX.Kernels.InklingRelDecode.Proof
