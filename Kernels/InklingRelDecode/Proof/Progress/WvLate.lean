-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuAll
public import Kernels.InklingRelDecode.Proof.Interface.WvAnchor

@[expose] public section

/-!
# After a role: the later round of the dispatch loop and the exit role

* `noExit_of_end`: a thread whose machine is at a state after its last event has no exit event
  (an exit is the last event, and the machine stops at it).
* `late_back`: a worker state of the later round of the dispatch loop (`Worker.late`) or of the
  exit role follows a role's last state (`wrap = 1`): the round marker is set only by a role's
  return (`Worker.bumpPro`), and the exit role is entered only from the later round's load of the
  role byte (its count of register requests is at least 4, `phase_inv`, so the marker is set,
  `Wu.late_inv`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **A thread whose machine is at a state after its last event has not exited.** -/
theorem noExit_of_end (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s)) :
    ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩ := by
  intro j pc hj
  have hg := Frame.lt_of_get hX hj
  have hj' : (X.tr g)[j]? = some ⟨pc, .exit⟩ := hj
  obtain ⟨o, hr⟩ := hX.thr g hg
  have hlast := Run.end_last hr hj' (.inr rfl)
  rw [← hlast] at hσ
  rw [St, Frame.stateAt_succ hj'] at hσ
  rcases exit_event_state hX hf.sound hf.tracked hj with ⟨d, hσj, hs⟩ | ⟨x, hσj, hs⟩
  · have h1 : Frame.stateAt (code L Q) X g j = some (some (.d (.epi d))) := hσj
    rw [h1] at hσ
    have hn : (threadCode L g Q).next (.d (.epi d)) ⟨pc, .exit⟩ = some (some s) := hσ
    rw [next_d] at hn
    obtain ⟨site, rest⟩ := d
    simp only at hs
    subst hs
    simp [DComp.next, Epi.next] at hn
  · have h1 : Frame.stateAt (code L Q) X g j = some (some (.w (.exit x))) := hσj
    rw [h1] at hσ
    have hn : (threadCode L g Q).next (.w (.exit x)) ⟨pc, .exit⟩ = some (some s) := hσ
    rw [next_w] at hn
    obtain ⟨site, P⟩ := x
    simp only at hs
    subst hs
    have h2 : WComp.next L g (.exit ⟨.ret, P⟩) ⟨pc, .exit⟩ = none := rfl
    rw [h2] at hn
    cases hn

/-- A state of the later round of the dispatch loop or of the exit role. -/
def LateSt : TSt → Prop
  | .w (.worker w) => Worker.late w.P
  | .w (.exit _) => True
  | _ => False

/-- **A later-round or exit state follows a role's last state.** -/
theorem late_back (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → LateSt s →
      ∃ j σ, j < k ∧ St Q L X g j = some (some (.w σ)) ∧ wrap σ = 1 := by
  intro k
  induction k with
  | zero =>
    intro s _ hs hl
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    by_cases hd : g % L.block < 128
    · have he : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
        show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init) = _
        simp only [hd, ite_true]
      rw [he] at hl
      exact hl.elim
    · have he : (threadCode L g Q).init =
          .w (.worker (Worker.D.start (Worker.startPro Q))) := by
        show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init) = _
        simp only [hd, ite_false]
      rw [he] at hl
      exact absurd hl (Wu.not_late_start Q)
  | succ k ih =>
    intro s' hk hs' hl
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some s') := hs''
        have hσ' : St Q L X g k = some (some s) := hσ
        have back : LateSt s → ∃ j σ, j < k + 1 ∧ St Q L X g j = some (some (.w σ)) ∧
            wrap σ = 1 := by
          intro h
          obtain ⟨j, σ, hj, h1, h2⟩ := ih s (by omega) hσ' h
          exact ⟨j, σ, by omega, h1, h2⟩
        obtain ⟨hto, -⟩ := phase_inv hpre hX hS hR k s (by omega) hσ'
        obtain ⟨hto', t', h1', h2', h3', h4', h5', h6'⟩ :=
          phase_inv hpre hX hS hR (k + 1) s' hk hs'
        cases s with
        | d s0 =>
          obtain ⟨a, -, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s0 e).map
            (Option.map TSt.d) = some (some s') from hn)
          exact hl.elim
        | w s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
            (Option.map TSt.w) = some (some s') from hn)
          have hs0 : wTo s0 = false := hto
          cases a with
          | worker w =>
            obtain ⟨site, P⟩ := w
            have hlate : Worker.late P := hl
            rcases Wu.late_next ha hs0 rfl with ⟨P0, rfl, -, rfl⟩ | ⟨P0, v, rfl, -, rfl⟩ |
              ⟨P0, rfl, -, rfl⟩ | ⟨P0, rfl, -, rfl⟩ | ⟨P0, rfl, -, rfl⟩ |
              ⟨P0, rfl, -, rfl⟩ | hst | ⟨-, hw, -⟩
            · exact back hlate
            · exact back ((Wu.late_setTm _ _).mp hlate)
            · exact back hlate
            · exact back hlate
            · exact back hlate
            · exact back hlate
            · subst hst
              simp [tTo, wTo] at hto'
            · exact ⟨k, s0, by omega, hσ', hw⟩
          | exit x =>
            cases s0 with
            | worker w =>
              by_cases hsr : w.site = .ldRole
              · obtain ⟨site0, P0⟩ := w
                simp only at hsr
                subst hsr
                have hk2 : tKind (.w (.exit x)) = 2 := rfl
                have ht1 := h5' hk2
                have hp1 : (tPh (.w (.exit x))).1 = 1 := rfl
                have hrq := Wu.rqN_succ hX hS he hσ'
                have hr0 : rInc (tReq (.w (.worker ⟨.ldRole, P0⟩))) = 0 := rfl
                rw [hr0] at hrq
                have hge : 3 ≤ rqN X g k := by omega
                have hlt := (Wu.late_inv hpre hX hS hR k _ (by omega) hσ').2 P0 .ldRole
                  (.inr (.inr rfl)) rfl
                exact back (hlt.mpr hge)
              · rw [Wt.next_worker_eq hsr] at ha
                obtain ⟨b, -, hb⟩ := Ledger.mapInv ha
                cases hb
            | idle d =>
              by_cases hsi : d.site = .inc
              · obtain ⟨s1, P0⟩ := d
                simp only at hsi
                subst hsi
                have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) =
                    some (some (WComp.WSt.exit x)) := ha
                cases h1
              · rw [Wt.next_idle_eq hsi] at ha
                obtain ⟨b, -, hb⟩ := Ledger.mapInv ha
                cases hb
            | loader d P0 =>
              by_cases hsi : d.site = .setMaxInc
              · obtain ⟨s1, pro, i, n, p0, p1, ln⟩ := d
                simp only at hsi
                subst hsi
                have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) =
                    some (some (WComp.WSt.exit x)) := ha
                cases h1
              · rw [Wt.next_loader_eq P0 hsi] at ha
                obtain ⟨b, -, hb⟩ := Ledger.mapInv ha
                cases hb
            | mma d P0 =>
              by_cases hsi : d.site = .setMaxRegInc
              · obtain ⟨s1, i, n, tm, pro⟩ := d
                simp only at hsi
                subst hsi
                have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) =
                    some (some (WComp.WSt.exit x)) := ha
                cases h1
              · rw [Wt.next_mma_eq P0 hsi] at ha
                obtain ⟨b, -, hb⟩ := Ledger.mapInv ha
                cases hb
            | exit x0 => exact back trivial
          | _ => exact hl.elim

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
