-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WyPoll
public import Kernels.InklingRelDecode.Proof.Thread.WpSites

@[expose] public section

/-!
# A poll event, its state and its position

`poll_at`: a poll event of a launched thread fires from a state at one of the six poll sites
(`Interface.PollAt` names its object and parity), at the position of that site (`pollPc`). So two
polls at one position are polls of one site (`pollIdx`, `Wp.idx_waitS` …), and the poll branch
after them is selected by `pollAgree` (`pollPc_sel`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The position of the event of a state at a poll site. -/
def pollPc : TSt → Nat
  | .d (.sm d) => Sm.evPc d.site
  | .d (.epi d) => Epi.evPc d.site
  | .w (.loader d _) => d.site.pc
  | .w (.mma d _) => d.site.pc
  | _ => 0

/-- **The shape of a poll from the state, with its position** (`Interface.poll_site` with the
position named). -/
theorem poll_site_pc (hpre : Pre Q L mem0) (hrg : LdRng Q L X) (hg : g < L.threads) {k : Nat}
    {s : TSt}
    (hσ : St Q L X g k = some (some s)) {ins : Instr} (hc : kernel.code[TSt.pc s]? = some ins)
    (hop : isWaitOp ins.op = true) :
    ∃ m par, PollAt L g s m par ∧ ∀ e u,
      (threadCode L g Q).toMachine.Fired (some s) e (some u) →
        ∃ ok, e = ⟨pollPc s, .wait m par ok true .cta⟩ := by
  have hpw : TSt.pc s ∈ waitPcs := OpPcsFast.mem kernel_wait_pcs hc hop
  have hr := treach_stateAt hpre hg hσ
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_wait w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_wait d.site h)
    | exit x => exact absurd hpw (fun h => by simpa using exit_wait x.site h)
    | loader d P =>
      have hs : d.site = .wait := by simpa using loader_wait d.site hpw
      refine ⟨_, _, ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      have h := EvW.loader_shape hpre hr.2 (hrg hg hσ) ⟨t', ⟨ha, hi.2⟩, hf'⟩
      unfold EvW.LdShape at h
      rw [hs] at h
      simp only [pollPc, hs]
      exact h
    | mma d P =>
      have hs : d.site = .kvWait ∨ d.site = .pWait := by simpa using mma_wait d.site hpw
      rcases hs with hs | hs
      · refine ⟨_, _, .inl ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
        have h := EvW.mma_shape hpre hg ⟨t', ⟨ha, hi.2⟩, hf'⟩
        unfold EvW.MmShape at h
        rw [hs] at h
        simp only [pollPc, hs]
        exact h
      · refine ⟨_, _, .inr ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
        have h := EvW.mma_shape hpre hg ⟨t', ⟨ha, hi.2⟩, hf'⟩
        unfold EvW.MmShape at h
        rw [hs] at h
        simp only [pollPc, hs]
        exact h
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_wait d.site h)
    | pro d => exact absurd hpw (fun h => by simpa using pro_wait d.site h)
    | sm d =>
      have hs : d.site = .waitS ∨ d.site = .waitO := by simpa using sm_wait d.site hpw
      rcases hs with hs | hs
      · refine ⟨_, _, .inl ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨ok, he⟩ := Sm.shape_waitS_loc (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs
        exact ⟨ok, by rw [he, SO.loc_sReadyOf]; rfl⟩
      · refine ⟨_, _, .inr ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨ok, he⟩ := Sm.shape_waitO (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs
        exact ⟨ok, by rw [he]; rfl⟩
    | epi d =>
      have hs : d.site = .wait := by simpa using epi_wait d.site hpw
      have hsb : L.sharedBase + 213340 ≤ 2 ^ 18 := hpre.sharedRange
      refine ⟨_, _, ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
      obtain ⟨ok, he⟩ := Epi.shape_wait_oFinal hsb hr.2 (fired_epi hF) hs
      exact ⟨ok, by rw [he, SO.loc_oFinal]; rfl⟩

/-- **A poll event fires from a state at a poll site**, at the site's position, polling the object
and the parity `PollAt` names. -/
theorem poll_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc : Nat} {m : Loc} {p : Nat} {ok acq : Bool}
    {sc : MbarScope} (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ s, St Q L X g k = some (some s) ∧ PollAt L g s m p ∧ pc = pollPc s := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨s, t, ins, o, u, hσ, hc, hfi, hF⟩ := event_pre hX hf.sound hf.tracked hg he
    (not_ends (by intro f h; cases h) (by intro h; cases h)) (no_ub_of_kind (by intro f h; cases h))
  have hop : isWaitOp ins.op = true := by
    cases hq : isWaitOp ins.op
    · exfalso
      refine fires_notWait (eventTmpl_notWait ?_) hfi m p ok acq sc rfl
      intro p' b o' par a' s' h
      simp [isWaitOp, h] at hq
    · rfl
  obtain ⟨m', par, hpa, hsh⟩ := poll_site_pc hpre hf.ldRng hg hσ hc hop
  obtain ⟨ok', hev⟩ := hsh _ u hF
  simp only [Event.mk.injEq, Kind.wait.injEq] at hev
  obtain ⟨rfl, rfl, rfl, -, -, -⟩ := hev
  exact ⟨s, hσ, hpa, rfl⟩

/-- **The position of a state at a poll site is one of the six**, and the poll branch after it is
selected by `pollAgree`. -/
theorem pollPc_sel {s : TSt} {m : Loc} {p : Nat} (h : PollAt L g s m p) :
    Assumptions.all.any (·.uniPoll (pollPc s + 1)) = true := by
  apply pollPcs_sel
  cases s with
  | w s =>
    cases s with
    | loader d P =>
      obtain ⟨hs, -⟩ := h
      simp [pollPc, hs, pollPcs]
    | mma d P =>
      rcases h with ⟨hs, -⟩ | ⟨hs, -⟩ <;> simp [pollPc, hs, pollPcs]
    | _ => exact h.elim
  | d s =>
    cases s with
    | sm d => rcases h with ⟨hs, -⟩ | ⟨hs, -⟩ <;> simp [pollPc, hs, pollPcs]
    | epi d =>
      obtain ⟨hs, -⟩ := h
      simp [pollPc, hs, pollPcs]
    | _ => exact h.elim

end
end PTX.Kernels.InklingRelDecode.Proof.Wp
