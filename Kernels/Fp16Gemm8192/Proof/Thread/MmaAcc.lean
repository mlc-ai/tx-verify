-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Rings

@[expose] public section

/-! # The MMA warps' accumulator polls and commits

An MMA thread polls its accumulator-empty barrier once per task, with the parity after its own
successful polls on it, and commits to its accumulator-full barrier after its last trip. These
counts are kept by `Mma.Counts` (`MmaCounts`); `Mma.acc_poll_parity` and `Mma.acc_commit_budget`
are their projections to the ring layer, and `Mma.wait_site` and `Mma.commit_site` say which site
polls or commits. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- The MMA thread polls at its full polls (slot `s`'s full barrier, the trip parity), its
accumulator poll (its accumulator's empty barrier, `ap`) and its CLC poll. -/
theorem wait_site (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? =
      some ins) (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    (∃ s : Fin 4, d.site = .full s ∧ m = Bar.loc L (g / L.block) ⟨.input, s.val, true⟩ ∧
      p = d.fp) ∨
    (d.site = .accWait ∧ m = accBar L g (d.w % 2) false ∧ p = d.ap) ∨
    (d.site = .clcWait ∧ m.addr = L.sharedBase + 104) := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  cases hp : site.polls with
  | false => exact (fires_notWait (eventTmpl_notWait (code_notPoll site hp hc)) hf _ _ _ _ _
    hk).elim
  | true =>
    cases site with
    | full s =>
      obtain ⟨ok', acq', sc', rfl⟩ := full_event hpre s rfl hi hat hc hf
      simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, rfl, -⟩ := hk
      exact .inl ⟨s, rfl, by simp only [Bar.loc, Bar.off, Nat.add_assoc], rfl⟩
    | accWait =>
      obtain ⟨ok', acq', sc', rfl⟩ := accWait_event hpre rfl hi hat hc hf
      simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, rfl, -⟩ := hk
      exact .inr (.inl ⟨rfl, by simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and]; omega, rfl⟩)
    | clcWait =>
      obtain ⟨p', ok', acq', sc', -, rfl⟩ := clcWait_event hpre rfl hat hc hf
      simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact .inr (.inr ⟨rfl, rfl⟩)
    | _ => simp [Site.polls] at hp

set_option maxHeartbeats 4000000 in
/-- The MMA thread commits at its slot commits and at its accumulator commit. -/
theorem commit_site (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? =
      some ins) (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {sp : TcCommit.Spec} (hk : e.kind = .tc (.commit sp)) :
    (∃ s : Fin 4, d.site = .commit s ∧ sp = commitSpec L g s) ∨
    (d.site = .accCommit ∧ sp = accSpec L g d.w) := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  by_cases hs : site.commits = false
  · exact (notCommit_fires site hs hc hf sp hk).elim
  · cases site with
    | commit s =>
      obtain rfl := commit_event hpre hg s rfl hat hc hf
      cases hk
      exact .inl ⟨s, rfl, rfl⟩
    | accCommit =>
      obtain rfl := accCommit_spec hpre hg rfl hat hc hf
      cases hk
      exact .inr ⟨rfl, rfl⟩
    | _ => simp [Site.commits] at hs

end Mma

/-- An MMA thread's poll of accumulator empty barrier `j` uses the parity after its own successful
polls on it. -/
theorem Mma.acc_poll_parity {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.mma m))))
    {j p : Nat} {ok acq : Bool} {sc : MbarScope} (hj : j < 2)
    (hk : e.kind = .wait (Mma.accBar L g j false) p ok acq sc) :
    p % 2 = (okPolls (Mma.accBar L g j false) ((X.tr g).take k) + 1) % 2 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, ⟨hi, -⟩, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  rcases Mma.wait_site hpre hi hat hc hfire hk with ⟨s, -, h, -⟩ | ⟨hs, h, rfl⟩ | ⟨-, h⟩
  · have := congrArg Loc.addr h
    simp only [Bar.loc, Bar.off] at this
    omega
  · have hjw : j = m.w % 2 := by
      have := congrArg Loc.addr h
      simp only [Bar.loc, Bar.off] at this
      omega
    subst hjw
    have hA := hC.accPar (by rw [hs]; decide) (by simp [Mma.Site.done, hs])
    simp only [Mma.holdsAcc, hs] at hA
    omega
  · simp only [Bar.loc, Bar.off] at h
    omega

/-- An MMA thread's commit to accumulator full barrier `j` follows a successful poll of accumulator
empty barrier `j` that no earlier commit to it has used. -/
theorem Mma.acc_commit_budget {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.mma m))))
    {sp : TcCommit.Spec} {j : Nat} (hj : j < 2) (hk : e.kind = .tc (.commit sp))
    (hm : sp.mbar = Mma.accBar L g j true) :
    ((X.tr g).take k).countP (commitsTo sp.mbar) + 1 ≤
      okPolls (Mma.accBar L g j false) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, ⟨hi, -⟩, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  rcases Mma.commit_site hpre hg hat hc hfire hk with ⟨s, -, rfl⟩ | ⟨hs, rfl⟩
  · have := congrArg Loc.addr hm
    simp only [commitSpec, Bar.loc, Bar.off] at this
    omega
  · have hjw : j = m.w % 2 := by
      have := congrArg Loc.addr hm
      simp only [accSpec, Bar.loc, Bar.off] at this
      omega
    have hA := hC.acc j hj
    rw [hm]
    simp [hjw, Mma.holdsAcc, hs] at hA ⊢
    omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
