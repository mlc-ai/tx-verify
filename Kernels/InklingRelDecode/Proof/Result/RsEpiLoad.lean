-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutOrigin
public import Kernels.InklingRelDecode.Proof.Result.PrChain

@[expose] public section

/-!
# The epilogue's load of the `O` tile and the poll before it

`Out.Inputs.oSource` is stated for every event `k0` of the thread that is a `tcgen05.ld` at the
address `Prm.taddr` returning `D.o`. The softmax region's rescale loads (`Sm.Site.ldO`) are loads of
64 words of `O` at that address as well, and their words can equal `D.o` (an `O` row that a block
leaves unchanged), so the statement is false for them: their read source is an earlier PV MMA, not
the last one. The epilogue's own load is the one `Inputs.oSource` has to be about, and it is the
one the state names:

* `ld_event'`: an epilogue state past the load carries an earlier state `d0` at the load's site
  (`Epi.Site.ld`), with the same registers, whose event is the `tcgen05.ld` at `Prm.taddr` with the
  words `D.o`.
* `ld_poll`: the state at the load's site is two events after the successful poll of `o_final`
  (the poll, the broadcast of the warp index, the load): the event two before is the poll, an
  acquire poll at CTA scope of the barrier `o_final` of the thread's CTA.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The epilogue's load event, with its state.** An epilogue state past the load (on the
normal path) has an earlier state at the load's site with the same registers, and the event of that
state is the `tcgen05.ld` at the address of the registers that returned the state's words. -/
theorem ld_event' (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : Interface.ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ (k : Nat) (d : Epi.D), Interface.St Q L X g k = some (some (.d (.epi d))) →
      d.sk = false → 3 ≤ sitePos d.site →
      ∃ (k0 pc : Nat) (d0 : Epi.D), Interface.St Q L X g k0 = some (some (.d (.epi d0))) ∧
        d0.site = .ld ∧ d0.pr = d.pr ∧
        X.get (g, k0) = some ⟨pc, .tc (.ld d.pr.taddr d.o (.s16x32bx2 64))⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hσ hsk hp
    have hne : (Interface.TSt.d (.epi d)) ≠ (Interface.code L Q g).init := by
      simp only []
      split_ifs <;> simp
    obtain ⟨k0, e, s0, hk0, he, hσ0, hn⟩ := Interface.stateAt_pred hσ hne
    rcases epi_pred hn with ⟨d0, rfl, hnx⟩ | ⟨dsm, rfl, hd⟩
    · obtain ⟨hpr, -, hso, hsite⟩ := next_site hnx
      by_cases hs0 : d0.site = .ld
      · have hnx' : ¬ Interface.ExitState (.d (.epi d0)) := by
          show ¬ d0.site = .exit
          rw [hs0]
          nofun
        obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg (g := g) (k := k0) he hσ0 hnx'
        obtain ⟨vals, hl, he2⟩ := Epi.shape_ld (Interface.fired_epi hF) hs0
        rw [he2, Epi.ld_next hs0 hl] at hnx
        have hd : d = { d0 with site := .waitLd, o := vals } := (Option.some.inj
          (Option.some.inj hnx)).symm
        refine ⟨k0, Epi.evPc d0.site, d0, hσ0, hs0, ?_, ?_⟩
        · rw [hd]
        · show (X.tr g)[k0]? = _
          rw [he, he2, hd]
      · have hso' : d.o = d0.o := hso.resolve_left hs0
        have hsk0 : d0.sk = false := by
          obtain ⟨-, hs, -, -⟩ := next_site hnx
          rw [← hs]
          exact hsk
        have hp0 : 3 ≤ sitePos d0.site := by
          rcases hsite with h | h | ⟨h, -⟩ | ⟨h, -⟩
          · rw [← h]; exact hp
          · have : sitePos d0.site ≠ 2 := fun h2 => hs0 (sitePos_inj (by rw [h2]; rfl))
            omega
          · rcases h with h | ⟨-, h⟩
            · rw [h]; rfl
            · rw [hsk0] at h; exact absurd h (by simp)
          · rw [h]; show 3 ≤ 73; omega
        obtain ⟨k1, pc, d1, hσ1, hs1, hpr1, hget⟩ := ih k0 hk0 d0 hσ0 hsk0 hp0
        have hpr' : d.pr = d0.pr := Epi.next_pr_ne hnx (by
          intro h; rw [h] at hp0; simp [sitePos] at hp0)
        exact ⟨k1, pc, d1, hσ1, hs1, hpr1.trans hpr'.symm, by rw [hget, hso', hpr']⟩
    · exfalso
      by_cases hs : (DComp.exitIn L g dsm).skip = true
      · simp only [hs, ↓reduceIte] at hd
        subst hd
        exact absurd hsk (by simp [Epi.D.startSk, Epi.D.entry])
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hd
        subst hd
        have : sitePos (Epi.D.start (Br.prm (DComp.exitIn L g dsm))).site = 0 := rfl
        omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The epilogue site before the load's is the broadcast. -/
theorem next_to_ld {d1 d0 : Epi.D} {e : Event} (hn : Epi.next d1 e = some (some d0))
    (hs : d0.site = .ld) : d1.site = .shfl := by
  obtain ⟨site, pr, o, sk⟩ := d1
  cases site
  case shfl => rfl
  all_goals
    exfalso
    simp only [Epi.next] at hn
    (repeat' split at hn)
    all_goals first
      | (cases hn; done)
      | (try simp only [Option.some.injEq] at hn
         subst hn
         first
           | (simp at hs; done)
           | (simp only [Epi.D.stores] at hs; split_ifs at hs <;> cases hs; done)
           | (simp only [Epi.stNext] at hs; split_ifs at hs <;> simp at hs; done))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The epilogue's step to the broadcast's site comes from the poll's, with a successful poll. -/
theorem next_to_shfl {d1 d0 : Epi.D} {e : Event} (hn : Epi.next d1 e = some (some d0))
    (hs : d0.site = .shfl) :
    d1.site = .wait ∧ ∃ l p acq sc, e.kind = .wait l p true acq sc := by
  obtain ⟨site, pr, o, sk⟩ := d1
  cases site
  case wait =>
    refine ⟨rfl, ?_⟩
    simp only [Epi.next] at hn
    split at hn
    · rename_i l p ok acq sc hk
      split at hn
      · exact ⟨l, p, acq, sc, by rw [hk]; rename_i hok; rw [hok]⟩
      · simp only [Option.some.injEq] at hn
        subst hn
        simp at hs
    · cases hn
  all_goals
    exfalso
    simp only [Epi.next] at hn
    (repeat' split at hn)
    all_goals first
      | (cases hn; done)
      | (try simp only [Option.some.injEq] at hn
         subst hn
         first
           | (simp at hs; done)
           | (simp only [Epi.D.stores] at hs; split_ifs at hs <;> cases hs; done)
           | (simp only [Epi.stNext] at hs; split_ifs at hs <;> simp at hs; done))

/-- **The poll of `o_final` before the epilogue's load.** At the load's site, two events after the
successful poll: the event two before is the poll of the barrier `o_final` of the thread's CTA,
with parity 0 and acquire semantics at CTA scope. -/
theorem ld_poll (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : Interface.ThreadFacts Q L mem0 X) (hg : g < L.threads) {k0 : Nat} {d0 : Epi.D}
    (hk0 : k0 < (X.tr g).length) (hσ : Interface.St Q L X g k0 = some (some (.d (.epi d0))))
    (hs : d0.site = .ld) :
    ∃ pc sc, 2 ≤ k0 ∧
      X.get (g, k0 - 2) = some ⟨pc, .wait (EvW.oFinal L (g / L.block)) 0 true true sc⟩ := by
  have hne : ∀ d : Epi.D, (Interface.TSt.d (.epi d)) ≠ (Interface.code L Q g).init := by
    intro d
    simp only []
    split_ifs <;> simp
  have hstart : ∀ {dsm : Sm.D} {d : Epi.D},
      d = (if (DComp.exitIn L g dsm).skip then Epi.D.startSk (Br.prm (DComp.exitIn L g dsm))
        else Epi.D.start (Br.prm (DComp.exitIn L g dsm))) → d.site ≠ .ld ∧ d.site ≠ .shfl := by
    intro dsm d hd
    subst hd
    split_ifs
    · simp [Epi.D.startSk, Epi.D.entry]
    · simp [Epi.D.start, Epi.D.entry]
  obtain ⟨k1, rfl⟩ : ∃ k1, k0 = k1 + 1 := by
    rcases Nat.eq_zero_or_pos k0 with h | h
    · subst h
      exact absurd (Option.some.inj (Option.some.inj (by
        have h0 := hσ
        rw [Interface.St, Frame.stateAt_zero] at h0
        exact h0.symm))) (hne d0)
    · exact ⟨k0 - 1, by omega⟩
  obtain ⟨e1, s1, he1, hσ1, hn1⟩ := Pr.pred_adj (by omega) hσ
  rcases epi_pred hn1 with ⟨d1, rfl, hnx1⟩ | ⟨dsm, rfl, hd⟩
  · have hsh1 := next_to_ld hnx1 hs
    obtain ⟨k2, rfl⟩ : ∃ k2, k1 = k2 + 1 := by
      rcases Nat.eq_zero_or_pos k1 with h | h
      · subst h
        exact absurd (Option.some.inj (Option.some.inj (by
          have h0 := hσ1
          rw [Interface.St, Frame.stateAt_zero] at h0
          exact h0.symm))) (hne d1)
      · exact ⟨k1 - 1, by omega⟩
    obtain ⟨e2, s2, he2, hσ2, hn2⟩ := Pr.pred_adj (by omega) hσ1
    rcases epi_pred hn2 with ⟨d2, rfl, hnx2⟩ | ⟨dsm, rfl, hd⟩
    · obtain ⟨hw2, l, p, acq, sc, hk⟩ := next_to_shfl hnx2 hsh1
      have hnx' : ¬ Interface.ExitState (.d (.epi d2)) := by
        show ¬ d2.site = .exit
        rw [hw2]
        nofun
      have hge2 : X.get (g, k2) = some e2 := he2
      obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg (g := g) (k := k2) hge2 hσ2 hnx'
      have hm : Epi.Means Q L g d2.pr := (hf.reach hg hσ2).2
      obtain ⟨ok, he⟩ := Epi.shape_wait_oFinal (EvW.mmEnv_of_pre hpre).sb hm
        (Interface.fired_epi hF) hw2
      rw [he] at hk
      simp only [Kind.wait.injEq] at hk
      obtain ⟨hl, hp, hok, hacq, hsc⟩ := hk
      subst hl hp hok hacq hsc
      refine ⟨Epi.evPc d2.site, .cta, by omega, ?_⟩
      have : k2 + 1 + 1 - 2 = k2 := by omega
      rw [this, hge2, he, SO.loc_oFinal]
    · exact absurd hsh1 (hstart hd).2
  · exact absurd hs (hstart hd).1

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
