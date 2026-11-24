-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FootOrder
public import Kernels.InklingRelDecode.Proof.Interface.FootPhase
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Interface.PrefixPro

@[expose] public section

/-!
# The early shared stores exist before the barrier-1 arrivals that follow them

A default-partition thread that is at a prologue site after `st8`, or in the softmax region or the
epilogue, has fired the role-table store `st8` earlier in its trace (`exists_st8`); one that is at
an epilogue site after `stTab` has fired the table store (`exists_stTab`). The measure is the
order of the sites (`FootOrder`): a step into the sites after a store comes from the store or from
the sites after it.

`st8_event` and `stTab_event` give the event at the state of such a store: the write of the
role table's four bytes at `sharedBase + 213336`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The default-partition states after the prologue's role-table store. -/
def AfterSt8 : TSt → Prop
  | .d (.pro d) => d.site.afterSt8 = true
  | .d (.sm _) => True
  | .d (.epi _) => True
  | _ => False

/-- The default-partition states after the epilogue's table store. -/
def AfterTab : TSt → Prop
  | .d (.epi d) => d.site.afterTab = true
  | _ => False

/-- A step into a state after the role-table store comes from the store or from such a state. -/
theorem next_afterSt8 {g : Nat} {s s' : TSt} {e : Event}
    (hn : (threadCode L g Q).next s e = some (some s')) (hs : AfterSt8 s') :
    AfterSt8 s ∨ ∃ d : ProA.D, s = .d (.pro d) ∧ d.site = .st8 := by
  cases s with
  | w s =>
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map (Option.map TSt.w) =
      some (some s') from hn)
    exact hs.elim
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from hn)
    cases s with
    | dstart d =>
      exfalso
      change DComp.dstartNext L g Q d _ = _ at ha
      unfold DComp.dstartNext at ha
      obtain ⟨d', -, hs'⟩ := map_map_eq_some_some ha
      split at hs'
      · subst hs'
        exact absurd hs (by simp [AfterSt8, ProA.D.start, ProA.Site.afterSt8])
      · subst hs'
        exact hs
    | pro dp =>
      change DComp.proNext L g Q dp _ = _ at ha
      unfold DComp.proNext at ha
      split at ha
      · rename_i hb
        left
        show dp.site.afterSt8 = true
        rw [hb]
        rfl
      · obtain ⟨d3, hd3, h3⟩ := map_map_eq_some_some ha
        subst h3
        obtain ⟨site, dt⟩ := dp
        rcases ProA.next_afterSt8 hd3 hs with h | h
        · right
          exact ⟨_, rfl, h⟩
        · left
          exact h
    | sm d => left; trivial
    | epi d => left; trivial

/-- A step into a state after the epilogue's table store comes from the store or from such a
state. -/
theorem next_afterTab {g : Nat} {s s' : TSt} {e : Event}
    (hn : (threadCode L g Q).next s e = some (some s')) (hs : AfterTab s') :
    AfterTab s ∨ ∃ d : Epi.D, s = .d (.epi d) ∧ d.site = .stTab := by
  cases s with
  | w s =>
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map (Option.map TSt.w) =
      some (some s') from hn)
    exact hs.elim
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from hn)
    cases s with
    | dstart d =>
      exfalso
      change DComp.dstartNext L g Q d _ = _ at ha
      unfold DComp.dstartNext at ha
      obtain ⟨d', -, hs'⟩ := map_map_eq_some_some ha
      split at hs' <;> (subst hs'; exact hs)
    | pro dp =>
      exfalso
      change DComp.proNext L g Q dp _ = _ at ha
      unfold DComp.proNext at ha
      split at ha
      · split at ha
        · simp only [Option.some.injEq] at ha
          subst ha
          exact hs
        · cases ha
      · obtain ⟨d3, -, h3⟩ := map_map_eq_some_some ha
        subst h3
        exact hs
    | sm d =>
      exfalso
      change DComp.smNext L g d _ = _ at ha
      unfold DComp.smNext at ha
      split at ha
      · unfold DComp.exitNext at ha
        split at ha
        · simp only [Option.some.injEq] at ha
          subst ha
          split at hs
          · exact absurd hs (by simp [AfterTab, Epi.startSk_afterTab])
          · exact absurd hs (by simp [AfterTab, Epi.D.start, Epi.D.entry, Epi.Site.afterTab])
        · cases ha
      · obtain ⟨d3, -, h3⟩ := map_map_eq_some_some ha
        subst h3
        exact hs
    | epi d =>
      change (Epi.next d _).map (Option.map DComp.St.epi) = _ at ha
      obtain ⟨d', hd', h3⟩ := map_map_eq_some_some ha
      subst h3
      rcases Epi.next_afterTab hd' hs with h | h
      · right
        exact ⟨d, rfl, h⟩
      · left
        exact h

theorem init_notAfterSt8 (g : Nat) : ¬ AfterSt8 (code L Q g).init := by
  show ¬ AfterSt8 (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init)
  split <;> exact fun h => h

theorem init_notAfterTab (g : Nat) : ¬ AfterTab (code L Q g).init := by
  show ¬ AfterTab (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init)
  split <;> exact fun h => h

/-- **A state after the role-table store has the store's state earlier in its thread's run.** -/
theorem exists_st8 {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → AfterSt8 s →
      ∃ j < k, ∃ d : ProA.D, St Q L X g j = some (some (.d (.pro d))) ∧ d.site = .st8 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hσ hs
    by_cases hinit : s = (code L Q g).init
    · subst hinit
      exact absurd hs (init_notAfterSt8 g)
    · obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hσ hinit
      rcases next_afterSt8 hn hs with h | ⟨d, rfl, hd⟩
      · obtain ⟨j, hj, d, hd, hsite⟩ := ih k0 hlt s0 hs0 h
        exact ⟨j, by omega, d, hd, hsite⟩
      · exact ⟨k0, hlt, d, hs0, hd⟩

/-- **A state after the epilogue's table store has the store's state earlier in its run.** -/
theorem exists_stTab {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → AfterTab s →
      ∃ j < k, ∃ d : Epi.D, St Q L X g j = some (some (.d (.epi d))) ∧ d.site = .stTab := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hσ hs
    by_cases hinit : s = (code L Q g).init
    · subst hinit
      exact absurd hs (init_notAfterTab g)
    · obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hσ hinit
      rcases next_afterTab hn hs with h | ⟨d, rfl, hd⟩
      · obtain ⟨j, hj, d, hd, hsite⟩ := ih k0 hlt s0 hs0 h
        exact ⟨j, by omega, d, hd, hsite⟩
      · exact ⟨k0, hlt, d, hs0, hd⟩

/-- **The event at the role-table store's state** is the write of the table `0x01000202` at
`sharedBase + 213336` of the thread's CTA. -/
theorem st8_event (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g j : Nat} {e : Event} {d : ProA.D}
    (hg : g < L.threads) (he : X.get (g, j) = some e)
    (hσ : St Q L X g j = some (some (.d (.pro d)))) (hs : d.site = .st8) :
    ∃ pc, e = ⟨pc, .wr (EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
      (b32 16777730).toBytes⟩ := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  obtain ⟨v, hv, he2⟩ := ProA.shape_st8 (fired_pro hF) hs
  rw [storeValue_b32] at hv
  cases hv
  exact ⟨_, he2⟩

/-- **The event at the table store's state** is the write of the table `0x03030303` at
`sharedBase + 213336` of the thread's CTA. -/
theorem stTab_event (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g j : Nat} {e : Event} {d : Epi.D}
    (hg : g < L.threads) (he : X.get (g, j) = some e)
    (hσ : St Q L X g j = some (some (.d (.epi d)))) (hs : d.site = .stTab) :
    ∃ pc, e = ⟨pc, .wr (EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
      (b32 50529027).toBytes⟩ := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState, hs])
  obtain ⟨v, hv, he2⟩ := Epi.shape_stTab (fired_epi hF) hs
  rw [storeValue_b32] at hv
  cases hv
  exact ⟨_, he2⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
