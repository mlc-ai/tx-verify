-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Select
public import Kernels.InklingRelDecode.Proof.Thread.EvDAll
public import Kernels.InklingRelDecode.Proof.Thread.EvSAll
public import Kernels.InklingRelDecode.Proof.Thread.EvWAll
public import Kernels.InklingRelDecode.Proof2.Lib.EpiMeans

@[expose] public section

/-!
# What the default-partition states mean along every run

The default-partition machine `DComp.code` carries, in its abstract states, the numbers the
prologue computed (`Sm.D.e`) and the registers the epilogue stores with (`Epi.D.pr`). Along every
run of the machine these keep the meaning the launch gives them: `DReach Q L g s` says it for the
state `s`, `reach_next` that the machine's successor keeps it, and `DReach_after` that it holds
at every state the machine reaches from its first state.

* the common start's Tensor Memory word is a 32-bit number;
* the prologue's inherited registers are the common start's (`DStart.inh`);
* the softmax region's entry numbers mean what `Sm.EntMeans` says for the thread's request, split
  and KV head, and its `num_tokens`, `OPart` and `LsePart` bases are the launch's;
* the epilogue's registers mean what `Epi.Means` says.

`Sm.next` keeps `D.e` and `Epi.next` keeps `D.pr` (`sm_next_e`, `epi_next_pr`); the loop's exit
hands the bridge the numbers `exitIn` reads off the softmax state, which `exitIn_means` shows to be
`Epi.Means` of the epilogue's registers.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-! ### The numbers a state carries -/

/-- **What a default-partition state's numbers mean.** -/
def DReach (Q : Params) (L : Launch) (g : Nat) : DComp.St → Prop
  | .dstart _ => True
  | .pro d => ∃ tm, tm < 2 ^ 32 ∧ d.dt.pro = DStart.inh L g Q tm
  | .sm d => SmMeans Q L g d.e
  | .epi d => Epi.Means Q L g d.pr

/-! ### The softmax region and the epilogue keep their numbers -/

theorem afterSetup_e {d d' : Sm.D} (h : Sm.afterSetup L g d = some (some d')) : d'.e = d.e := by
  unfold Sm.afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; rfl)

theorem toBar20_e {d d' : Sm.D} (h : Sm.toBar20 d = some (some d')) : d'.e = d.e := by
  unfold Sm.toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

/-- **The softmax region's successor keeps the entry numbers.** -/
theorem sm_next_e {d d' : Sm.D} {e : Event} (h : Sm.next L g d e = some (some d')) :
    d'.e = d.e := by
  unfold Sm.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (have := afterSetup_e h; exact this)
    | (have := toBar20_e h; exact this)

/-- **The epilogue's successor keeps its registers**; the broadcast records the lane bits. -/
theorem epi_next_pr {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d')) :
    d'.pr = { d.pr with bw := d'.pr.bw } :=
  Epi.next_pr h

/-! ### The bridge's numbers -/

/-! ### The invariant along the machine -/

/-- **The default-partition machine keeps `DReach`**: under `Pre`, for a launched thread of the
default partition. -/
theorem reach_next (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : IsDefault L g)
    {s s' : DComp.St} {e : Event}
    (h : DReach Q L g s) (hn : DComp.next L g Q s e = some (some s')) : DReach Q L g s' := by
  cases s with
  | dstart d =>
    change DComp.dstartNext L g Q d _ = _ at hn
    unfold DComp.dstartNext at hn
    obtain ⟨d', -, hs⟩ := map_map_eq_some_some hn
    split at hs
    · subst hs
      exact ⟨ProA.shW d'.w, ProA.shW_lt _, rfl⟩
    · subst hs
      trivial
  | pro d =>
    obtain ⟨tm, htm, hpro⟩ := h
    change DComp.proNext L g Q d _ = _ at hn
    unfold DComp.proNext at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        have ha : ProA.ArgsOk L g d.dt.pro := by
          rw [hpro]
          exact DStart.argsOk_inh hpre hg hw tm
        obtain ⟨-, -, hntok, -, hrd75, hrd76⟩ := SmEntry.entOf_params hpre ha
        exact ⟨Sm.entOf_means hpre ha, hntok, hrd75, hrd76⟩
      · cases hn
    · obtain ⟨d', hd', hs⟩ := map_map_eq_some_some hn
      subst hs
      exact ⟨tm, htm, (DComp.next_pro hd').trans hpro⟩
  | sm d =>
    change DComp.smNext L g d _ = _ at hn
    unfold DComp.smNext at hn
    split at hn
    · unfold DComp.exitNext at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        show Epi.Means Q L g (if _ then _ else _ : Epi.D).pr
        split <;> exact exitIn_means hpre hg h
      · cases hn
    · obtain ⟨d', hd', hs⟩ := map_map_eq_some_some hn
      subst hs
      show SmMeans Q L g d'.e
      rw [sm_next_e hd']
      exact h
  | epi d =>
    change (Epi.next d _).map (Option.map DComp.St.epi) = _ at hn
    obtain ⟨d', hd', hs⟩ := map_map_eq_some_some hn
    subst hs
    show Epi.Means Q L g d'.pr
    rw [epi_next_pr hd']
    exact h.bw _

/-! ### Along an execution -/

/-- **What a state of a thread's machine means**: for a default-partition state, that the thread
is of the default partition and `DReach`; for a worker state, that the inherited registers hold
the launch's parameter words and the map pointer (`EvW.ProMeans`). -/
def TReach (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .d s => IsDefault L g ∧ DReach Q L g s
  | .w s => EvW.ProMeans Q (EvW.stPro s)

/-- **The thread machine keeps `TReach`.** -/
theorem treach_next (hpre : Pre Q L mem0) (hg : g < L.threads) {s s' : TSt} {e : Event}
    (h : TReach Q L g s) (hn : TSt.next L g Q s e = some (some s')) : TReach Q L g s' := by
  cases s with
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some hn
    exact ⟨h.1, reach_next hpre hg h.1 h.2 ha⟩
  | w s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some hn
    exact EvW.ProMeans.keep h (EvW.next_keep ha)

/-- **Every state the thread's machine is in has its meaning**, along any list of events. -/
theorem treach_after (hpre : Pre Q L mem0) (hg : g < L.threads) {es : List Event} {s : TSt}
    (h : (threadCode L g Q).toMachine.after (threadCode L g Q).toMachine.init es =
      some (some s)) : TReach Q L g s := by
  have key := Machine.after_induction (M := (threadCode L g Q).toMachine)
    (σ0 := (threadCode L g Q).toMachine.init)
    (fun τ _ => ∀ s, τ = some s → TReach Q L g s)
    (by
      intro s hs
      have := Option.some.inj hs
      subst this
      by_cases hd : g % L.block < 128
      · show TReach Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init)
        simp only [hd, ↓reduceIte]
        exact ⟨hd, trivial⟩
      · show TReach Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init)
        simp only [hd, ↓reduceIte]
        exact EvW.init_means (L := L) (g := g))
    (by
      intro τ es' e τ' ih hn s hs
      subst hs
      cases τ with
      | none => cases hn
      | some σ0 => exact treach_next hpre hg (ih σ0 rfl) hn)
    es (some s) h s rfl
  exact key

/-- **The meaning of the state before an event of a thread of an execution.** -/
theorem treach_stateAt (hpre : Pre Q L mem0) (hg : g < L.threads) {X : Execution} {k : Nat}
    {s : TSt} (h : Frame.stateAt (code L Q) X g k = some (some s)) : TReach Q L g s :=
  treach_after hpre hg h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
