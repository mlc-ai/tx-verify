-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueRun
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCountsStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStage
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreCounts
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.InitFacts
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaFullCommit
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Kernel.Frame
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Where a thread's events come from

A run invariant of the thread's machine (`RunInv`: it holds at the first state and every
continuing event keeps it) holds at the state before each event of a thread (`RunInv.holds`, by
`Code.run_inv_live` along the thread's trace). In an execution whose threads the machine follows
(`Frame.Tracked`), every event other than undefined behaviour is fired from such a state, at
its site's instruction, with the state's facts and invariant (`event_origin`). A layer above
that needs a role's run invariant at the role's events instantiates `event_origin` with an
invariant that is the role's on the role's states.

`roleJ` is that invariant for the loader, the MMA warp, the store warp, the softmax warps and
the correction warps (`roleJ_run`):
the prologue's events are of the prologue's kinds, which leaves each role's counts at zero at
its entry (`Loader.Counts.init`, `Mma.counts_init`, `Correction.counts_start`), and the roles'
steps keep them (`counts_step`). Every Tensor Core commit is an instruction of the MMA warp
(`kernel_commit_pcs`, and no other role's site is at a commit), so in a followed execution it
comes from an MMA state of a thread of warp 12 with the role's run invariant (`mma_commitRun`,
the premise `Mma.CommitRun`). No role site is a barrier initialization (`Role.noInitSite`): each
site's position is outside the initializations' (`kernel_init_pcs`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `J` is a run invariant of thread `g`'s machine: it holds at the first state and every
continuing event keeps it. -/
structure RunInv (L : Launch) (g : Nat) (J : ThreadD → List Event → Prop) : Prop where
  init : J (code L g).init []
  step : ∀ {d d' : ThreadD} {pre : List Event} {e : Event} {t u : TState} {ins : Instr},
    J d pre → (code L g).AtD d t → (code L g).inv d →
    kernel.code[(code L g).pc d]? = some ins →
    Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e (some u) →
    (code L g).next d e = some (some d') → J d' (pre ++ [e])

/-- A run invariant holds at the state before each event of a thread. -/
theorem RunInv.holds (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g k : Nat}
    (hg : g < L.threads) {J : ThreadD → List Event → Prop} (hJ : RunInv L g J) {d : ThreadD}
    (hk : k < (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    J d ((X.tr g).take k) :=
  Code.run_inv_live (sound hpre hg)
    (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) J hJ.init hJ.step k hk d hσ

/-- **The origin of an event**: in an execution whose threads the machine follows, an event
other than undefined behaviour is fired from the state before it, at its site's instruction,
with the state's facts, its invariant and every run invariant. -/
theorem event_origin (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {J : Nat → ThreadD → List Event → Prop}
    (hJ : ∀ g < L.threads, RunInv L g (J g)) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ d t ins o, Frame.stateAt (code L) X g k = some (some d) ∧ J g d ((X.tr g).take k) ∧
      (code L g).AtD d t ∧ (code L g).inv d ∧ kernel.code[(code L g).pc d]? = some ins ∧
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e o := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he hub
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hC hX he hσ
  exact ⟨d, t, ins, o, hσ, RunInv.holds hpre hX hg (hJ g hg) hk hσ, hat, hi, hc, hf⟩

/-! ### The roles' run invariants -/

/-- The prologue's events leave every count of the roles at zero. -/
theorem Prologue.ProKind.quiet {e : Event} (h : Prologue.ProKind e.kind) :
    (∀ m, okPoll m e = false ∧ arrivesOn m e = false ∧ commitsTo m e = false ∧
      issuesTo m e = false) ∧ Mma.isMma e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [Prologue.ProKind] at h <;>
    simp [okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, commitsTo, issuesTo, Mma.isMma]

/-- The correction role's counted events are not the prologue's. -/
theorem Prologue.ProKind.corrQuiet {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind)
    (L : Launch) (g : Nat) : Correction.Quiet L g es := by
  have hz : ∀ p : Event → Bool, (∀ x, Prologue.ProKind x.kind → p x = false) →
      es.countP p = 0 := fun p hp => List.countP_eq_zero.mpr fun x hx => by simp [hp x (h x hx)]
  have hk : ∀ x : Event, Prologue.ProKind x.kind → ∀ m, okPoll m x = false ∧
      arrivesOn m x = false := fun x hx m =>
    ⟨((ProKind.quiet hx).1 m).1, ((ProKind.quiet hx).1 m).2.1⟩
  have hb : ∀ x : Event, Prologue.ProKind x.kind → ∀ id c md, barIs id c md x = false := by
    rintro ⟨pc, k⟩ hx id c md
    cases k <;> simp only [Prologue.ProKind] at hx <;> simp [barIs]
  have ht : ∀ x : Event, Prologue.ProKind x.kind → ∀ lo hi pc, tcLdAt lo hi x = false ∧
      tcStAt lo hi x = false ∧ isWaitSt x = false ∧ Correction.nzVote pc x = false ∧
      Correction.isVoteAt pc x = false := by
    rintro ⟨pc, k⟩ hx lo hi pc'
    cases k <;> simp only [Prologue.ProKind] at hx <;>
      simp [tcLdAt, tcStAt, isWaitSt, Correction.nzVote, Correction.isVoteAt]
  have hv : ∀ x : Event, Prologue.ProKind x.kind → Correction.isVote x = false ∧
      isNzVote x = false ∧ isTcColl x = false := by
    rintro ⟨pc, k⟩ hx
    cases k <;> simp only [Prologue.ProKind] at hx <;>
      simp_all [Correction.isVote, isNzVote, isTcColl]
  exact ⟨fun _ _ => hz _ fun x hx => hb x hx _ _ _,
    fun _ _ => hz _ fun x hx => (hk x hx _).2, fun _ _ => hz _ fun x hx => (hk x hx _).2,
    fun _ _ => hz _ fun x hx => (hk x hx _).1, fun _ _ => hz _ fun x hx => (hk x hx _).1,
    fun _ _ => hz _ fun x hx => (hk x hx _).2,
    ⟨hz _ fun x hx => hb x hx _ _ _, hz _ fun x hx => hb x hx _ _ _⟩,
    fun _ _ => hz _ fun x hx => (ht x hx _ _ 0).1,
    fun _ _ => hz _ fun x hx => (ht x hx _ _ 0).2.1,
    hz _ fun x hx => (ht x hx 0 0 0).2.2.1,
    fun _ _ => hz _ fun x hx => (ht x hx 0 0 _).2.2.2.1,
    fun _ _ => hz _ fun x hx => (ht x hx 0 0 _).2.2.2.2, hz _ fun x hx => (hv x hx).1,
    hz _ fun x hx => (hv x hx).2.1, hz _ fun x hx => (hv x hx).2.2⟩

/-- The store warp's counted events are not the prologue's. -/
theorem Prologue.ProKind.storeQuiet {e : Event} (h : Prologue.ProKind e.kind) :
    Store.isStore e = false ∧ Store.isCommit e = false ∧ Store.isBulkWait e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [Prologue.ProKind] at h <;>
    simp [Store.isStore, Store.isCommit, Store.isBulkWait]

/-- The softmax warps' counted events are not the prologue's. -/
theorem Prologue.ProKind.softQuiet {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind)
    (L : Launch) (g : Nat) : Softmax.Quiet L g es := by
  have hz : ∀ p : Event → Bool, (∀ x, Prologue.ProKind x.kind → p x = false) →
      es.countP p = 0 := fun p hp => List.countP_eq_zero.mpr fun x hx => by simp [hp x (h x hx)]
  have hk : ∀ x : Event, Prologue.ProKind x.kind → ∀ m, okPoll m x = false ∧
      arrivesOn m x = false := fun x hx m =>
    ⟨((ProKind.quiet hx).1 m).1, ((ProKind.quiet hx).1 m).2.1⟩
  have hb : ∀ x : Event, Prologue.ProKind x.kind → ∀ id c md, barIs id c md x = false := by
    rintro ⟨pc, k⟩ hx id c md
    cases k <;> simp only [Prologue.ProKind] at hx <;> simp [barIs]
  have ht : ∀ x : Event, Prologue.ProKind x.kind → ∀ lo hi l, tcLdAt lo hi x = false ∧
      tcStAt lo hi x = false ∧ isWaitSt x = false ∧ writeAt l x = false := by
    rintro ⟨pc, k⟩ hx lo hi l
    cases k <;> simp only [Prologue.ProKind] at hx <;>
      simp [tcLdAt, tcStAt, isWaitSt, writeAt]
  have hw : ∀ x : Event, Prologue.ProKind x.kind → Execution.isWarpBar x = false := by
    rintro ⟨pc, k⟩ hx
    cases k <;> simp only [Prologue.ProKind] at hx <;> simp [Execution.isWarpBar]
  have hc : ∀ x : Event, Prologue.ProKind x.kind → isTcColl x = false := by
    rintro ⟨pc, k⟩ hx
    cases k <;> simp only [Prologue.ProKind] at hx <;> simp [isTcColl]
  have hp : ∀ x : Event, Prologue.ProKind x.kind → ∀ pc, okPollAt pc x = false := by
    rintro ⟨pc', k⟩ hx pc
    cases k <;> simp only [Prologue.ProKind] at hx <;> simp [okPollAt]
  exact ⟨hz _ fun x hx => (hk x hx _).1, hz _ fun x hx => (hk x hx _).1,
    hz _ fun x hx => (hk x hx _).2, hz _ fun x hx => (hk x hx _).2,
    hz _ fun x hx => hb x hx _ _ _,
    ⟨hz _ fun x hx => hb x hx _ _ _, hz _ fun x hx => hb x hx _ _ _⟩,
    hz _ fun x hx => (ht x hx _ _ (Softmax.statsWord L g)).1,
    hz _ fun x hx => (ht x hx _ _ (Softmax.statsWord L g)).2.1,
    hz _ fun x hx => (ht x hx 0 0 (Softmax.statsWord L g)).2.2.1,
    hz _ fun x hx => (ht x hx 0 0 (Softmax.statsWord L g)).2.2.2, hz _ fun x hx => hw x hx,
    hz _ fun x hx => hc x hx, fun pc => hz _ fun x hx => hp x hx pc⟩

/-- The roles' run invariants on the thread's states: the prologue's event kinds and its
elections (for a warp other than 0, then for warp 0), then the loader's, the MMA warp's, the
store warp's, the softmax warps' or the correction warps' counts. -/
def roleJ (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl p, es => (∀ x ∈ es, Prologue.ProKind x.kind) ∧
      (warpOf L g ≠ 0 → es.countP (Prologue.isElect ·.kind) = p.site.elects (warpOf L g)) ∧
      (warpOf L g = 0 → es.countP (Prologue.isElect ·.kind) = p.site.elects0)
  | .inr (.loader d), es => Loader.Counts L g d es
  | .inr (.mma d), es => Mma.Counts L g d es
  | .inr (.store d), es => Store.Counts L g d es
  | .inr (.softmax d), es => Softmax.Counts L g d es
  | .inr (.corr d), es => Correction.Counts L g d es
  | .inr _, _ => True

/-- A role's successor in the thread's machine is its own machine's. -/
theorem next_role {α : Type} {f : α → Role} (hf : Function.Injective f) {o : Option (Option α)}
    {a : α} (h : o.map (Option.map (Sum.inr ∘ f : α → ThreadD)) = some (some (.inr (f a)))) :
    o = some (some a) := by
  rcases o with _ | _ | b
  · cases h
  · cases h
  · simp only [Option.map_some, Option.some.injEq, Function.comp, Sum.inr.injEq] at h
    rw [hf h]

/-- The election tests of the roles agree. -/
theorem mma_isElectE_eq (x : Event) : Mma.isElectE x = Prologue.isElect x.kind := by
  obtain ⟨_, k⟩ := x
  cases k <;> rfl

theorem loader_isElectE_eq (x : Event) : Loader.isElectE x = Mma.isElectE x := by
  obtain ⟨_, k⟩ := x
  cases k <;> rfl

theorem softmax_isElectE_eq (x : Event) : Softmax.isElectE x = Mma.isElectE x := by
  obtain ⟨_, k⟩ := x
  cases k <;> rfl

/-- A prologue event is no Tensor Memory resource operation and no barrier arrival. -/
theorem proKind_tmemOp {y : Event} (h : Prologue.ProKind y.kind) :
    Tmem.Pair.isTmemOp y = false := by
  obtain ⟨_, k⟩ := y
  cases k <;> simp_all [Prologue.ProKind, Tmem.Pair.isTmemOp]

theorem proKind_barId {y : Event} {id : Nat} (h : Prologue.ProKind y.kind) :
    Execution.isBarId id y = false := by
  obtain ⟨_, k⟩ := y
  cases k <;> simp_all [Prologue.ProKind, Execution.isBarId]

theorem roleJ_run (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    RunInv L g (roleJ L g) where
  init := ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ => rfl, fun _ => rfl⟩
  step := by
    intro d d' pre e t u ins hJ hat hi hc hf hn
    rcases d with p | r
    · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
      have hat' : At t p.site.pc (Prologue.facts L g p) :=
        ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
      cases hx : Prologue.next L g p e with
      | none => rw [hx] at hn; cases hn
      | some x =>
        rw [hx] at hn
        cases x with
        | none => cases hn
        | some x =>
          have hev := Prologue.event_ok hpre hat' hc hf hx
          have hk : Prologue.ProKind e.kind := hev.proKind
          have hall : ∀ y ∈ pre ++ [e], Prologue.ProKind y.kind := by
            intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hJ.1 y hy
            · rw [List.mem_singleton.mp hy]; exact hk
          have hq := fun y hy => Prologue.ProKind.quiet (hall y hy)
          cases x with
          | inl p' =>
            simp only [Option.map_some, Option.bind_some, handoff, Option.some.injEq] at hn
            subst hn
            refine ⟨hall, fun hw => ?_, fun hw => ?_⟩
            · rw [List.countP_append, hJ.2.1 hw, Prologue.elects_step hw hi hev hx]
              simp
            · rw [List.countP_append, hJ.2.2 hw, Prologue.elects0_step hw hi hev hx]
              simp
          | inr k =>
            simp only [Option.map_some, Option.bind_some, handoff] at hn
            have hsk := Prologue.next_inr hx
            have hel : ∀ w, warpOf L g = w → w ≠ 0 →
                (pre ++ [e]).countP Mma.isElectE = Prologue.Site.elects w .clWait := by
              intro w hw hw0
              subst hw
              have he' : Mma.isElectE e = false := by
                rw [hsk.1] at hev
                obtain ⟨op, hop⟩ := hev
                simp [Mma.isElectE, hop]
              rw [List.countP_append, ← hsk.1, ← hJ.2.1 hw0, List.countP_singleton, he']
              simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
              exact List.countP_congr fun x _ => by rw [mma_isElectE_eq]
            have hel0 : warpOf L g = 0 → (pre ++ [e]).countP Mma.isElectE = 14 := by
              intro hw0
              have he' : Mma.isElectE e = false := by
                rw [hsk.1] at hev
                obtain ⟨op, hop⟩ := hev
                simp [Mma.isElectE, hop]
              rw [List.countP_append, List.countP_singleton, he',
                show (14 : Nat) = Prologue.Site.clWait.elects0 from rfl, ← hsk.1, ← hJ.2.2 hw0]
              simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
              exact List.countP_congr fun x _ => by rw [mma_isElectE_eq]
            cases k <;> simp only [Role.start, Option.map_some,
              Option.some.injEq] at hn <;> subst hn
            · have hw14 : warpOf L g = 14 := by
                have h := hsk.2
                unfold RoleKind.ofWarp at h
                split_ifs at h
                assumption
              refine Loader.Counts.init (fun y hy m =>
                ⟨((hq y hy).1 m).1, ((hq y hy).1 m).2.1, ((hq y hy).1 m).2.2.2⟩) ?_
              rw [show (pre ++ [e]).countP Loader.isElectE = (pre ++ [e]).countP Mma.isElectE from
                List.countP_congr fun x _ => by rw [loader_isElectE_eq], hel 14 hw14 (by decide)]
              rfl
            · have hw12 : warpOf L g = 12 := by
                have h := hsk.2
                unfold RoleKind.ofWarp at h
                split_ifs at h
                assumption
              exact Mma.counts_init _ _
                (fun m => List.countP_eq_zero.mpr fun y hy => by simp [((hq y hy).1 m).1])
                (fun m => List.countP_eq_zero.mpr fun y hy => by simp [((hq y hy).1 m).2.1])
                (fun m => List.countP_eq_zero.mpr fun y hy => by simp [((hq y hy).1 m).2.2.1])
                (List.countP_eq_zero.mpr fun y hy => by simp [(hq y hy).2])
                (List.countP_eq_zero.mpr fun y hy => by simp [proKind_tmemOp (hall y hy)])
                (List.countP_eq_zero.mpr fun y hy => by simp [proKind_barId (hall y hy)])
                (by rw [hel 12 hw12 (by decide)]; rfl)
            · exact Store.Counts.init fun y hy m =>
                ⟨((hq y hy).1 m).1, ((hq y hy).1 m).2.1,
                  (Prologue.ProKind.storeQuiet (hall y hy)).1,
                  (Prologue.ProKind.storeQuiet (hall y hy)).2.1,
                  (Prologue.ProKind.storeQuiet (hall y hy)).2.2⟩
            · have hw8 : warpOf L g < 8 := by
                have h := hsk.2
                unfold RoleKind.ofWarp at h
                split_ifs at h
                assumption
              refine Softmax.counts_start (Prologue.ProKind.softQuiet hall L g) ?_
              rw [show (pre ++ [e]).countP Softmax.isElectE = (pre ++ [e]).countP Mma.isElectE
                from List.countP_congr fun x _ => by rw [softmax_isElectE_eq]]
              by_cases hw0 : warpOf L g = 0
              · simp [hel0 hw0, hw0]
              · have hw12 : warpOf L g ≠ 12 := by omega
                simp [hel _ rfl hw0, hw0, Prologue.Site.elects, hw12]
            · exact Correction.counts_start (Prologue.ProKind.corrQuiet hall L g)
            · trivial
    · obtain ⟨r', rfl, hk⟩ := code_next_inr hn
      cases r with
      | loader l =>
        cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
        rename_i l'
        exact Loader.counts_step hpre hg hJ hi ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1,
          hat.2.2.2.2⟩ hc hf (next_role (fun _ _ h => Role.loader.inj h) hn)
      | mma m =>
        cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
        exact Mma.counts_step hpre hg hJ hat hi.1 hc hf
          (next_role (fun _ _ h => Role.mma.inj h) hn)
      | corr c =>
        cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
        have hT : 1 ≤ Correction.trips L := by
          have := skOf_eq hpre; have := hpre.skPos
          unfold Correction.trips; omega
        exact Correction.counts_step hT hi (Correction.site_event hpre hg hi hat hc hf)
          (Correction.site_wr hpre hat hc hf) (Correction.site_vote hpre hi hat hc hf)
          (next_role (fun _ _ h => Role.corr.inj h) hn) hJ
      | store s =>
        cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
        exact Store.counts_step hpre hJ hi hat hc hf (next_role (fun _ _ h => Role.store.inj h) hn)
      | softmax s =>
        cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
        exact Softmax.counts_step hi (Softmax.site_event hpre hg hi hat hc hf) (fires_pc hf)
          (next_role (fun _ _ h => Role.softmax.inj h) hn) hJ
      | idle _ => cases r' <;> trivial

/-! ### Commits come from the MMA warp -/

/-- Every Tensor Core commit of the kernel is one of the MMA warp's. -/
theorem kernel_commit_pcs : OpPcsFast kernel.code commitOp Flow.tcCommit.toList = true := by
  decide +kernel

/-- Decide a fact of every site's instruction position: one goal per site, its parameters
reverted. -/
macro "site_decide" : tactic => `(tactic| (
  all_goals (try cases ‹Loader.UseK›)
  all_goals (try cases ‹Correction.Gen›)
  all_goals (repeat' (first | revert ‹Fin _› | revert ‹Bool›))
  all_goals decide))

/-- The positions of the commits and of the barrier initializations. -/
abbrev commitPcs : List Nat := Flow.tcCommit.toList
abbrev initPcs : List Nat := Flow.mbarInit.toList

theorem Prologue.site_not_commit (s : Prologue.Site) : s.pc ∉ commitPcs := by
  cases s <;> site_decide

theorem Loader.site_not (s : Loader.Site) : s.pc ∉ commitPcs ∧ s.pc ∉ initPcs := by
  cases s <;> site_decide

theorem Store.site_not (s : Store.Site) : s.pc ∉ commitPcs ∧ s.pc ∉ initPcs := by
  cases s <;> site_decide

theorem Idle.site_not (s : Idle.Site) : s.pc ∉ commitPcs ∧ s.pc ∉ initPcs := by
  cases s <;> site_decide

theorem Correction.site_not (s : Correction.Site) : s.pc ∉ commitPcs ∧ s.pc ∉ initPcs := by
  cases s <;> site_decide

theorem Softmax.site_not (s : Softmax.Site) : s.pc ∉ commitPcs ∧ s.pc ∉ initPcs := by
  cases s <;> site_decide

theorem Mma.site_not_init (s : Mma.Site) : s.pc ∉ initPcs := by
  cases s <;> site_decide

/-- **Commits come from the MMA warp** with its run invariant, in a followed execution. -/
theorem mma_commitRun (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : Mma.CommitRun L X := by
  intro g k pc sp he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hop : commitOp ins.op = true := by
    by_contra hne
    exact fires_notCommit (eventTmpl_notCommit (commitOp_ne (by simpa using hne))) hf sp rfl
  have hpc := OpPcsFast.mem kernel_commit_pcs hc hop
  have hg := Frame.lt_of_get hX he
  rcases d with p | r
  · exact absurd hpc (Prologue.site_not_commit p.site)
  cases r with
  | idle s => exact absurd hpc (Idle.site_not s.site).1
  | loader l => exact absurd hpc (Loader.site_not l.site).1
  | store s => exact absurd hpc (Store.site_not s.site).1
  | softmax s => exact absurd hpc (Softmax.site_not s.site).1
  | corr c => exact absurd hpc (Correction.site_not c.site).1
  | mma m =>
    have hw : RoleKind.Warp .mma (warpOf L g) :=
      role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k
        (.mma m) hσ
    exact ⟨hw, m, t, ins, o, hJ, hi.1, hat.2.2.2.2, hc, hf⟩

/-! ### No role initializes a barrier -/

/-- Every barrier initialization of the kernel is listed. -/
theorem kernel_init_pcs : OpPcsFast kernel.code initOp initPcs = true := by
  decide +kernel

/-- **No role site is a barrier initialization**: the sites of every role, the softmax
placeholder's included, are outside the initializations' positions. -/
theorem Role.noInitSite (L : Launch) : Role.NoInitSite L := by
  intro g r ins hc
  by_contra hop
  have hpc := OpPcsFast.mem kernel_init_pcs hc (by simpa using hop)
  cases r with
  | idle s => exact (Idle.site_not s.site).2 hpc
  | loader d => exact (Loader.site_not d.site).2 hpc
  | mma d => exact Mma.site_not_init d.site hpc
  | store d => exact (Store.site_not d.site).2 hpc
  | softmax d => exact (Softmax.site_not d.site).2 hpc
  | corr d => exact (Correction.site_not d.site).2 hpc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
