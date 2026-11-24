-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWLoader
public import Kernels.InklingRelDecode.Proof.Thread.EvWMma

@[expose] public section

/-!
# The event shapes on the states of the worker thread machine

`EvWLoader` and `EvWMma` state the shape of the event of a loader state and of an MMA state
(`Loader.D`, `Mma.D`). The states of the composed machine `WComp.code` are `WSt.loader d P` and
`WSt.mma d P`. The theorems of this file say the same of the machine: an event that fires at one
of these states (`Machine.Fired`) has the shape of the state's own role.

* `loader_shape`: for a state `.loader d P` whose inherited registers `P` hold the pointer to the
  tensor-map parameter in the register the copies read (`MapReg`, the one fact of `Pre` the
  worker's start establishes and no site changes, `mapReg_after`), `LdShape Q L g d e`;
* `mma_shape`: for a state `.mma d P` of a thread of the launch, `MmShape L g d e`.

The fact `MapReg` is not part of the machine's invariant (`WComp.Inv`), so `loader_shape` takes it
as a premise of the state; `after_mapReg` proves that every state the machine reaches from its
first state has it, so that the layers above can discharge it from a trace.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro Pro.val Pro.table)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0} {t u : TState} {e : Event}

/-- The pointer the inherited registers hold in the register the K/V copies read. -/
def proMapPtr (P : Pro) : Value := P.rest 1949

/-- The inherited registers hold the pointer to the tensor-map parameter `param_1` in the register
the K/V copies read (`%rd` of the map operand). -/
def MapReg (P : Pro) : Prop := proMapPtr P = .ptr 64 true (.param (param "1")) 0

/-- The inherited registers of a state of the worker machine. -/
def stPro : WComp.WSt → Pro
  | .worker w => w.P
  | .idle d => d.P
  | .loader _ P => P
  | .mma _ P => P
  | .exit x => x.P

/-- The words and the map register of the inherited registers `P`, kept by `P'`. -/
def Keep (P P' : Pro) : Prop :=
  P'.w67 = P.w67 ∧ P'.w68 = P.w68 ∧ P'.w69 = P.w69 ∧ P'.w70 = P.w70 ∧ P'.w71 = P.w71 ∧
    P'.bt = P.bt ∧ proMapPtr P' = proMapPtr P

theorem Keep.refl (P : Pro) : Keep P P := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The round marker changes none of the kept words. -/
theorem bump_keep (P : Pro) : Keep P (Worker.bumpPro P) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [proMapPtr, Worker.bumpPro, Function.update_of_ne (show (1949 : Nat) ≠ Worker.roundReg by
    decide)]

/-- **A loader state's event, for every counter.** An event that fires at the loader state `d`
(of the thread with inherited registers `P`) is `LdShapeW` of `d`. -/
theorem loader_shapeW (hpre : Pre Q L mem0) {d : Loader.D} {P : Pro} (hmap : MapReg P)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) :
    LdShapeW Q L g d e := by
  obtain ⟨t, hgood, hfire⟩ := hF
  obtain ⟨hat, hinv⟩ := hgood
  have hinv' : (WComp.code L g Q).inv (.loader d P) := hinv
  obtain ⟨ins, hc, -, -⟩ := (WComp.stepAt hpre (.loader d P)).site hinv'
  have hc' : kernel.code[d.site.pc]? = some ins := hc
  have hat' : Loader.AtS L g d t := hat
  have hf : Fires d.site.pc (eventTmpl Loader.asms L g t ins.op) e (some u) := by
    have hpc : t.pc = d.site.pc := hat.1
    have := hfire
    simp only [Code.toMachine, Code.tmpl, hpc] at this
    have hc'' : kernel.code[WComp.pc (WComp.WSt.loader d P)]? = some ins := hc'
    rw [hc''] at this
    exact this
  have hpro : ldMapPtr d = .ptr 64 true (.param (param "1")) 0 := by
    unfold ldMapPtr
    rw [hinv.2.1 1949 (by decide) (by decide)]
    have h1 : Pro.val L g P 1949 = P.rest 1949 := by
      simp [Pro.val, Pro.table, PTX.Flow.lookupLit]
    rw [h1]
    exact hmap
  exact ld_shapeW (P := P) hpre hpro hat' hinv.1 hc' hf

/-- **A loader state's event.** An event that fires at the loader state `d` (of the thread with
inherited registers `P`) is `LdShape` of `d`, when the state has the counter bounds (`Loader.Rng`,
which a consistent execution gives: `Interface.LdRng`). -/
theorem loader_shape (hpre : Pre Q L mem0) {d : Loader.D} {P : Pro} (hmap : MapReg P)
    (hrg : Loader.Rng d)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) :
    LdShape Q L g d e :=
  (loader_shapeW hpre hmap hF).shape (sbOk_of_pre hpre) hrg.bndI

/-- **An MMA state's event.** An event that fires at the MMA state `d` of a thread of the launch is
`MmShape` of `d`. -/
theorem mma_shape (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) :
    MmShape L g d e := by
  obtain ⟨t, hgood, hfire⟩ := hF
  obtain ⟨hat, hinv⟩ := hgood
  have hinv' : (WComp.code L g Q).inv (.mma d P) := hinv
  obtain ⟨ins, hc, -, -⟩ := (WComp.stepAt hpre (.mma d P)).site hinv'
  have hc' : kernel.code[d.site.pc]? = some ins := hc
  have hat' : At t d.site.pc (Mma.facts L d) := hat
  have hf : Fires d.site.pc (eventTmpl Loader.asms L g t ins.op) e (some u) := by
    have hpc : t.pc = d.site.pc := hat.1
    have := hfire
    simp only [Code.toMachine, Code.tmpl, hpc] at this
    have hc'' : kernel.code[WComp.pc (WComp.WSt.mma d P)]? = some ins := hc'
    rw [hc''] at this
    exact this
  exact mm_shape hpre hg hinv.1 hinv.2.2.2.2.1 hat' hc' hf

/-! ### Every reachable state has `MapReg` -/

theorem handoff_keep (P : Pro) : Keep P (Worker.handoff L g P) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [proMapPtr, Worker.handoff, Worker.valueOf, Worker.own, Pro.val, Pro.table,
    PTX.Flow.lookupLit]

/-- The worker's own successors keep the inherited words and map register (the load of the Tensor
Memory word writes `%r2`, which is another register). -/
theorem worker_next_keep {w w' : Worker.D} (h : Worker.next L g w e = some (some w')) :
    Keep w.P w'.P := by
  obtain ⟨s, P⟩ := w
  cases s <;> simp only [Worker.next] at h
  case ld0 =>
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        simp [proMapPtr, Worker.setTm]
      · cases h
    · cases h
  case shfl =>
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact Keep.refl _
        · cases h
      · simp only [Option.some.injEq] at h
        cases h
    · cases h
  case ldRole =>
    split at h
    · exact (WComp.dispatch_some h).1 ▸ Keep.refl _
    · cases h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; exact Keep.refl _)
    | cases h

theorem ldRole_next {P : Pro} {d' : Worker.D}
    (hd : Worker.next L g ⟨.ldRole, P⟩ e = some (some d')) :
    d'.P = P ∧ (d'.site = .toLoader ∨ d'.site = .toMma ∨ d'.site = .toIdle ∨
      d'.site = .toExit ∨ d'.site = .bad0) := by
  simp only [Worker.next] at hd
  split at hd
  · exact WComp.dispatch_some hd
  · cases hd

/-- The dispatch enters a role with the inherited words and map register unchanged. -/
theorem dispatch_keep {P : Pro} {σ' : WComp.WSt} (h : WComp.dispatch L g P e = some (some σ')) :
    Keep P (stPro σ') := by
  unfold WComp.dispatch at h
  split at h
  · rename_i d' hd
    rcases (ldRole_next hd).2 with hs | hs | hs | hs | hs <;> rw [hs] at h <;>
      simp only [WComp.roleStart] at h
    · simp only [Option.some.injEq] at h
      subst h
      exact handoff_keep P
    · split at h
      · split_ifs at h
        · simp only [Option.some.injEq] at h
          subst h
          exact handoff_keep P
        · cases h
      · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact Keep.refl _
    · simp only [Option.some.injEq] at h
      subst h
      exact Keep.refl _
    · simp only [Option.some.injEq] at h
      subst h
      exact Keep.refl _
  · cases h
  · cases h

theorem map_map_some {α β : Type} {x : Option (Option α)} {f : α → β} {y : β}
    (h : x.map (Option.map f) = some (some y)) : ∃ a, x = some (some a) ∧ f a = y := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a =>
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨a, rfl, h⟩

theorem next_worker_map {w : Worker.D} (hs : w.site ≠ .ldRole) :
    WComp.next L g (.worker w) e = (Worker.next L g w e).map (Option.map WComp.WSt.worker) := by
  obtain ⟨s, P⟩ := w
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_idle_map {d : Worker.Idle.D} (hs : d.site ≠ .inc) :
    WComp.next L g (.idle d) e = (Worker.Idle.next d e).map (Option.map WComp.WSt.idle) := by
  obtain ⟨s, P⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_loader_map {d : Loader.D} (P : Pro) (hs : d.site ≠ .setMaxInc) :
    WComp.next L g (.loader d P) e =
      (Loader.next L g d e).map (Option.map (fun d' => WComp.WSt.loader d' P)) := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_mma_map {d : Mma.D} (P : Pro) (hs : d.site ≠ .setMaxRegInc) :
    WComp.next L g (.mma d P) e =
      (Mma.next L g d e).map (Option.map (fun d' => WComp.WSt.mma d' P)) := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

/-- **A successor keeps the inherited words and map register.** -/
theorem next_keep {σ σ' : WComp.WSt} (h : WComp.next L g σ e = some (some σ')) :
    Keep (stPro σ) (stPro σ') := by
  cases σ with
  | worker w =>
    by_cases hs : w.site = .ldRole
    · obtain ⟨s, P⟩ := w
      simp only at hs
      subst hs
      exact dispatch_keep h
    · rw [next_worker_map hs] at h
      obtain ⟨a, ha, rfl⟩ := map_map_some h
      exact worker_next_keep ha
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some σ') := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact bump_keep _
    · rw [next_idle_map hs] at h
      obtain ⟨a, ha, rfl⟩ := map_map_some h
      obtain ⟨s, P⟩ := d
      cases s <;> first
        | exact absurd rfl hs
        | (simp only [Worker.Idle.next, Option.some.injEq] at ha
           subst ha
           exact Keep.refl _)
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some σ') := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact bump_keep _
    · rw [next_loader_map P hs] at h
      obtain ⟨a, ha, rfl⟩ := map_map_some h
      exact Keep.refl _
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some σ') := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact bump_keep _
    · rw [next_mma_map P hs] at h
      obtain ⟨a, ha, rfl⟩ := map_map_some h
      exact Keep.refl _
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s
    · have h' : some (some (WComp.WSt.exit ⟨.ret, P⟩)) = some (some σ') := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact Keep.refl _
    · cases h

/-- What the launch fixes in the inherited registers the loader reads: the parameter words the
worker's start loaded (`Worker.startPro`), modulo `2 ^ 32` as the registers hold them. -/
structure Words (Q : Params) (P : Pro) : Prop where
  w67 : P.w67 = Q.strideBt % 2 ^ 32
  w68 : P.w68 = Q.pageRows % 2 ^ 32
  w69 : P.w69 = Q.headRows % 2 ^ 32
  w70 : P.w70 = Q.headCols % 2 ^ 32
  w71 : P.w71 = Q.splits % 2 ^ 32
  bt : P.bt = Q.btBase

/-- The inherited registers of a thread of the launch with parameters `Q`: the words and the map
register. -/
def ProMeans (Q : Params) (P : Pro) : Prop := Words Q P ∧ MapReg P

theorem ProMeans.keep {Q : Params} {P P' : Pro} (h : ProMeans Q P) (hk : Keep P P') :
    ProMeans Q P' := by
  obtain ⟨⟨a, b, c, d, f, g⟩, hm⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hk
  exact ⟨⟨k1.trans a, k2.trans b, k3.trans c, k4.trans d, k5.trans f, k6.trans g⟩,
    k7.trans hm⟩

/-- The machine's first state has `ProMeans`. -/
theorem init_means : ProMeans Q (stPro (WComp.code L g Q).init) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by
    show MapReg (Worker.startPro Q)
    simp [MapReg, proMapPtr, Worker.startPro]⟩

/-- **Every state the machine reaches from its first state has `ProMeans`**: the inherited
registers of every reachable state (and so of every state `.loader d P`) hold the launch's
parameter words and the pointer to the tensor-map parameter that the K/V copies read. -/
theorem after_means {es : List Event} {σ : WComp.WSt}
    (h : (WComp.code L g Q).toMachine.after (WComp.code L g Q).toMachine.init es =
      some (some σ)) : ProMeans Q (stPro σ) := by
  have key := Machine.after_induction (M := (WComp.code L g Q).toMachine)
    (σ0 := (WComp.code L g Q).toMachine.init)
    (fun τ _ => ∀ σ, τ = some σ → ProMeans Q (stPro σ))
    (by
      intro σ hσ
      have := Option.some.inj hσ
      subst this
      exact init_means)
    (by
      intro τ es' e τ' ih hn σ hσ
      subst hσ
      cases τ with
      | none => cases hn
      | some σ0 =>
        have hn' : WComp.next L g σ0 e = some (some σ) := hn
        exact (ih σ0 rfl).keep (next_keep hn'))
    es (some σ) h σ rfl
  exact key

theorem after_mapReg {es : List Event} {σ : WComp.WSt}
    (h : (WComp.code L g Q).toMachine.after (WComp.code L g Q).toMachine.init es =
      some (some σ)) : MapReg (stPro σ) :=
  (after_means h).2

end
end PTX.Kernels.InklingRelDecode.Proof.EvW
