-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvEv

@[expose] public section

/-! # The prologue's initializations, elections and barrier-0 count

The prologue (`Proof2/ProA`) runs twelve elections `el j` (pc `elPc j`), each followed, in the
lane of warp 0 the election returned, by the initialization `init j` of the barrier
`Proof.ProA.initBar j` (pc `initPc j`, count 1), then the proxy fence and the partition's barrier
`bar2` (`bar.sync 0, 128`, pc 180). Read off the code (positions of the flat machine's sites):

* `next_close`, `pro_close`: a step from a site before an election or before `bar2` does not pass
  it, and a step out of an election, an initialization or `bar2` increases the position;
* `pro_el_step`: the step out of `el j` is an election, into `init j` exactly when the election
  returned the thread's lane and the thread is in warp 0; `pro_in_pred`: only `el j` steps into
  `init j`;
* `PI`, `pi_inv`: along every thread, at a prologue state the barrier-0 events before it are 2 up
  to `bar2` and at least 3 after, its initializations of barrier `j` at most one and none before
  `init j`, and after `el j` its trace has the election of `el j`, at `init j` an election that
  returned its lane in warp 0, and after `init j` (when the election returned its lane in warp 0)
  the initialization; after the prologue the same facts with at least 3 barrier-0 events. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

/-- The positions a step does not pass: the twelve elections and `bar2`. -/
def closePcs : List Nat := [130, 135, 139, 143, 147, 151, 155, 159, 163, 167, 171, 175, 180]

/-- The positions a step leaves upwards: the elections and the initializations. -/
def strictPcs : List Nat :=
  [130, 135, 139, 143, 147, 151, 155, 159, 163, 167, 171, 175,
    134, 138, 142, 146, 150, 154, 158, 162, 166, 170, 174, 178]

set_option maxHeartbeats 1000000 in
/-- **A step of the flat prologue before `bar2` passes no election and not `bar2`**, and a step
out of an election or an initialization increases the position. -/
theorem next_close {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (hs : s.pc < 180) (h : next L g ⟨s, dt⟩ e = some (some d')) :
    (∀ c ∈ closePcs, s.pc < c → d'.site.pc ≤ c) ∧ (s.pc ∈ strictPcs → s.pc < d'.site.pc) := by
  cases s
  all_goals first
    | (exfalso; revert hs; decide)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            dsimp only
            decide))

/-- **The step out of `bar2` increases the position.** -/
theorem next_bar2 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.bar2, dt⟩ e = some (some d')) : 180 < d'.site.pc := by
  simp only [next] at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    dsimp only
    split
    · decide
    · exact lt_of_lt_of_le (by decide) (qSite_pc_ge L g _ 0)

/-- `%p40`, the guard of the initializations, is the thread being in warp 0. -/
theorem v_p40_iff' {L : Launch} {g : Nat} (hb : L.block = 256) (dt : Dat) :
    v_p40 L g dt = true ↔ g % L.block < 32 := by
  have h1 : g % L.block < 256 := by rw [hb]; exact Nat.mod_lt _ (by omega)
  unfold v_p40 v_r3 pEqB32
  simp only [truncBits, PTX.compare, BitVec.toNat_ofNat, tidOf]
  simp
  omega

/-- **The step from an election site** of the flat machine: an election event, into the
initialization exactly when the election returned the thread's lane and it is in warp 0. -/
theorem el_step' {L : Launch} {g : Nat} (hb : L.block = 256) {j : Nat} (hj : j < 12) {dt : Dat}
    {e : Event} {d' : D} (h : next L g ⟨elSite j, dt⟩ e = some (some d')) :
    ∃ mk inst ld, e.kind = .elect mk inst ld ∧
      (d'.site = inSite j ↔ (laneOf L g = ld ∧ g % L.block < 32)) := by
  interval_cases j <;>
  · simp only [elSite, elSites, inSite, inSites, List.getD_cons_zero,
      List.getD_cons_succ, next] at h ⊢
    split at h
    · rename_i mk inst ld hk
      refine ⟨mk, inst, ld, hk, ?_⟩
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, v_p40_iff' hb, beq_iff_eq] at hc
        exact ⟨fun _ => ⟨hc.2, hc.1⟩, fun _ => rfl⟩
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, v_p40_iff' hb, beq_iff_eq] at hc
        constructor
        · intro h2
          cases h2
        · rintro ⟨h1, h2⟩
          exact absurd ⟨h2, h1⟩ hc
    · simp at h

/-- **The only site before the initialization `in j` is the election `el j`.** -/
theorem in_pred' {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) :
    ∀ j < 12, d'.site = inSite j → d.site = elSite j := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; (try simp only [qSite])
       (repeat' split) <;> decide)

end PTX.Kernels.InklingRelDecode.Proof.ProA

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The prologue's steps around its initializations -/

theorem el_old (j : Fin 12) : (ProA.Site.el j).old = Proof.ProA.elSite j.val := by
  fin_cases j <;> rfl

theorem in_old (j : Fin 12) : (ProA.Site.init j).old = Proof.ProA.inSite j.val := by
  fin_cases j <;> rfl

theorem ofOld_in (j : Fin 12) : ProA.Site.ofOld (Proof.ProA.inSite j.val) = .init j := by
  fin_cases j <;> rfl

theorem ofOld_el (j : Fin 12) : ProA.Site.ofOld (Proof.ProA.elSite j.val) = .el j := by
  fin_cases j <;> rfl

theorem el_pc (j : Fin 12) : (ProA.Site.el j).pc = Proof.ProA.closePcs.getD j.val 0 := by
  fin_cases j <;> rfl

theorem init_pc_lt (j : Fin 12) : (ProA.Site.el j).pc < (ProA.Site.init j).pc := by
  fin_cases j <;> decide

/-- The flat step of a prologue step away from the third request word and the last barrier. -/
theorem pro_flat {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d'))
    (h1 : d.site ≠ .bar18) (h3 : d.site ≠ .ld 2) :
    Proof.ProA.next L g d.old e = some (some (ProA.D.old d')) := by
  obtain ⟨s, dt⟩ := d
  have h2 : s ≠ .exit := by
    rintro rfl
    simp [ProA.next, ProA.next0, ProA.kill] at h
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  exact ProA.next0_flat h1 h2 h3 h'

/-- **A prologue step before `bar2` passes no election and not `bar2`**, and a step out of an
election or an initialization increases the position; the step out of `bar2` increases it. -/
theorem pro_close {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d')) :
    (d.site.pc < 180 → (∀ c ∈ Proof.ProA.closePcs, d.site.pc < c → d'.site.pc ≤ c) ∧
      (d.site.pc ∈ Proof.ProA.strictPcs → d.site.pc < d'.site.pc)) ∧
    (d.site = .bar2 → 180 < d'.site.pc) := by
  by_cases h1 : d.site = .bar18
  · refine ⟨fun hlt => ?_, fun h2 => ?_⟩
    · rw [h1] at hlt; exact absurd hlt (by decide)
    · rw [h1] at h2; cases h2
  by_cases h3 : d.site = .ld 2
  · have hk : ProA.kill d e = false ∨ ProA.kill d e = true := by cases ProA.kill d e <;> simp
    obtain ⟨s, dt⟩ := d
    simp only at h3
    subst h3
    rcases hk with hk | hk
    · have h' : ProA.next0 L g ⟨.ld 2, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
      rw [ld2_succ h']
      refine ⟨fun _ => ⟨fun c hc hlt => ?_, fun h => ?_⟩, fun h => by cases h⟩
      · dsimp only at hlt ⊢; revert hlt; revert hc; revert c; decide
      · dsimp only at h ⊢; revert h; decide
    · simp [ProA.next, hk] at h
  have hf := pro_flat h h1 h3
  have hx : d'.site ≠ .exit := fun hx => h1 (exit_from_bar18 h hx)
  have hdx : d.site ≠ .exit := by
    intro hdx
    obtain ⟨s, dt⟩ := d
    simp only at hdx
    subst hdx
    simp [ProA.next, ProA.next0, ProA.kill] at h
  have e1 := ProA.pc_old d.site hdx
  have e2 := ProA.pc_old d'.site hx
  refine ⟨fun hlt => ?_, fun hb => ?_⟩
  · have := Proof.ProA.next_close (by rw [← e1]; exact hlt) hf
    simp only [ProA.D.old] at this
    rw [e1, e2]
    exact this
  · have hb' : d.old = ⟨.bar2, d.dt⟩ := by simp [ProA.D.old, hb, ProA.Site.old]
    rw [hb'] at hf
    have := Proof.ProA.next_bar2 hf
    simp only [ProA.D.old] at this
    rw [e2]
    exact this

/-- **The step out of `el j`**: an election, into `init j` exactly when the election returned the
thread's lane and the thread is in warp 0. -/
theorem pro_el_step (hb : L.block = 256) {j : Fin 12} {d d' : ProA.D} {e : Event}
    (hs : d.site = .el j) (h : ProA.next L g d e = some (some d')) :
    ∃ mk inst ld, e.kind = .elect mk inst ld ∧
      (d'.site = .init j ↔ (laneOf L g = ld ∧ g % L.block < 32)) := by
  have hf := pro_flat h (by rw [hs]; nofun) (by rw [hs]; nofun)
  have hold : d.old = ⟨Proof.ProA.elSite j.val, d.dt⟩ := by simp [ProA.D.old, hs, el_old]
  rw [hold] at hf
  obtain ⟨mk, inst, ld, hk, hiff⟩ := Proof.ProA.el_step' hb j.isLt hf
  refine ⟨mk, inst, ld, hk, ?_⟩
  rw [← hiff]
  have hx : d'.site ≠ .exit := fun hx => by
    have := exit_from_bar18 h hx
    rw [hs] at this
    cases this
  simp only [ProA.D.old]
  constructor
  · intro h'
    rw [h', in_old]
  · intro h'
    rw [← ProA.ofOld_old _ hx, h', ofOld_in]

/-- **Only `el j` steps into `init j`.** -/
theorem pro_in_pred {j : Fin 12} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) (hs : d'.site = .init j) : d.site = .el j := by
  by_cases h1 : d.site = .bar18
  · have hx : d'.site = .exit := by
      obtain ⟨s, dt⟩ := d
      simp only at h1
      subst h1
      simp [ProA.next, ProA.next0, ProA.kill] at h
      rw [← h.2]
    rw [hx] at hs; cases hs
  by_cases h3 : d.site = .ld 2
  · obtain ⟨s, dt⟩ := d
    simp only at h3
    subst h3
    by_cases hk : ProA.kill ⟨.ld 2, dt⟩ e = true
    · simp [ProA.next, hk] at h
    · have h' : ProA.next0 L g ⟨.ld 2, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
      rw [ld2_succ h'] at hs
      cases hs
  have hf := pro_flat h h1 h3
  have hdx : d.site ≠ .exit := by
    intro hdx
    obtain ⟨s, dt⟩ := d
    simp only at hdx
    subst hdx
    simp [ProA.next, ProA.next0, ProA.kill] at h
  have := Proof.ProA.in_pred' hf j.val j.isLt (by simp [ProA.D.old, hs, in_old])
  simp only [ProA.D.old] at this
  rw [← ProA.ofOld_old _ hdx, this, ofOld_el]

/-! ### The positions of the initializations -/

def initPcs : List Nat := [134, 138, 142, 146, 150, 154, 158, 162, 166, 170, 174, 178]

theorem kernel_init_pcs : OpPcsFast kernel.code initOp initPcs = true := by decide +kernel

/-- **An initialization event is at one of twelve positions.** -/
theorem init_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {l : Loc} {c : Nat} (hk : e.kind = .mbInit l c) : pc ∈ initPcs := by
  refine OpPcsFast.mem kernel_init_pcs hc ?_
  cases hop : initOp ins.op
  · exact absurd hk (notInit_of_op hop hf l c)
  · rfl

local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_init : ∀ s : Startup.Site, s.pc ∈ initPcs → False := by
  intro s h; revert h; cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_init (s : ProA.Site) (h : s.pc ∈ initPcs) : ∃ j, s = .init j := by
  cases s with
  | init j => exact ⟨j, rfl⟩
  | ld k | el k | arr k | psh k | ldq k | st9 k =>
    exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    exfalso; revert h; revert j; revert b; decide
  | _ => exfalso; revert h; decide

theorem sm_init : ∀ s : Proof.Sm.Site, s.pc ∈ initPcs → False := by site_cls
theorem epi_init : ∀ s : Proof.Epi.Site, s.pc ∈ initPcs → False := by site_cls
theorem worker_init : ∀ s : Proof.Worker.Site, s.pc ∈ initPcs → False := by site_cls
theorem idle_init : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ initPcs → False := by site_cls
theorem loader_init : ∀ s : Proof.Loader.Site, s.pc ∈ initPcs → False := by site_cls
theorem mma_init : ∀ s : Proof.Mma.Site, s.pc ∈ initPcs → False := by site_cls
theorem exitsite_init : ∀ s : Proof.WComp.ExitSite, s.pc ∈ initPcs → False := by site_cls

/-- The prologue's site at position 180 is `bar2`. -/
theorem pc180 (s : ProA.Site) (h : s.pc = 180) : s = .bar2 := by
  cases s with
  | bar2 => rfl
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k =>
    exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    exfalso; revert h; revert j; revert b; decide
  | _ => exfalso; revert h; decide

/-- The prologue's site at an election's position is the election. -/
theorem pc_el (j : Fin 12) (s : ProA.Site) (h : s.pc = (ProA.Site.el j).pc) : s = .el j := by
  revert h
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => revert k; revert j; decide
  | pb b i | lb b i | pel b i | ptc b i | stq b i => revert i; revert b; revert j; decide
  | _ => revert j; decide

/-- The only prologue site after an election and up to its initialization is the
initialization. -/
theorem pc_between (j : Fin 12) (s : ProA.Site) (h1 : (ProA.Site.el j).pc < s.pc)
    (h2 : s.pc ≤ (ProA.Site.init j).pc) : s = .init j := by
  revert h1 h2
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => revert k; revert j; decide
  | pb b i | lb b i | pel b i | ptc b i | stq b i => revert i; revert b; revert j; decide
  | _ => revert j; decide

theorem el_close (j : Fin 12) : (ProA.Site.el j).pc ∈ Proof.ProA.closePcs ∧
    (ProA.Site.el j).pc < 180 := by
  fin_cases j <;> decide

theorem el_strict (j : Fin 12) : (ProA.Site.el j).pc ∈ Proof.ProA.strictPcs := by
  fin_cases j <;> decide

theorem init_strict (j : Fin 12) : (ProA.Site.init j).pc ∈ Proof.ProA.strictPcs ∧
    (ProA.Site.init j).pc < 180 := by
  fin_cases j <;> decide

/-- A `bar.sync 0, 128`. -/
def isBar2Op : Op → Bool
  | .barSyncN (.imm v) (.imm w) _ => decide (v = 0) && decide (w = 128)
  | _ => false

/-- An event at position 180 is `bar.sync 0, 128`. -/
theorem fires_bar2 (hb : L.block = 256) {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[180]? = some ins)
    (hf : Fires 180 (eventTmpl Assumptions.all L g t ins.op) e o) :
    e = ⟨180, .bar 0 (some 128) .sync⟩ := by
  have h1 : kernel.code[180]?.map (fun i => isBar2Op i.op) = some true := by decide +kernel
  rw [hc] at h1
  have h2 : isBar2Op ins.op = true := Option.some.inj h1
  cases hop : ins.op with
  | barSyncN a b al =>
    rw [hop] at h2 hf
    cases a with
    | imm v =>
      cases b with
      | imm w =>
        simp only [isBar2Op, Bool.and_eq_true, decide_eq_true_eq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact Proof.EvD.fires_barSyncN_128 (by omega) hf
      | _ => simp [isBar2Op] at h2
    | _ => simp [isBar2Op] at h2
  | _ => rw [hop] at h2; simp [isBar2Op] at h2

theorem initBar_off_inj : ∀ a < 12, ∀ b < 12,
    (Proof.ProA.initBar a).off = (Proof.ProA.initBar b).off → a = b := by
  decide +kernel

theorem pc_ge27 (s : ProA.Site) : 27 ≤ s.pc := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j => revert j; revert b; decide
  | _ => decide

theorem initBar_loc_inj {c c' : Nat} {i j : Fin 12}
    (h : (Proof.ProA.initBar i.val).loc L c = (Proof.ProA.initBar j.val).loc L c') :
    i = j ∧ c = c' := by
  simp only [Proof.EvD.Bar.loc, Loc.mk.injEq, true_and] at h
  refine ⟨Fin.ext (initBar_off_inj i.val i.isLt j.val j.isLt (by omega)), h.1⟩

/-! ### The invariant -/

/-- The thread's initializations of barrier `j` of its CTA. -/
def initN (L : Launch) (g : Nat) (j : Fin 12) (es : List Event) : Nat :=
  es.countP fun e => match e.kind with
    | .mbInit l _ => decide (l = (Proof.ProA.initBar j.val).loc L (g / L.block))
    | _ => false

/-- The initialization event of barrier `j` of the thread's CTA. -/
def initEv (L : Launch) (g : Nat) (j : Fin 12) : Event :=
  ⟨(ProA.Site.init j).pc, .mbInit ((Proof.ProA.initBar j.val).loc L (g / L.block)) 1⟩

/-- **After the election `el j`**: the trace has the election, and the initialization of barrier
`j` when the election returned the thread's lane in warp 0. -/
def ElF (L : Launch) (g : Nat) (j : Fin 12) (es : List Event) : Prop :=
  ∃ k0 inst ld : Nat,
    es[k0]? = some (⟨(ProA.Site.el j).pc, .elect 4294967295 inst ld⟩ : Event) ∧
    (ld = laneOf L g → g % L.block < 32 → ∃ k1 : Nat, es[k1]? = some (initEv L g j))

/-- **The prologue's facts at a state.** -/
def PIP (L : Launch) (g : Nat) (d : ProA.D) (es : List Event) : Prop :=
  (d.site.pc ≤ 180 → es.countP (Execution.isBarId 0) = 2) ∧
  (180 < d.site.pc → 3 ≤ es.countP (Execution.isBarId 0)) ∧
  (∀ j : Fin 12, initN L g j es ≤ if (ProA.Site.init j).pc < d.site.pc then 1 else 0) ∧
  ∀ j : Fin 12, (ProA.Site.el j).pc < d.site.pc →
    ∃ k0 inst ld : Nat,
      es[k0]? = some (⟨(ProA.Site.el j).pc, .elect 4294967295 inst ld⟩ : Event) ∧
      (d.site = .init j → ld = laneOf L g ∧ g % L.block < 32) ∧
      ((ProA.Site.init j).pc < d.site.pc → ld = laneOf L g → g % L.block < 32 →
        ∃ k1 : Nat, es[k1]? = some (initEv L g j))

/-- **The facts along a thread**: none of the startup initializes a barrier; the prologue's
`PIP`; after the prologue every election's facts. -/
def PI (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → List Event → Prop
  | (.inl _, _), es => ∀ j, initN L g j es = 0
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), es => PIP L g d es
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, _⟩⟩, _), es => ∀ j, ElF L g j es
  | _, _ => True

theorem getElem?_append_some {es : List Event} {e x : Event} {k : Nat} (h : es[k]? = some x) :
    (es ++ [e])[k]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem getElem?_append_last (es : List Event) (e : Event) : (es ++ [e])[es.length]? = some e := by
  simp

theorem initN_snoc (j : Fin 12) (es : List Event) (e : Event) :
    initN L g j (es ++ [e]) = initN L g j es + (match e.kind with
      | .mbInit l _ => if l = (Proof.ProA.initBar j.val).loc L (g / L.block) then 1 else 0
      | _ => 0) := by
  simp only [initN, List.countP_append, List.countP_singleton]
  split <;> simp_all

theorem initN_other {j : Fin 12} {es : List Event} {e : Event}
    (h : ∀ l c, e.kind ≠ .mbInit l c) : initN L g j (es ++ [e]) = initN L g j es := by
  rw [initN_snoc]
  split
  · rename_i l c hk; exact absurd hk (h l c)
  · rfl

theorem countP_snoc_le (P : Event → Bool) (es : List Event) (e : Event) :
    es.countP P ≤ (es ++ [e]).countP P := by
  simp only [List.countP_append]; omega

/-- The startup enters a role only from its shuffle. -/
theorem succ_enter {s s' : Startup.D} {e : Event} {r : Startup.Entry}
    (h : Startup.succ L g s e = some (some s')) (hs : s'.site = .enter r) : s.site = .shfl := by
  obtain ⟨site, tm, x, w⟩ := s
  cases site <;> simp only [Startup.succ] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all)

/-- **The prologue's step keeps its facts.** -/
theorem pip_step (hp : Pre Q L m) {tm : Nat} {bw : Value} {d d' : ProA.D}
    {t u : TState} {ins : Instr} {e : Event} {es : List Event}
    (hat : (ProA.code L g (Startup.inh L g Q tm) bw).AtD d t)
    (hi : (ProA.code L g (Startup.inh L g Q tm) bw).inv d) (hx : d.site ≠ .exit)
    (hc : kernel.code[(ProA.code L g (Startup.inh L g Q tm) bw).pc d]? = some ins)
    (hf : Fires ((ProA.code L g (Startup.inh L g Q tm) bw).pc d)
      (eventTmpl Assumptions.all L g t ins.op) e (some u))
    (hn : ProA.next L g d e = some (some d')) (hP : PIP L g d es) :
    PIP L g d' (es ++ [e]) ∧ (d'.site = .exit → ∀ j, ElF L g j (es ++ [e])) := by
  have hb : L.block = 256 := hp.block
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
  obtain ⟨hle, -⟩ := pro_pc_le hn
  obtain ⟨hcl, hb2⟩ := pro_close hn
  have hev : ProA.Ev L g d e := ProA.shape (Startup.inh L g Q tm) hx hat hi hc hf
  have hpc : (ProA.code L g (Startup.inh L g Q tm) bw).pc d = d.site.pc := rfl
  rw [hpc] at hc hf
  -- an initialization event is at `init i`, of barrier `i`
  have hinit : ∀ l c, e.kind = .mbInit l c → ∃ i : Fin 12, d.site = .init i ∧
      e = initEv L g i := by
    intro l c hk
    obtain ⟨i, hi'⟩ := proA_init d.site (init_pc hc hf hk)
    refine ⟨i, hi', ?_⟩
    have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi (by rw [hpc]; exact hc)
      (by rw [hpc]; exact hf)
    have := Proof.ProA.shape_in (Proof.ProA.sharedOk_of_pre hp) (i := i.val) i.isLt hF
      (by simp only [ProA.D.old, hi', in_old])
    rw [this]
    simp only [initEv, Proof.ProA.evPc, ProA.D.old, hi', in_old]
    rw [ProA.pc_old (.init i) (by nofun), in_old]
  -- the barrier-0 count
  have hc0 : (d'.site.pc ≤ 180 → (es ++ [e]).countP (Execution.isBarId 0) = 2) ∧
      (180 < d'.site.pc → 3 ≤ (es ++ [e]).countP (Execution.isBarId 0)) := by
    have hmono := countP_snoc_le (Execution.isBarId 0) es e
    by_cases h180 : d.site.pc < 180
    · have hnb : Execution.isBarId 0 e = false := by
        cases hq : Execution.isBarId 0 e
        · rfl
        · exfalso
          obtain ⟨pc', c, md, hk⟩ : ∃ pc' c md, e = ⟨pc', .bar 0 c md⟩ := by
            obtain ⟨pc', k⟩ := e
            cases k <;> simp [Execution.isBarId] at hq
            subst hq
            exact ⟨_, _, _, rfl⟩
          rw [hk] at hf
          cases c with
          | none =>
            have := b0n_pc hc hf rfl (by omega)
            simp only [b0nPcs, List.mem_cons, List.mem_nil_iff, or_false] at this
            have := pc_ge27 d.site
            omega
          | some c =>
            have := b0c_pc hc hf rfl (by omega)
            simp only [b0cPcs, List.mem_cons, List.mem_nil_iff, or_false] at this
            omega
      have hc' : (es ++ [e]).countP (Execution.isBarId 0) = es.countP (Execution.isBarId 0) := by
        simp [List.countP_append, hnb]
      have h2 := (hcl h180).1 180 (by decide) h180
      exact ⟨fun _ => by rw [hc']; exact hP1 (by omega), fun h => by omega⟩
    · by_cases hb180 : d.site.pc = 180
      · have hs := pc180 _ hb180
        have h3 := hb2 hs
        rw [hb180] at hc hf
        have he := fires_bar2 hb hc hf
        have hc' : (es ++ [e]).countP (Execution.isBarId 0) =
            es.countP (Execution.isBarId 0) + 1 := by
          simp [List.countP_append, he, Execution.isBarId]
        exact ⟨fun h => by omega, fun _ => by rw [hc', hP1 (by omega)]⟩
      · exact ⟨fun h => by omega, fun _ => le_trans (hP2 (by omega)) hmono⟩
  refine ⟨⟨hc0.1, hc0.2, fun j => ?_, fun j hj => ?_⟩, fun hxd j => ?_⟩
  · -- the initializations
    by_cases hk : ∃ l c, e.kind = .mbInit l c
    · obtain ⟨l, c, hk⟩ := hk
      obtain ⟨i, hs, he⟩ := hinit l c hk
      have hst := (hcl (by rw [hs]; exact (init_strict i).2)).2
        (by rw [hs]; exact (init_strict i).1)
      rw [initN_snoc, he]
      simp only [initEv]
      by_cases hij : i = j
      · subst hij
        have := hP3 i
        rw [hs] at this hst
        simp only [lt_irrefl, ite_false, nonpos_iff_eq_zero] at this
        simp [this, hst]
      · have hne : (Proof.ProA.initBar i.val).loc L (g / L.block) ≠
            (Proof.ProA.initBar j.val).loc L (g / L.block) := fun h => hij (initBar_loc_inj h).1
        simp only [hne, ite_false, Nat.add_zero]
        refine le_trans (hP3 j) ?_
        split <;> split <;> omega
    · push Not at hk
      rw [initN_other hk]
      refine le_trans (hP3 j) ?_
      split <;> split <;> omega
  · -- the election facts
    by_cases hsel : d.site = .el j
    · obtain ⟨mk, inst, ld, hk, hiff⟩ := pro_el_step hb hsel hn
      have hev' : ∃ inst ld, e = ⟨(ProA.Site.el j).pc, .elect 4294967295 inst ld⟩ := by
        have h' := hev
        simp only [ProA.Ev, hsel] at h'
        exact h'
      obtain ⟨inst', ld', he'⟩ := hev'
      rw [he'] at hk
      simp only [Kind.elect.injEq] at hk
      obtain ⟨-, -, rfl⟩ := hk
      refine ⟨es.length, inst', ld', ?_, fun hs => ⟨(hiff.mp hs).1.symm, (hiff.mp hs).2⟩,
        fun hlt hl hw => ?_⟩
      · rw [getElem?_append_last, he']
      · exfalso
        have := hiff.mpr ⟨hl.symm, hw⟩
        rw [this] at hlt
        omega
    · have hjd : (ProA.Site.el j).pc < d.site.pc := by
        by_contra hge
        have hlt : d.site.pc < (ProA.Site.el j).pc := by
          rcases Nat.lt_or_ge d.site.pc (ProA.Site.el j).pc with h | h
          · exact h
          · exact absurd (pc_el j _ (by omega)) hsel
        have := (hcl (by have := (el_close j).2; omega)).1 _ (el_close j).1 hlt
        omega
      obtain ⟨k0, inst, ld, hk0, hin, hpost⟩ := hP4 j hjd
      refine ⟨k0, inst, ld, getElem?_append_some hk0, fun hs => ?_, fun hlt hl hw => ?_⟩
      · exact absurd (pro_in_pred hn hs) hsel
      · by_cases hsi : d.site = .init j
        · have hf' := hf
          rw [hsi] at hc hf'
          obtain ⟨hl', hw'⟩ := hin hsi
          refine ⟨es.length, ?_⟩
          rw [getElem?_append_last]
          -- the event of `init j` is its initialization
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi
            (by rw [hpc, hsi]; exact hc)
            (by rw [hpc, hsi]; exact hf')
          have := Proof.ProA.shape_in (Proof.ProA.sharedOk_of_pre hp) (i := j.val) j.isLt hF
            (by simp only [ProA.D.old, hsi, in_old])
          rw [this]
          simp only [initEv, Proof.ProA.evPc, ProA.D.old, hsi, in_old]
          rw [ProA.pc_old (.init j) (by nofun), in_old]
        · have hdi : (ProA.Site.init j).pc < d.site.pc := by
            by_contra hge
            exact hsi (pc_between j _ hjd (by omega))
          obtain ⟨k1, hk1⟩ := hpost hdi hl hw
          exact ⟨k1, getElem?_append_some hk1⟩
  · -- the prologue's exit: every election is before `bar18`
    have h18 : d.site = .bar18 := exit_from_bar18 hn hxd
    have hjd : (ProA.Site.el j).pc < d.site.pc := by rw [h18]; fin_cases j <;> decide
    obtain ⟨k0, inst, ld, hk0, -, hpost⟩ := hP4 j hjd
    refine ⟨k0, inst, ld, getElem?_append_some hk0, fun hl hw => ?_⟩
    obtain ⟨k1, hk1⟩ := hpost (by rw [h18]; fin_cases j <;> decide) hl hw
    exact ⟨k1, getElem?_append_some hk1⟩

/-- **The facts along every thread.** -/
theorem pi_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      PI Q L g σ ((X.tr g).take k) := by
  have hb : L.block = 256 := hp.block
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    intro j
    simp [initN]
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rw [htake]
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      cases o with
      | none => exact absurd (fires_none_ends hf) hnE
      | some u =>
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup: no initialization; it enters the prologue at its first site
        have hni : ∀ l c, e.kind ≠ .mbInit l c := fun l c hk' =>
          startup_init st.site (init_pc hc hf hk')
        have h0 : ∀ j, initN L g j ((X.tr g).take k ++ [e]) = 0 := fun j => by
          rw [initN_other hni]; exact hR0 j
        rw [next_start] at hn
        obtain ⟨s', hs', rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j hj
          have hx : ∃ r, Startup.enterOf s' = some r := by
            simp only [Code.gatedExit] at hj
            cases hq : Startup.enterOf s' with
            | none => rw [hq] at hj; simp at hj
            | some r => exact ⟨r, rfl⟩
          obtain ⟨r, hr⟩ := hx
          have hsr : s'.site = .enter r := by
            simp only [Startup.enterOf] at hr
            split at hr <;> simp_all
          have hsh := succ_enter hs' hsr
          rcases j with (_ | _) | _
          · -- the prologue's first state
            have hev := frag_ev hp hg hJ hat hi hc hf
            have hev' : Startup.Ev L g st e := hev
            obtain ⟨site, tm0, x0, w0⟩ := st
            simp only at hsh
            subst hsh
            simp only [Startup.Ev] at hev'
            obtain ⟨recv, ok, rfl⟩ := hev'
            have hC := c0_inv hp hX hg k hlt _ hk0
            have hC' : ((X.tr g).take k).countP (Execution.isBarId 0) = 2 := hC
            refine ⟨fun _ => ?_, fun h => ?_, fun j => ?_, fun j h => ?_⟩
            · simp [List.countP_append, hC', Execution.isBarId]
            · change 180 < 27 at h; omega
            · rw [h0 j]; exact Nat.zero_le _
            · exfalso; change _ < 27 at h; revert h; fin_cases j <;> decide
          · trivial
          · trivial
        · exact h0
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | worker w => trivial
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
            obtain ⟨hP, hE⟩ := pip_step hp hat hi.1 hxd hc hf hd'' (hR0 : PIP L g d _)
            have hx : ProA.exitOf d'' = none ∨ ∃ v, ProA.exitOf d'' = some v := by
              cases ProA.exitOf d'' <;> simp
            rcases hx with hx | ⟨v, hxo⟩
            · rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
              simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
              obtain ⟨rfl, -⟩ := he''
              exact hP
            · have hxs : d''.site = .exit := by
                simp only [ProA.exitOf] at hxo
                split at hxo <;> simp_all
              cases hsel : ProA.selTail Q L g v d'' with
              | some dt' =>
                rw [Code.enter_some (i := Sum.inl dt')
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                exact hE hxs
              | none =>
                rw [Code.enter_some (i := Sum.inr ())
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
          · rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            intro j
            obtain ⟨k0, inst, ld, hk0, hpost⟩ := (hR0 : ∀ j, ElF L g j _) j
            refine ⟨k0, inst, ld, getElem?_append_some hk0, fun hl hw => ?_⟩
            obtain ⟨k1, hk1⟩ := hpost hl hw
            exact ⟨k1, getElem?_append_some hk1⟩
          · exact hJ.elim
      · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
