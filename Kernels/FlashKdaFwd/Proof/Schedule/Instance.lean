-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Contract
public import Kernels.FlashKdaFwd.Proof.Schedule.Dispatch
public import Kernels.FlashKdaFwd.Proof.Thread.Sound

@[expose] public section

/-!
# The progress instance: the time table's arithmetic and the premises proved so far

* The arithmetic of the time table (`timeAt`, `Defs.lean`) on abstract positions:
  `timeAt_start_lt` (a startup position is before the first slot), `timeAt_pipe` (a position
  of the tile loops lies in the slot of its tile), `timeAt_end_ge` (an epilogue position is
  after every slot), `timeAt_lt_of_pc_lt` (within one tile a later instruction is later, from
  sub-step 0), `timeAt_lt_of_pc_lt_of_tile_le` (the same when the tile index does not
  decrease: the state after a barrier event), `timeAt_lt_of_tile_lt` (a position of the tile
  loops at an earlier tile is before every position of a later tile's slot).
* Static premises of the dispatcher (`Premises2`, `Dispatch.lean`), for every state of the
  machine: `prem_started`, `prem_pollShape`, `prem_pollTime`, `prem_pollOp`, `wkey_eq`
  (`keyWarp`), `prem_block32`.
* Premises from the contract `RefProgress` (`Contract.lean`): `prem_barAfter`; from the
  protocol layer's facts: `prem_barGroup`.
* `terminates_of_ref`: the termination bound from the contract's `left_dec` and a bound on the
  counted events left at the first states.

The remaining premises are derived in `Free.lean` (`freeTmpl`), `Lag.lean` (`barLag`, `coll`,
`matrix`) and `Poll.lean` (`pollState`, `pollBlk`); `Assembly.lean` puts them together.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

/-! ### The arithmetic of the time table -/

/-- A startup position is before the first slot. -/
theorem timeAt_start_lt {T t pc sub : Nat} (h : pc ≤ 1402) (hs : sub ≤ 3) :
    timeAt T t pc sub < slot := by
  unfold timeAt slot
  split_ifs
  omega

/-- A position of the tile loops lies in the slot of its tile. -/
theorem timeAt_pipe {T t pc sub : Nat} (h1 : 1402 < pc) (h2 : pc ≤ 3112) (hs : sub ≤ 3)
    (ht : t ≤ T) :
    slot * (t + 1) ≤ timeAt T t pc sub ∧ timeAt T t pc sub < slot * (t + 2) := by
  have hmin : min t T = t := Nat.min_eq_left ht
  unfold timeAt band slot
  rw [hmin]
  split_ifs <;> omega

/-- An epilogue position is after every slot. -/
theorem timeAt_end_ge {T t pc sub : Nat} (h : 3113 ≤ pc) :
    slot * (T + 2) ≤ timeAt T t pc sub := by
  unfold timeAt
  split_ifs <;> omega

/-- Within one tile a later instruction is later, from sub-step 0. -/
theorem timeAt_lt_of_pc_lt {T t pc pc' sub' : Nat} (h : pc < pc') :
    timeAt T t pc 0 < timeAt T t pc' sub' := by
  unfold timeAt band slot
  have hm : min t T ≤ T := Nat.min_le_right _ _
  generalize min t T = m at hm
  split_ifs <;> omega

/-- A later instruction at the same tile or a later one is later, from sub-step 0: what the
state after a barrier event needs. -/
theorem timeAt_lt_of_pc_lt_of_tile_le {T t t' pc pc' sub' : Nat} (h : pc < pc') (ht : t ≤ t')
    (ht' : t' ≤ T) : timeAt T t pc 0 < timeAt T t' pc' sub' := by
  unfold timeAt band slot
  rw [Nat.min_eq_left (by omega : t ≤ T), Nat.min_eq_left ht']
  split_ifs <;> omega

/-- A position of the tile loops or of the startup at an earlier tile is before the slot of a
later tile. -/
theorem timeAt_lt_of_tile_lt {T t t' pc sub : Nat} (h2 : pc ≤ 3112) (hs : sub ≤ 3)
    (ht : t < t') (ht' : t' ≤ T) : timeAt T t pc sub + 1 < slot * (t' + 1) := by
  by_cases h1 : pc ≤ 1402
  · have h4 := timeAt_start_lt (T := T) (t := t) h1 hs
    have h5 : slot * 2 ≤ slot * (t' + 1) := Nat.mul_le_mul_left _ (by omega)
    unfold slot at h4 h5 ⊢
    omega
  · have h4 := (timeAt_pipe (T := T) (t := t) (sub := sub) (by omega) h2 hs (by omega)).2
    have h3 : slot * (t + 2) ≤ slot * (t' + 1) := Nat.mul_le_mul_left _ (by omega)
    have h5 : timeAt T t pc sub + 1 ≤ slot * (t + 2) := h4
    -- the last position of a slot is not used: the bands end below it
    have h6 : timeAt T t pc sub + 1 ≠ slot * (t + 2) := by
      unfold timeAt band slot
      rw [Nat.min_eq_left (show t ≤ T by omega)]
      split_ifs <;> omega
    omega

/-! ### Static premises -/

variable {L : Launch} {mem0 : Mem0} {X : Execution} {I : Nums}

/-- The first state of a thread is at a warp collective. -/
theorem init_cls (g : Nat) : siteCls (Thread.init L g).site = .coll := by
  simp only [Thread.init, Thread.entry]
  split_ifs <;> rfl

set_option maxRecDepth 100000 in
/-- **`Premises2.started`**: a thread at a free event or at a poll has made an event. -/
theorem prem_started {g : Nat} {d : Thread.D}
    (hσ : Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d))
    (hc : cls g d = .free ∨ cls g d = .poll) : X.tr g ≠ [] := by
  intro h0
  rw [h0, List.length_nil, Frame.stateAt_zero] at hσ
  have hd : (Thread.code L g).init = d := by
    injection hσ with h
    injection h
  have hi : siteCls (Thread.code L g).init.site = .coll := init_cls (L := L) g
  rw [hd] at hi
  unfold cls at hc
  rw [hi] at hc
  rcases hc with h | h <;> cases h

/-- **`Premises2.pollShape`**: by the definition of `pollEv`. -/
theorem prem_pollShape {g : Nat} {d : Thread.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (Thread.code L g).AtD d t)
    (hi : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) : pollEv L g d e :=
  ⟨t, ins, o, hat, hi, hf⟩

/-- A poll site is `mbarWait j`. -/
theorem site_of_poll {s : Thread.Site} (h : siteCls s = .poll) : ∃ j, s = .mbarWait j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

/-- The ten polls are at instruction 384 or later. -/
theorem mbarWait_pc_ge : ∀ j : Fin 10, 384 ≤ (Thread.Site.mbarWait j).pc := by
  decide +kernel

/-- The instruction of every poll site is an acquiring `mbarrier.try_wait`. -/
theorem mbarWait_op : ∀ j : Fin 10,
    ((Decoded.kernel.code[(Thread.Site.mbarWait j).pc]?).all fun ins =>
      Sched.waitOp ins.op) = true := by decide +kernel

/-- **`Premises2.pollTime`**: a poll state is at time 2 or later. -/
theorem prem_pollTime {g : Nat} {d : Thread.D} (hc : cls g d = .poll) : 2 ≤ time I g d := by
  obtain ⟨j, hj⟩ := site_of_poll hc
  have hpc := mbarWait_pc_ge j
  rw [← hj] at hpc
  unfold time timeAt band slot
  split_ifs <;> omega

/-- **`Premises2.pollOp`**: the instruction of a poll state is an acquiring
`mbarrier.try_wait`. -/
theorem prem_pollOp {g : Nat} {d : Thread.D} (hc : cls g d = .poll) (ins : Instr)
    (hi : kernel.code[(Thread.code L g).pc d]? = some ins) : Sched.waitOp ins.op = true := by
  obtain ⟨j, hj⟩ := site_of_poll hc
  have h := mbarWait_op j
  rw [← hj] at h
  have hi' : Decoded.kernel.code[d.site.pc]? = some ins := hi
  rw [hi'] at h
  simpa using h

/-- **`Premises2.block32`**. -/
theorem prem_block32 (hb : L.block = 192) : L.block % 32 = 0 := by rw [hb]

/-! ### Premises from the contract -/

/-- **`Premises2.barAfter`**: after a barrier event the thread is at a later time, or its
machine has stopped. -/
theorem prem_barAfter (R : RefProgress L mem0 X I) {g j pc id : Nat} {cnt : Option Nat}
    {m : BarMode} {d : Thread.D} (hg : g < L.threads)
    (he : X.get (g, j) = some ⟨pc, .bar id cnt m⟩)
    (hσ : Frame.stateAt (Thread.code L) X g j = some (some d)) :
    (∃ d', Frame.stateAt (Thread.code L) X g (j + 1) = some (some d') ∧
        time I g d < time I g d') ∨
      Frame.stateAt (Thread.code L) X g (j + 1) = none := by
  cases h1 : Frame.stateAt (Thread.code L) X g (j + 1) with
  | none => exact .inr rfl
  | some o =>
    cases o with
    | none => exact absurd h1 (R.tracked g _ hg)
    | some d' =>
      obtain ⟨hsub, hpc, htile⟩ := R.barStep hg hσ he h1
      refine .inl ⟨d', rfl, ?_⟩
      unfold time
      rw [hsub]
      exact timeAt_lt_of_pc_lt_of_tile_le hpc htile (R.tile_le hg h1)

/-- **`Premises2.barGroup`**, from the protocol layer's barrier facts. -/
theorem prem_barGroup {T : Nat → Nat} (hB : BarFacts L X T) (hb : L.block = 192)
    {g i pc id : Nat} {cnt : Option Nat} {m : BarMode} (hg : g < L.threads)
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    ∃ p : Finset Nat, NamedBar.Shape L cnt p id ∧ NamedBar.Sources L X cnt p id ∧
      ∀ w ∈ p, barG id w :=
  Protocol.barGroup hB hb (fun _ hw => .inl ⟨rfl, hw⟩) (fun _ hw => .inr ⟨rfl, hw⟩) hg he

/-! ### Termination -/

set_option maxRecDepth 100000 in
/-- **Termination of the FlashKDA kernel from the reference layer's contract**: the
precondition (it makes the thread machines sound, `Thread.sound`), the contract for every
consistent execution, and at most `n` counted events left at the first state of every
thread. -/
theorem terminates_of_ref {P : Params} {n : Nat} (hpre : Pre P L mem0)
    (hR : ∀ X, Consistent L kernel Assumptions.all mem0 X → RefProgress L mem0 X I)
    (hinit : ∀ g < L.threads, rank I g (Thread.code L g).init ≤ n) :
    BoundGoal kernel Assumptions.all L mem0 :=
  bound_of (C := Thread.code L) (rank := rank I) (n := n) codeOk
    { sound := fun _ hg => Thread.sound hpre hg
      tracked := fun X hX => (hR X hX).tracked
      dec := fun X hX _ hg _ _ _ _ he hσ _ hn => (hR X hX).left_dec hg he hσ hn
      init := hinit }

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
