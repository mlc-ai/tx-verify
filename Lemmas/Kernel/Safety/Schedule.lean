-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table
public import Core.Assembly.Safety
public import Core.Thread.SetMaxNReg
public import Core.Sync.Aligned

@[expose] public section

/-! # Barrier and register classes from a schedule

A proof tool, generic over the kernel. Three classes of Core's `Unsafe` compare the `k`-th event
of one kind across the lanes of a group: the barrier events of a warp (ERR-BARRIER-MISMATCH,
`BarMismatch`), the aligned instructions of a warp and their participants' exits
(ERR-ALIGNED-MISMATCH, `AlignedMismatch`) and the `setmaxnreg` requests of a warpgroup
(ERR-SETMAXNREG, `SetMaxNReg.UnsafeAt`). Each follows from a **schedule**: a function giving the
operands of a thread's `k`-th event of the kind, equal for two threads of one group.

* **Barriers** (`noBarMismatch_of_schedule`): every barrier event of a launched thread has the
  barrier, thread count and form `B g k` of its ordinal `k` among the thread's barrier events, and
  `B g = B h` for two lanes of a warp. `RoleTable.noBarMismatch` states the first premise per
  state (the ordinal is a use count of the role's ledger, `Frame.count_eq`).
* **Aligned instructions** (`noAlignedMismatch_of_schedule`): for each class of aligned
  instructions, the `k`-th event of the class has a warp-uniform source position and operands, and
  the participants of the class's exit clause all make the same number of its events, all of them
  if they exit.
* **Register requests** (`noSetMaxNReg_of_schedule`): every request has the direction and count
  `R g k` of its ordinal `k`; `R g = R h` within a warpgroup; a thread's requests move the count in
  their direction (`hmono`); a block is whole warpgroups (`L.block % 128 = 0`); and a request after
  the first follows its group's previous requests (`hsync`, Core's clause; vacuous for a thread with
  one request, `noSetMaxNReg_of_first`).

The schedule is the kernel's: which barrier a role's `k`-th barrier is, and which count its
`k`-th request asks, are facts of the role's reference invariant at the site (the ordinal is a
ghost count), and the lanes of a group agree on them when the invariant's terms agree (the warp's
collective sources, launch values). -/

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution}

/-! ### ERR-BARRIER-MISMATCH -/

/-- **ERR-BARRIER-MISMATCH from a warp-uniform barrier schedule**: every barrier event of a launched
thread has the barrier, count and form of its ordinal in the schedule, and two lanes of a warp have
one schedule. -/
theorem noBarMismatch_of_schedule (B : Nat → Nat → Nat × Option Nat × BarMode)
    (hB : ∀ g k pc id cnt mode, g < L.threads → X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ →
      (id, cnt, mode) = B g (((X.tr g).take k).countP Execution.isBar))
    (hW : ∀ g h, SameWarp L g h → B g = B h) : ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', cnt, cnt', pc, pc', hs, hi, hj, hk, hne⟩ |
    ⟨g, h, i, j, id, id', cnt, cnt', m', pc, pc', hs, hi, hj, hk, hne⟩)
  · have e1 := hB g i pc id cnt .sync hs.1.1 hi
    have e2 := hB h j pc' id' cnt' .sync hs.1.2.1 hj
    rw [← hk, ← hW g h hs, ← e1] at e2
    simp only [Prod.mk.injEq] at e2
    rcases hne with h1 | h1
    · exact h1 e2.1.symm
    · exact h1 e2.2.1.symm
  · have e1 := hB g i pc id cnt .arrive hs.1.1 hi
    have e2 := hB h j pc' id' cnt' m' hs.1.2.1 hj
    rw [← hk, ← hW g h hs, ← e1] at e2
    simp only [Prod.mk.injEq] at e2
    rcases hne with h1 | h1 | h1
    · exact h1 e2.1.symm
    · exact h1 e2.2.1.symm
    · exact h1 e2.2.2

section table
variable {K : Kernel} {A : List Assumption} {mem0 : Mem0} {C : (g : Nat) → Code K A L g}
  {T : RoleTable C} {S : Nat → Prop}

/-- **ERR-BARRIER-MISMATCH on a role table** that follows every launched thread: the schedule's
first premise per state. -/
theorem RoleTable.noBarMismatch (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S) (hF : T.Followed X S)
    (hall : ∀ g < L.threads, S g) (B : Nat → Nat → Nat × Option Nat × BarMode)
    (hB : ∀ g k d pc id cnt mode, S g → stateAt C X g k = some (some d) → T.J g d →
      (C g).inv d → T.Ev g d ⟨pc, .bar id cnt mode⟩ →
      (id, cnt, mode) = B g (((X.tr g).take k).countP Execution.isBar))
    (hW : ∀ g h, SameWarp L g h → B g = B h) : ¬ BarMismatch L X :=
  noBarMismatch_of_schedule B (fun g k pc id cnt mode hg he =>
    RoleTable.forall_at hC hX hT hF (P := fun e => ∃ pc id cnt mode, e = ⟨pc, .bar id cnt mode⟩)
      (Q := fun i e => ∀ pc id cnt mode, e = ⟨pc, .bar id cnt mode⟩ →
        (id, cnt, mode) = B i.1 (((X.tr i.1).take i.2).countP Execution.isBar))
      (fun e ⟨pc, id, cnt, mode, h⟩ f => by subst h; simp)
      (fun g k d e hg hσ hJ hi hev _ pc id cnt mode h => by
        subst h; exact hB g k d pc id cnt mode hg hσ hJ hi hev)
      (hall g hg) he ⟨pc, id, cnt, mode, rfl⟩ pc id cnt mode rfl) hW

end table

/-! ### ERR-SETMAXNREG -/

end PTX.Frame

namespace PTX.SetMaxNReg

variable {X : Execution}

/-- The request count a thread's earlier events leave, from the end. -/
theorem prior_of_foldl :
    ∀ (k : Nat) (es : List Event) {m : Nat},
      (es.take k).foldl (fun old ev => match ev.kind with
        | .setMaxReg _ n _ => some n | _ => old) none = some m →
      ∃ j < k, ∃ pc inc inst, es[j]? = some ⟨pc, .setMaxReg inc m inst⟩ ∧
        (es.take k).countP isRequest = (es.take j).countP isRequest + 1
  | 0, es, m, h => by simp at h
  | k + 1, es, m, h => by
    by_cases hk : k < es.length
    · rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
        List.foldl_append] at h
      simp only [List.foldl_cons, List.foldl_nil] at h
      have htk : (es.take (k + 1)).countP isRequest =
          (es.take k).countP isRequest + (if isRequest es[k] then 1 else 0) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
          List.countP_append]
        simp
      have hget : es[k]? = some es[k] := List.getElem?_eq_getElem hk
      generalize es[k] = x at h htk hget
      obtain ⟨pc, kd⟩ := x
      cases kd with
      | setMaxReg inc n inst =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨k, by omega, pc, inc, inst, hget, by simp [htk, isRequest]⟩
      | _ =>
        obtain ⟨j, hj, pc', inc, inst, hget', hc⟩ := prior_of_foldl k es h
        exact ⟨j, by omega, pc', inc, inst, hget', by simp [htk, isRequest, hc]⟩
    · have h1 : es.take (k + 1) = es.take k := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [h1] at h ⊢
      obtain ⟨j, hj, rest⟩ := prior_of_foldl k es h
      exact ⟨j, by omega, rest⟩

/-- **The prior count of a request is its thread's previous request's**, whose ordinal is one
less. -/
theorem prior_eq {e : EvId} {m : Nat} (h : prior X e = some m) :
    ∃ j < e.2, ∃ pc inc inst, Request X (e.1, j) pc inc m inst ∧
      ordinal X (e.1, j) + 1 = ordinal X e := by
  obtain ⟨j, hj, pc, inc, inst, hget, hc⟩ := prior_of_foldl e.2 (X.tr e.1) h
  exact ⟨j, hj, pc, inc, inst, hget, hc.symm⟩

end PTX.SetMaxNReg

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution}

/-- **ERR-SETMAXNREG from a warpgroup-uniform request schedule.** -/
theorem noSetMaxNReg_of_schedule {A : List Assumption} (hb : 0 < L.block ∧ L.block % 128 = 0)
    (R : Nat → Nat → Bool × Nat)
    (hR : ∀ g k pc inc n inst, X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      (inc, n) = R g (SetMaxNReg.ordinal X (g, k)))
    (hW : ∀ g h, SetMaxNReg.SameGroup L g h → R g = R h)
    (hmono : ∀ g k, ((R g (k + 1)).1 = true → (R g k).2 ≤ (R g (k + 1)).2) ∧
      ((R g (k + 1)).1 = false → (R g (k + 1)).2 ≤ (R g k).2))
    (hsync : ∀ e pc inc n inst, SetMaxNReg.Request X e pc inc n inst →
      A.all (fun a => !a.regSyncExempt pc) = true → 0 < SetMaxNReg.ordinal X e →
      ∀ h, h < L.threads → SetMaxNReg.SameGroup L e.1 h →
        ∃ j pc' inc' n' inst', SetMaxNReg.Request X (h, j) pc' inc' n' inst' ∧
          SetMaxNReg.ordinal X (h, j) + 1 = SetMaxNReg.ordinal X e ∧ baseCausality L X (h, j) e) :
    ¬ SetMaxNReg.UnsafeAt A L X := by
  rintro ⟨⟨g, k⟩, pc, inc, n, inst, hr, ⟨m, hm, hcmp⟩ | h2 | ⟨f, pc', inc', n', inst', hs, hf, ho,
    hne⟩ | ⟨hA, hpos, hno⟩⟩
  · obtain ⟨j, -, pcj, incj, instj, hj, hord⟩ := SetMaxNReg.prior_eq hm
    have e1 := hR g j pcj incj m instj hj
    have e2 := hR g k pc inc n inst hr
    simp only at hord e1
    rw [← hord] at e2
    obtain ⟨hup, hdown⟩ := hmono g (SetMaxNReg.ordinal X (g, j))
    rw [← e1, ← e2] at hup hdown
    cases inc
    · simp only [Bool.false_eq_true, ↓reduceIte] at hcmp
      have := hdown rfl
      omega
    · simp only [↓reduceIte] at hcmp
      have := hup rfl
      omega
  · simp only at h2
    have hx : g % L.block < L.block := Nat.mod_lt _ hb.1
    omega
  · have e1 := hR g k pc inc n inst hr
    have e2 := hR f.1 f.2 pc' inc' n' inst' hf
    rw [← ho, ← hW g f.1 hs, ← e1] at e2
    simp only [Prod.mk.injEq] at e2
    rcases hne with h1 | h1
    · exact h1 e2.1.symm
    · exact h1 e2.2.symm
  · exact hno (hsync _ pc inc n inst hr hA hpos)

/-- **ERR-SETMAXNREG for threads that make one request each**: every request is a thread's first
(`hfirst`), so no prior count and no group clause apply; its direction and count are the
warpgroup's. -/
theorem noSetMaxNReg_of_first {A : List Assumption} (hb : 0 < L.block ∧ L.block % 128 = 0)
    (R : Nat → Bool × Nat)
    (hR : ∀ g k pc inc n inst, X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ → (inc, n) = R g)
    (hW : ∀ g h, SetMaxNReg.SameGroup L g h → R g = R h)
    (hfirst : ∀ e pc inc n inst, SetMaxNReg.Request X e pc inc n inst →
      SetMaxNReg.ordinal X e = 0) :
    ¬ SetMaxNReg.UnsafeAt A L X := by
  rintro ⟨⟨g, k⟩, pc, inc, n, inst, hr, ⟨m, hm, -⟩ | h2 | ⟨f, pc', inc', n', inst', hs, hf, -,
    hne⟩ | ⟨-, hpos, -⟩⟩
  · obtain ⟨j, -, pcj, incj, instj, hj, hord⟩ := SetMaxNReg.prior_eq hm
    have := hfirst _ pc inc n inst hr
    omega
  · simp only at h2
    have hx : g % L.block < L.block := Nat.mod_lt _ hb.1
    omega
  · have e1 := hR g k pc inc n inst hr
    have e2 := hR f.1 f.2 pc' inc' n' inst' hf
    rw [← hW g f.1 hs, ← e1] at e2
    simp only [Prod.mk.injEq] at e2
    rcases hne with h1 | h1
    · exact h1 e2.1.symm
    · exact h1 e2.2.symm
  · have := hfirst _ pc inc n inst hr
    omega

/-! ### ERR-ALIGNED-MISMATCH -/

/-- A thread's events of a class up to and including one of them. -/
theorem countP_take_lt_countP {P : Event → Bool} {es : List Event} {i : Nat} {ev : Event}
    (hev : es[i]? = some ev) (hp : P ev = true) : (es.take i).countP P + 1 ≤ es.countP P := by
  have h1 : (es.take (i + 1)).countP P = (es.take i).countP P + 1 := by
    rw [List.take_add_one, hev, Option.toList_some, List.countP_append]
    simp [hp]
  have h2 := (List.take_sublist (i + 1) es).countP_le (p := P)
  omega

/-- **ERR-ALIGNED-MISMATCH from schedules.** For every class of aligned instructions: the `k`-th
event of the class of a thread is at the source position and has the operands `P c g k`, the same
for two lanes of a warp (`hP`, `hW`); and every participant makes `N c g` events of the class's exit
numbering, the same for two participants, all of them if it exits (`hNp`, `hle`, `hex`). -/
theorem noAlignedMismatch_of_schedule {K : Kernel}
    (P : AlignedClass → Nat → Nat → Nat × Option Kind)
    (hP : ∀ c g k pe ke, X.get (g, k) = some ⟨pe, ke⟩ → c.member ⟨pe, ke⟩ = true →
      (pe, c.operands ke) = P c g (((X.tr g).take k).countP c.member))
    (hW : ∀ c g h, SameWarp L g h → P c g = P c h)
    (N : AlignedClass → Nat → Nat)
    (hNp : ∀ c g h, c.Participants L g h → N c g = N c h)
    (hle : ∀ c g, (X.tr g).countP (c.exitMember K) ≤ N c g)
    (hex : ∀ c g j pc, X.get (g, j) = some ⟨pc, .exit⟩ →
      (X.tr g).countP (c.exitMember K) = N c g) :
    ¬ AlignedMismatch L K X := by
  rintro ⟨c, ⟨e, f, pe, pf, ke, kf, hs, he, hf, hme, hmf, hk, -, hne⟩ |
    ⟨e, f, ev, hpar, he, hm, -, ⟨pc, hx⟩, hshort⟩⟩
  · have e1 := hP c e.1 e.2 pe ke he hme
    have e2 := hP c f.1 f.2 pf kf hf hmf
    rw [← hk, ← hW c e.1 f.1 hs, ← e1] at e2
    simp only [Prod.mk.injEq] at e2
    rcases hne with h1 | h1
    · exact h1 e2.1.symm
    · exact h1 e2.2.symm
  · have h1 := countP_take_lt_countP (P := c.exitMember K) (es := X.tr e.1) (i := e.2) he hm
    have h2 := hle c e.1
    have h3 := hex c f.1 f.2 pc hx
    have h4 := hNp c e.1 f.1 hpar
    omega

end PTX.Frame
