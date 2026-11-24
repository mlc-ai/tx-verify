-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Ref.Follow
public import Lemmas.Kernel.UbLast
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

/-! # The first stage of the following: every thread up to its second barrier

No state of the startup before its second barrier stops on what an event returned
(`Startup.succ`: the base word's load records whatever value it returns and dies where the bytes
rebuild to no value). So, with no source and no fact about another
thread, every launched thread stands where its count of barrier-0 events says (`early`): while
no undefined behaviour has happened, its machine is

* dead, or
* at the allocation, its store or the first barrier, with no barrier-0 event before it,
* at the base word's load or the second barrier, with one,
* or anywhere else (or not followed any more) with at least two.

`early_at` reads this at an event whose thread has made at most one barrier-0 event before it:
the event is fired from a startup state of the first two kinds, with the startup's shape. This is
what `BaseRead` needs of the other threads (their writes before their second barrier, the sources
of barrier 0's first two instances, no exit before them), and it does not depend on `BaseRead`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The ledger's class of barrier-0 events is `Execution.isBarId 0`. -/
theorem cls_bar0 : cls (.bar 0) = Execution.isBarId 0 := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> rfl

/-- Where a state stands, by the barrier-0 count `c` of its ledger. -/
def EarlyPos : (thread Q L g).D → Prop
  | (.inl s, n) =>
    match s.site with
    | .alloc | .allocWr | .bar0 => n (.bar 0) = 0
    | .ld0 | .bar1 => n (.bar 0) = 1
    | _ => 2 ≤ n (.bar 0)
  | (.inr _, n) => 2 ≤ n (.bar 0)

/-- The barrier-0 count of a thread before position `k`. -/
abbrev c0 (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP (Execution.isBarId 0)

theorem c0_mono {k j : Nat} (h : k ≤ j) : c0 X g k ≤ c0 X g j :=
  (List.take_sublist_take_left h).countP_le

theorem c0_succ {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) :
    c0 X g (k + 1) = c0 X g k + if Execution.isBarId 0 e then 1 else 0 := by
  unfold c0
  rw [List.take_add_one, he, Option.toList_some, List.countP_append]
  by_cases hb : Execution.isBarId 0 e <;> simp [hb]

/-- The startup's step from a state, through the glue and the ledger. -/
theorem next_start {s : Startup.D} {n : Cls → Nat} {e : Event} :
    (thread Q L g).next (.inl s, n) e = (Startup.succ L g s e).map (Option.map fun s' =>
      (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) s', Code.bump cls n e)) := by
  rcases h : Startup.succ L g s e with _ | _ | s' <;>
    simp [thread, Code.roleThread, Code.counted, Code.glue, Startup.code, h]

/-- A startup state that is no exit enters itself. -/
theorem enter_inl {s' : Startup.D} (hx : Startup.enterOf s' = none) :
    Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s' = .inl s' := by
  simp [Code.enter, Code.gatedExit, hx]

/-- A role state steps to a role state. -/
theorem next_role {x} {n : Cls → Nat} {e : Event} {σ' : (thread Q L g).D}
    (h : (thread Q L g).next (.inr x, n) e = some (some σ')) :
    (∃ y, σ'.1 = .inr y) ∧ σ'.2 = Code.bump cls n e := by
  obtain ⟨i, d⟩ := x
  rcases h' : (Code.withStubs (frag Q L g) Startup.Entry.pc i).next d e with _ | _ | d'
  all_goals simp [thread, Code.roleThread, Code.counted, Code.glue, h'] at h
  subst h
  exact ⟨⟨_, rfl⟩, rfl⟩

theorem bump_bar0 (n : Cls → Nat) (e : Event) :
    Code.bump cls n e (.bar 0) = n (.bar 0) + if Execution.isBarId 0 e then 1 else 0 := by
  simp only [Code.bump, cls_bar0]

/-- A startup step into a state that is no exit. -/
theorem to_state {s s' : Startup.D} {n : Cls → Nat} {e : Event}
    (hsu : Startup.succ L g s e = some (some s')) (hx : Startup.enterOf s' = none) :
    (thread Q L g).next (.inl s, n) e = some (some (.inl s', Code.bump cls n e)) := by
  rw [next_start, hsu]
  simp only [Option.map_some]
  rw [enter_inl hx]

/-- **A startup step keeps the position**, for an event of the startup's shape. -/
theorem start_pos {s : Startup.D} {n : Cls → Nat} {e : Event} (hev : Startup.Ev L g s e)
    (hP : EarlyPos (Q := Q) (L := L) (g := g) (.inl s, n)) :
    (thread Q L g).next (.inl s, n) e = none ∨
      ((thread Q L g).next (.inl s, n) e = some none ∧
        2 ≤ n (.bar 0) + if Execution.isBarId 0 e then 1 else 0) ∨
      ∃ σ, (thread Q L g).next (.inl s, n) e = some (some σ) ∧ EarlyPos σ := by
  obtain ⟨site, tm, x, bw⟩ := s
  cases site with
  | alloc =>
    have hP' : n (.bar 0) = 0 := hP
    simp only [Startup.Ev] at hev
    subst hev
    by_cases hl : laneOf L g = 0
    · exact .inr (.inr ⟨_, to_state (s' := ⟨.allocWr, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
        by show _ = 0; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
    · exact .inr (.inr ⟨_, to_state (s' := ⟨.bar0, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
        by show _ = 0; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
  | allocWr =>
    have hP' : n (.bar 0) = 0 := hP
    simp only [Startup.Ev] at hev
    obtain ⟨col, -, rfl⟩ := hev
    exact .inr (.inr ⟨_, to_state (s' := ⟨.bar0, tm, x, bw⟩) (by simp [Startup.succ]) rfl,
      by show _ = 0; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
  | bar0 =>
    have hP' : n (.bar 0) = 0 := hP
    simp only [Startup.Ev] at hev
    subst hev
    exact .inr (.inr ⟨_, to_state (s' := ⟨.ld0, tm, x, bw⟩) (by simp [Startup.succ]) rfl,
      by show _ = 1; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
  | ld0 =>
    have hP' : n (.bar 0) = 1 := hP
    simp only [Startup.Ev] at hev
    obtain ⟨ac, bs, rfl, -⟩ := hev
    cases hr : rebuild 3 bs with
    | error f => exact .inl (by rw [next_start]; simp [Startup.succ, hr])
    | ok v =>
      cases hw : Proof.ProA.word32 v with
      | none => exact .inr (.inr ⟨_,
          to_state (s' := ⟨.bar1, 0, x, v⟩) (by simp [Startup.succ, hr, hw]) rfl,
          by show _ = 1; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
      | some w => exact .inr (.inr ⟨_,
          to_state (s' := ⟨.bar1, w, x, v⟩) (by simp [Startup.succ, hr, hw]) rfl,
          by show _ = 1; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
  | bar1 =>
    have hP' : n (.bar 0) = 1 := hP
    simp only [Startup.Ev] at hev
    subst hev
    by_cases hl : g % L.block < 32
    · exact .inr (.inr ⟨_, to_state (s' := ⟨.relinq, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
        by show 2 ≤ _; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
    · exact .inr (.inr ⟨_, to_state (s' := ⟨.shfl, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
        by show 2 ≤ _; rw [bump_bar0]; simp [Execution.isBarId, hP']⟩)
  | relinq =>
    have hP' : 2 ≤ n (.bar 0) := hP
    exact .inr (.inr ⟨_, to_state (s' := ⟨.shfl, tm, x, bw⟩) (by simp [Startup.succ]) rfl,
      by show 2 ≤ _; rw [bump_bar0]; omega⟩)
  | shfl =>
    have hP' : 2 ≤ n (.bar 0) := hP
    rcases hsu : Startup.succ L g ⟨.shfl, tm, x, bw⟩ e with _ | _ | s'
    · exact .inl (by rw [next_start, hsu]; rfl)
    · exact .inr (.inl ⟨by rw [next_start, hsu]; rfl, by omega⟩)
    · refine .inr (.inr ⟨_, by rw [next_start, hsu]; rfl, ?_⟩)
      simp only [Code.enter]
      split
      · show 2 ≤ _; rw [bump_bar0]; omega
      · rename_i hx
        have hs' : ∃ r, s'.site = .enter r := by
          simp only [Startup.succ] at hsu
          split at hsu <;> (try split at hsu) <;> simp only [Option.some.injEq,
            reduceCtorEq] at hsu
          subst hsu
          exact ⟨_, rfl⟩
        obtain ⟨r, hr⟩ := hs'
        simp [Code.gatedExit, Startup.enterOf, hr] at hx
  | enter r => exact .inl (by rw [next_start]; simp [Startup.succ])

/-- **Where a thread stands before its `k`-th event**, while no undefined behaviour has
happened. -/
theorem early (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, (∀ j < k, ∀ pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) →
      Frame.stateAt (thread Q L) X g k = none ∨
        (Frame.stateAt (thread Q L) X g k = some none ∧ 2 ≤ c0 X g k) ∨
        ∃ σ, Frame.stateAt (thread Q L) X g k = some (some σ) ∧ EarlyPos σ := by
  intro k
  induction k with
  | zero =>
    intro _
    refine .inr (.inr ⟨_, Frame.stateAt_zero, ?_⟩)
    show EarlyPos (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => 0)
    rw [enter_inl enterOf_init]
    unfold Startup.init
    split <;> rfl
  | succ k ih =>
    intro hnu
    have ih' := ih fun j hj => hnu j (by omega)
    by_cases hk : (X.tr g).length ≤ k
    · have h1 := Frame.stateAt_of_le (C := thread Q L) (X := X) (g := g) hk
      have h2 := Frame.stateAt_of_le (C := thread Q L) (X := X) (g := g)
        (show (X.tr g).length ≤ k + 1 by omega)
      have hc : c0 X g (k + 1) = c0 X g k := by
        unfold c0
        rw [List.take_of_length_le hk, List.take_of_length_le (by omega)]
      rw [h2, ← h1, hc]
      exact ih'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hnu' : ∀ f, e.kind ≠ .ub f := fun f hf => by
      obtain ⟨pc, kd⟩ := e
      simp only at hf
      subst hf
      exact hnu k (by omega) pc f he
    have hs := Frame.stateAt_succ (C := thread Q L) (X := X) (g := g) he
    have hc := c0_succ he
    rcases ih' with h0 | ⟨h0, h2⟩ | ⟨σ, hσ, hP⟩
    · left; rw [hs, h0]; rfl
    · right; left
      rw [hs, h0]
      exact ⟨rfl, by omega⟩
    · rw [hs, hσ]
      have hcn : σ.2 (.bar 0) = c0 X g k := by
        have := fcount hσ (.bar 0)
        rw [this, cls_bar0]
      obtain ⟨x, n⟩ := σ
      simp only at hcn
      simp only [Option.bind_some]
      change (thread Q L g).next (x, n) e = none ∨
        ((thread Q L g).next (x, n) e = some none ∧ 2 ≤ c0 X g (k + 1)) ∨
        ∃ σ, (thread Q L g).next (x, n) e = some (some σ) ∧ EarlyPos σ
      rcases x with s | y
      · -- a startup state
        have hst := start_pos (Q := Q) (hP := hP) (start_ev hp hX he hσ hnu')
        rcases hst with h | ⟨h, h2⟩ | h
        · exact .inl h
        · refine .inr (.inl ⟨h, ?_⟩)
          rw [hc, ← hcn]; exact h2
        · exact .inr (.inr h)
      · -- a role state
        have hP' : 2 ≤ n (.bar 0) := hP
        rcases h : (thread Q L g).next (.inr y, n) e with _ | _ | σ'
        · exact .inl rfl
        · exact .inr (.inl ⟨rfl, by rw [hc, ← hcn]; split <;> omega⟩)
        · obtain ⟨⟨y', hy⟩, hn⟩ := next_role h
          refine .inr (.inr ⟨σ', rfl, ?_⟩)
          obtain ⟨x', n'⟩ := σ'
          simp only at hy hn
          subst hy hn
          show 2 ≤ _
          rw [bump_bar0]
          omega

/-- No undefined behaviour before a thread's event. -/
theorem noUb_before (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) :
    ∀ j < k, ∀ pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩ := by
  intro j hj pc f hf
  have := ub_last hX hf he
  omega

/-- **An event of a thread with at most one barrier-0 event before it is fired from a startup
state before the second barrier, with the startup's shape**, when it is no undefined
behaviour. -/
theorem early_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (hc : c0 X g k ≤ 1) :
    ∃ s n, Frame.stateAt (thread Q L) X g k = some (some (.inl s, n)) ∧
      (s.site = .alloc ∨ s.site = .allocWr ∨ s.site = .bar0 ∨ s.site = .ld0 ∨
        s.site = .bar1) ∧ n (.bar 0) = c0 X g k ∧ Startup.Ev L g s e := by
  rcases early hp hX k (noUb_before hX he) with h0 | ⟨h0, h2⟩ | ⟨σ, hσ, hP⟩
  · rcases Frame.fired (fun g hg => thread_sound hp hg) hX he with ⟨σ, o, hσ', -⟩ |
      ⟨-, pc, f, hf⟩
    · rw [h0] at hσ'; cases hσ'
    · exact absurd (by rw [hf]) (hu f)
  · omega
  · have hcn : σ.2 (.bar 0) = c0 X g k := by
      rw [fcount hσ (.bar 0), cls_bar0]
    obtain ⟨x, n⟩ := σ
    simp only at hcn
    rcases x with s | y
    · obtain ⟨site, tm, x, bw⟩ := s
      refine ⟨⟨site, tm, x, bw⟩, n, hσ, ?_, hcn, start_ev hp hX he hσ hu⟩
      cases site <;> simp only [EarlyPos] at hP <;> simp <;> omega
    · simp only [EarlyPos] at hP
      omega

end
end PTX.Kernels.InklingRelDecode.Proof2
