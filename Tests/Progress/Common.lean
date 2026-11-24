-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Existence
public import Lemmas.Execution.NoAsync
public import Lemmas.Kernel.Correct

@[expose] public section

/-!
# Progress tests: shared machinery

The deadlock tests of `Tests/Progress/` show that the model rejects a known-deadlocking program
through CORRECT-PROGRESS: the program has a `Maximal` execution that is not `Complete`. When every
thread of the program is stuck at its first event, the empty execution is that execution
(`empty_maximal`, `empty_not_complete`); a test then only shows that no possible execution has a
thread event. When the stuck threads first record events (an mbarrier initialization, an
arrival), `deadlock_of_bound` gives the maximal execution instead: if every possible execution
has a bounded number of counted events per thread, no linear copy and is not complete, a largest
possible execution exists and is not complete. The run lemmas read the first events of a thread
off its program: a local step is deterministic (`run_of_tau`), and the first event of a run
instantiates the template of the instruction it starts at (`run_of_ev`).
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

section Run
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- No local step leaves a state whose instruction performs an event. -/
theorem tauStar_of_ev {t t1 : TState} {m : Tmpl} (hev : out K A L g t = .ev m)
    (h : Relation.ReflTransGen (Tau K A L g) t t1) : t1 = t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hs _ _ =>
    unfold Tau at hs
    rw [hev] at hs
    cases hs

/-- Local steps from a state whose instruction is local pass through its unique successor. -/
theorem tauStar_of_tau {t t' t1 : TState} (ht : out K A L g t = .tau t')
    (h : Relation.ReflTransGen (Tau K A L g) t t1) :
    t1 = t ∨ Relation.ReflTransGen (Tau K A L g) t' t1 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl rfl
  | head hs hr _ =>
    unfold Tau at hs
    rw [ht] at hs
    cases hs
    exact .inr hr

/-- A run of the successor of a local instruction is a run from that instruction. -/
theorem run_tau {t t' : TState} {e : Event} {l : List Event} {o : Option TState}
    (h : out K A L g t = .tau t') (hr : Run K A L g t' (e :: l) o) :
    Run K A L g t (e :: l) o := by
  cases hr with
  | step hl he hr => exact .step (.head h hl) he hr
  | last hl he => exact .last (.head h hl) he

/-- A run that starts at a local instruction is a run of its successor. -/
theorem run_of_tau {t t' : TState} {e : Event} {l : List Event} {o : Option TState}
    (ht : out K A L g t = .tau t') (h : Run K A L g t (e :: l) o) :
    Run K A L g t' (e :: l) o := by
  have noEv : ∀ {e o}, ¬ EStep K A L g t e o := by
    rintro e o ⟨m, hm, -⟩
    rw [ht] at hm
    cases hm
  cases h with
  | step hl he hr =>
    rcases tauStar_of_tau ht hl with rfl | hl'
    · exact absurd he noEv
    · exact .step hl' he hr
  | last hl he =>
    rcases tauStar_of_tau ht hl with rfl | hl'
    · exact absurd he noEv
    · exact .last hl' he

/-- The first event of a run from a state whose instruction performs an event instantiates that
instruction's template; after a final state (`none`) the run ends. -/
theorem run_of_ev {t : TState} {m : Tmpl} {e : Event} {l : List Event} {o : Option TState}
    (hev : out K A L g t = .ev m) (h : Run K A L g t (e :: l) o) :
    ∃ o', Fires t.pc m e o' ∧ (o' = none → l = []) ∧
      ∀ t2, o' = some t2 → Run K A L g t2 l o := by
  cases h with
  | step hl he hr =>
    rw [tauStar_of_ev hev hl] at he
    obtain ⟨m', hm', hf⟩ := he
    rw [hev] at hm'
    cases hm'
    exact ⟨_, hf, by simp, fun t2 h2 => by cases h2; exact hr⟩
  | last hl he =>
    rw [tauStar_of_ev hev hl] at he
    obtain ⟨m', hm', hf⟩ := he
    rw [hev] at hm'
    cases hm'
    exact ⟨_, hf, fun _ => rfl, fun t2 h2 => by cases h2⟩

/-- A run that starts at an `exit` performs only the exit. -/
theorem run_exit {t : TState} {e : Event} {l : List Event} {o : Option TState}
    (hev : out K A L g t = .ev .exit) (h : Run K A L g t (e :: l) o) :
    e = ⟨t.pc, .exit⟩ ∧ l = [] := by
  obtain ⟨o', ⟨he, ho⟩, hl, -⟩ := run_of_ev hev h
  exact ⟨he, hl ho⟩

/-- A run from an instruction that performs one event and then reaches an `exit` at `pcx`
performs that event and at most the exit. -/
theorem run_shape {t : TState} {m : Tmpl} {P : Event → Prop} {pcx : Nat} {e : Event}
    {l : List Event} {o : Option TState} (hev : out K A L g t = .ev m)
    (hP : ∀ e o, Fires t.pc m e o →
      P e ∧ ∃ t2, o = some t2 ∧ out K A L g t2 = .ev .exit ∧ t2.pc = pcx)
    (h : Run K A L g t (e :: l) o) : P e ∧ (l = [] ∨ l = [⟨pcx, .exit⟩]) := by
  obtain ⟨o', hf, -, hr⟩ := run_of_ev hev h
  obtain ⟨hPe, t2, rfl, hx, hpc⟩ := hP e o' hf
  refine ⟨hPe, ?_⟩
  cases l with
  | nil => exact .inl rfl
  | cons e' l' =>
    obtain ⟨rfl, rfl⟩ := run_exit hx (hr t2 rfl)
    exact .inr (by rw [hpc])

/-- A load at position `pc` that returns `bs`, followed by a run of the state after it. -/
theorem run_read {t : TState} {a : Acc} {k : List (Option Byte) → TState}
    {bs : List (Option Byte)} {pc : Nat} {rest : List Event} {o : Option TState}
    (hev : out K A L g t = .ev (.read a k)) (hpc : t.pc = pc) (hlen : bs.length = a.size)
    (hr : Run K A L g (k bs) rest o) : Run K A L g t (⟨pc, .rd a bs⟩ :: rest) o :=
  .step .refl ⟨_, hev, bs, hlen, by rw [hpc], rfl⟩ hr

/-- A store at position `pc`, followed by a run of the state after it. -/
theorem run_write {t t' : TState} {a : Acc} {bs : List Byte} {pc : Nat} {rest : List Event}
    {o : Option TState} (hev : out K A L g t = .ev (.write a bs t')) (hpc : t.pc = pc)
    (hr : Run K A L g t' rest o) : Run K A L g t (⟨pc, .wr a bs⟩ :: rest) o :=
  .step .refl ⟨_, hev, by rw [hpc], rfl⟩ hr

/-- An `exit` at position `pc` ends the run. -/
theorem run_exit_last {t : TState} {pc : Nat} (hev : out K A L g t = .ev .exit)
    (hpc : t.pc = pc) : Run K A L g t [⟨pc, .exit⟩] none :=
  .last .refl ⟨_, hev, by rw [hpc], rfl⟩

end Run

section Warp

/-- The trace of a thread that runs one event satisfying `P` and then an `exit` at `pcx`, cut at
any point. -/
def OneThenExit (tr : List Event) (P : Event → Prop) (pcx : Nat) : Prop :=
  tr = [] ∨ ∃ e, P e ∧ (tr = [e] ∨ tr = [e, ⟨pcx, .exit⟩])


theorem OneThenExit.mono {tr : List Event} {P P' : Event → Prop} {pcx : Nat}
    (h : OneThenExit tr P pcx) (hP : ∀ e, P e → P' e) : OneThenExit tr P' pcx := by
  rcases h with h | ⟨e, he, h⟩
  · exact .inl h
  · exact .inr ⟨e, hP e he, h⟩

/-- The trace of a thread whose local steps lead from `t0` to an instruction at `t` that performs
one event satisfying `P` and then reaches an `exit` at `pcx`. -/
theorem oneThenExit_of_run {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {t0 t : TState} {m : Tmpl} {P : Event → Prop} {pcx : Nat} {tr : List Event}
    {o : Option TState}
    (htau : ∀ e l o, Run K A L g t0 (e :: l) o → Run K A L g t (e :: l) o)
    (hev : out K A L g t = .ev m)
    (hP : ∀ e o, Fires t.pc m e o →
      P e ∧ ∃ t2, o = some t2 ∧ out K A L g t2 = .ev .exit ∧ t2.pc = pcx)
    (h : Run K A L g t0 tr o) : OneThenExit tr P pcx := by
  rcases tr with _ | ⟨e, l⟩
  · exact .inl rfl
  · obtain ⟨hPe, hl⟩ := run_shape hev hP (htau _ _ _ h)
    rcases hl with rfl | rfl
    · exact .inr ⟨e, hPe, .inl rfl⟩
    · exact .inr ⟨e, hPe, .inr rfl⟩

/-- The need of a masked warp collective for lane `l` of its member mask. -/
theorem mask_need' {L : Launch} {X : Execution} {Q V : Type} (c : Kind → Option (WarpPart Q V))
    {e : EvId} {pc : Nat} {k : Kind} {p : WarpPart Q V} {l : Nat} (he : X.get e = some ⟨pc, k⟩)
    (hK : KindNeeds L X k e = maskNeeds L c X e) (hc : c k = some p) (hl : l < 32)
    (hb : p.mask.testBit l = true) :
    Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
      MaskWait L c X (warpLane L e.1 l, j) e) ∈ Needs L X e := by
  simp only [Needs, he, hK, maskNeeds, Option.bind_some, hc]
  exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr hl, hb⟩, rfl⟩

/-- A masked warp collective that is the first event of its thread has not returned when lane `l`
of its mask runs one event of the same class and member mask with other qualifiers and then exits:
no event of that lane is the lane's event of the instance, and its exit follows its own event of
the class. -/
theorem mask_blocked {Q V : Type} (c : Kind → Option (WarpPart Q V)) (hexit : c .exit = none)
    {L : Launch} {K : Kernel} {Y : Execution} (hd : DependencyOk L K Y) {g pc pcx : Nat} {k : Kind}
    {p : WarpPart Q V} (he : Y.get (g, 0) = some ⟨pc, k⟩)
    (hK : KindNeeds L Y k (g, 0) = maskNeeds L c Y (g, 0)) (hc : c k = some p)
    (hret : Returned Y (g, 0)) {l : Nat} (hl : l < 32) (hb : p.mask.testBit l = true)
    (hother : OneThenExit (Y.tr (warpLane L g l))
      (fun e => ∃ p', c e.kind = some p' ∧ p'.mask = p.mask ∧ p'.qual ≠ p.qual) pcx) : False := by
  obtain ⟨x, -, j, rfl, -, m, n, q, hf, hsrc⟩ := hd.ready _ hret _ (mask_need' c he hK hc hl hb)
  obtain ⟨⟨⟨ev, p0, hev, hcp, hm⟩, hcount⟩, ev', p1, hev', hc', hq⟩ := hf
  rw [he] at hev hev'
  cases hev; cases hev'
  rw [hc] at hcp hc'
  cases hcp; cases hc'
  simp only [List.take_zero, List.countP_nil] at hcount
  subst hm hq hcount
  set h := warpLane L g l
  rcases hsrc with ⟨⟨⟨ev2, p2, hev2, hc2, hm2⟩, hcount2⟩, ev3, p3, hev3, hc3, hq3⟩ |
    ⟨-, ⟨pc', hx⟩, hcount2⟩
  · rw [hev2] at hev3; cases hev3
    rw [hc2] at hc3; cases hc3
    rcases hother with hnil | ⟨e0, ⟨p', hp', -, hq'⟩, htr | htr⟩
    · simp [Execution.get, hnil] at hev2
    · rcases j with _ | j <;> simp [Execution.get, htr] at hev2
      subst hev2; rw [hp'] at hc2; cases hc2; exact hq' hq3
    · rcases j with _ | _ | j <;> simp [Execution.get, htr] at hev2
      · subst hev2; rw [hp'] at hc2; cases hc2; exact hq' hq3
      · subst hev2; rw [hexit] at hc2; cases hc2
  · rcases hother with hnil | ⟨e0, ⟨p', hp', hm', -⟩, htr | htr⟩
    · simp [Execution.get, hnil] at hx
    · rcases j with _ | j <;> simp [Execution.get, htr] at hx
      subst hx; rw [hexit] at hp'; cases hp'
    · rcases j with _ | _ | j <;> simp [Execution.get, htr] at hx
      · subst hx; rw [hexit] at hp'; cases hp'
      · simp [htr, hp', hm'] at hcount2

end Warp

section Empty
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- The empty execution is maximal when no possible execution has a thread event. -/
theorem empty_maximal (hl : L.clusterGridValid) (hA : ∀ a ∈ A, a.wf L mem0 Execution.empty)
    (hnil : ∀ Y, Consistent L K A mem0 Y → ∀ g < L.threads, Y.tr g = []) :
    Maximal L K A mem0 Execution.empty := by
  refine ⟨consistent_empty hl hA, fun Y hY _ => ?_⟩
  have hall : ∀ g, Y.tr g = [] := by
    intro g
    by_cases hg : g < L.threads
    · exact hnil Y hY g hg
    · exact hY.outside g (by omega)
  have hn : Y.NoTma := by
    intro e pc kind he
    simp [Execution.get, hall] at he
  rw [hn.size_eq hY]
  simp [hall]

/-- The empty execution of a launch with a thread is not complete. -/
theorem empty_not_complete (hl : L.clusterGridValid) (hL : 0 < L.threads) :
    ¬ Complete L Execution.empty := by
  have hn : Execution.empty.NoTma := by
    intro e pc kind he
    simp [Execution.get, Execution.empty] at he
  intro hc
  have hclc := (consistent_empty (K := { name := "", params := [], code := [] }) (A := [])
    (mem0 := fun _ => none) hl (by simp)).clc
  obtain ⟨pc, h⟩ := (hn.complete_iff L hclc).mp hc 0 hL
  simp [Execution.empty] at h

/-- The deadlock statement: a possible execution that cannot grow and is not complete. -/
theorem empty_deadlock (hl : L.clusterGridValid) (hA : ∀ a ∈ A, a.wf L mem0 Execution.empty)
    (hL : 0 < L.threads) (hnil : ∀ Y, Consistent L K A mem0 Y → ∀ g < L.threads, Y.tr g = []) :
    Maximal L K A mem0 Execution.empty ∧ ¬ Complete L Execution.empty :=
  ⟨empty_maximal hl hA hnil, empty_not_complete hl hL⟩

/-- The deadlock statement from bounds: when every possible execution has at most `n` counted
events per thread, issues no linear copy and is not complete, a possible execution that cannot
grow and is not complete exists (a largest one, `bounded_largest_extension`). -/
theorem deadlock_of_bound (hl : L.clusterGridValid) (hA : ∀ a ∈ A, a.wf L mem0 Execution.empty)
    (n : Nat)
    (hcount : ∀ Y, Consistent L K A mem0 Y → ∀ g < L.threads, (Y.tr g).countP Event.counts ≤ n)
    (hcopy : ∀ Y, Consistent L K A mem0 Y → ∀ i s, ¬ Y.Copy i s)
    (hinc : ∀ Y, Consistent L K A mem0 Y → ¬ Complete L Y) :
    ∃ X, Maximal L K A mem0 X ∧ ¬ Complete L X := by
  obtain ⟨Y, hY, hle, hmax⟩ := bounded_largest_extension
    (terminates_of_count n hcount fun Y hY i s h => (hcopy Y hY i s h).elim)
    (consistent_empty hl hA)
  exact ⟨Y, ⟨hY, fun Z hZ hYZ => hmax Z hZ (Execution.le_trans hle hYZ)⟩, hinc Y hY⟩

end Empty

end

end PTX.Tests.Progress
