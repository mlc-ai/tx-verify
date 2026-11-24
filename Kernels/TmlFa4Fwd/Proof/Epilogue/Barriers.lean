-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Glue
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ledger
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's barrier events

Every event at an output pc is an event of a lane of warp 13 after its prologue, at the site of
the machine state before it (`output_event`). Its operands are then the shape table's:

* `wait_operands`, `arrive_operands`: the ready polls wait on the stage's ready barrier with
  parity zero, and the frees arrive once, with release, on the stage's free barrier;
* `free_unique`: a lane frees a stage at most once (the ledger's arrival count);
* `ready_before_free`: before a lane frees a stage, its poll of that stage succeeded (a count of
  the successful polls along the machine's run). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **An event of a lane of warp 13 after its prologue** other than undefined behaviour has the
shape of the site of its state, and sits at that site. -/
theorem event_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {j : Nat} {e : Event} (hj5 : 5 ≤ j)
    (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ d n, Frame.stateAt (thread p L) X g j = some (some (inj p L g d n)) ∧
      Fits p L g d (n .shfl) (n .vote) ∧ Ev p L g d e ∧ e.pc = d.site.pc := by
  obtain ⟨d, n, hσ, hF, hE⟩ :=
    good_at hp hX hj5 he hub (good_all hp hX (Frame.lt_of_get hX he) hw j)
  obtain ⟨-, o, hf⟩ := fired hp hX he hσ
  exact ⟨d, n, hσ, hF, hE, Code.fired_pc hf⟩

/-- **An event of a lane of warp 13 at an output pc** other than undefined behaviour is after its
prologue, at the site of its state. -/
theorem output_event (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hlo : 2768 ≤ e.pc) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    5 ≤ j ∧
      ∃ d n, Frame.stateAt (thread p L) X g j = some (some (inj p L g d n)) ∧
      Fits p L g d (n .shfl) (n .vote) ∧ Ev p L g d e ∧ e.pc = d.site.pc := by
  have hj5 : 5 ≤ j := by
    by_contra h
    obtain ⟨-, -, -, hpc, -⟩ := prologue_ev hp hX (by omega) he hub
      (good_all hp hX (Frame.lt_of_get hX he) hw j)
    omega
  exact ⟨hj5, event_site hp hX hw hj5 he hub⟩

theorem readyLoc_inj {st st' : Fin 2} (h : readyLoc L g st = readyLoc L g st') : st = st' := by
  simp only [readyLoc, Loc.mk.injEq] at h
  exact Fin.ext (by omega)

/-- A wait of a lane of warp 13 after its prologue is a poll of a stage's ready barrier. -/
theorem wait_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {j pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {sc : MbarScope} (hj5 : 5 ≤ j) (he : X.get (g, j) = some ⟨pc, .wait target q ok acq sc⟩) :
    ∃ st : Fin 2, pc = (Site.ready st).pc ∧ target = readyLoc L g st ∧ q = 0 ∧ acq = true ∧
      sc = .cta := by
  obtain ⟨⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩,
    cn, -, -, hE, hpc⟩ := event_site hp hX hw hj5 he (by rintro _ _ ⟨⟩)
  cases s <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self,
    Bool.false_eq_true] at hE
  case ready st =>
    obtain ⟨ok', hk⟩ := hE
    simp only [Kind.wait.injEq] at hk
    obtain ⟨h1, h2, -, h4, h5⟩ := hk
    exact ⟨st, hpc, h1, h2, h4, h5⟩

/-- An arrival of a lane of warp 13 after its prologue frees a stage: one arrival, with release,
on the stage's free barrier. -/
theorem arrive_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {j pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {sc : MbarScope} (hj5 : 5 ≤ j) (he : X.get (g, j) = some ⟨pc, .arrive target tx n rel sc⟩) :
    ∃ d cn, Frame.stateAt (thread p L) X g j = some (some (inj p L g d cn)) ∧
      ∃ st : Fin 2, d.site = .free st ∧
      pc = (Site.free st).pc ∧ target = freeLoc L g st ∧ tx = 0 ∧ n = 1 ∧ rel = true ∧
      sc = .cta := by
  obtain ⟨⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩,
    cn, hσ, -, hE, hpc⟩ := event_site hp hX hw hj5 he (by rintro _ _ ⟨⟩)
  cases s <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self,
    Bool.false_eq_true] at hE
  case free st =>
    simp only [Kind.arrive.injEq] at hE
    obtain ⟨h1, h2, h3, h4, h5⟩ := hE
    exact ⟨_, cn, hσ, st, rfl, hpc, h1, h2, h3, h4, h5⟩

/-! ### Counts along the thread -/

/-- **The ledger at a role state**: the thread's events of each class the output warp counts
before the state are the state's counts. -/
theorem ledger_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n))) :
    ((X.tr g).take k).countP isStore = stores d ∧ ((X.tr g).take k).countP isCommit = commits d ∧
      ((X.tr g).take k).countP isWait = drains d ∧ ((X.tr g).take k).countP isArrive = frees d ∧
      ∀ st, okPolls (readyLoc L g st) ((X.tr g).take k) = acqd st d ∧
        arrivals (freeLoc L g st) ((X.tr g).take k) = freedAt st d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (fits hp hX hg hw hσ).2
  exact ⟨(count hσ .store).trans h1, (count hσ .commit).trans h2, (count hσ .wait).trans h3,
    (count hσ .arrive).trans h4, fun st => ⟨(count hσ (.poll st)).trans (h5 st).1,
      (count hσ (.freed st)).trans (h5 st).2⟩⟩

theorem ite01 {c : Prop} [Decidable c] : (if c then 1 else 0 : Nat) ≤ 1 := by split <;> omega

/-- **The output warp's ledger of each stage's hand-off**: before a role state, a lane has polled
stage `st`'s ready barrier successfully at most once and arrived on the stage's free barrier no
more often. These are the consumer and producer counts of the unit hand-offs of the ready and
free barriers (`MbarRing.UnitHandoff`), in the library's counts. -/
theorem stage_budget (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n))) (st : Fin 2) :
    arrivals (freeLoc L g st) ((X.tr g).take k) ≤ okPolls (readyLoc L g st) ((X.tr g).take k) ∧
      okPolls (readyLoc L g st) ((X.tr g).take k) ≤ 1 := by
  obtain ⟨-, -, -, -, hPoll⟩ := ledger_at hp hX hg hw hσ
  obtain ⟨h1, h2⟩ := hPoll st
  rw [h1, h2]
  have := st.isLt
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  fin_cases st <;> cases s <;> (try cases ‹Scan›) <;> (try cases ‹Bool›) <;>
    simp [freedAt, acqd, frees, written, Scan.late]
  all_goals first | omega | exact ite01

theorem take_succ {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
  rw [List.take_add_one]; simp [show (X.tr g)[k]? = some e from he]

/-- **A lane frees a stage at most once**: the ledger's arrival count. -/
theorem free_unique (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {st : Fin 2} {i j : Nat} {di dj : D} {e : Event}
    (hij : i < j)
    {ni nj : Cls → Nat} (hσi : Frame.stateAt (thread p L) X g i = some (some (inj p L g di ni)))
    (hσj : Frame.stateAt (thread p L) X g j = some (some (inj p L g dj nj)))
    (hsi : di.site = .free st) (hsj : dj.site = .free st) (he : X.get (g, i) = some e)
    (ha : isArrive e = true) : False := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, -, -, ci, -⟩ := ledger_at hp hX hg hw hσi
  obtain ⟨-, -, -, cj, -⟩ := ledger_at hp hX hg hw hσj
  have hsucc := congrArg (List.countP isArrive) (take_succ he)
  have hmono := Flow.countP_take_mono isArrive (X.tr g) (show i + 1 ≤ j by omega)
  simp only [List.countP_append, List.countP_singleton, ha, ↓reduceIte] at hsucc
  simp only [frees, hsi, hsj] at ci cj
  omega

/-- Before a state that has passed stage `st`'s ready poll, the poll succeeded. -/
theorem ready_before (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {st : Fin 2} {i : Nat} {d : D} {e : Event}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g i = some (some (inj p L g d n)))
    (h1 : acqd st d = 1)
    (he : X.get (g, i) = some e) :
    ∃ j < i, 5 ≤ j ∧ ∃ pc q acq sc,
      X.get (g, j) = some ⟨pc, .wait (readyLoc L g st) q true acq sc⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, -, -, -, hPoll⟩ := ledger_at hp hX hg hw hσ
  have c := (hPoll st).1
  rw [h1] at c
  obtain ⟨j, pc, q, acq, sc, hj, hj'⟩ := exists_okPoll
    (show 0 < okPolls (readyLoc L g st) ((X.tr g).take i) by omega)
  refine ⟨j, hj, ?_, pc, q, acq, sc, hj'⟩
  by_contra h
  obtain ⟨-, -, -, -, hcls⟩ := prologue_ev hp hX (by omega) hj' (by intro _ _ h; simp at h)
    (good_all hp hX hg hw j)
  have := hcls (.poll st) (by simp [StartCls])
  simp [cls, sourceWaitSuccess] at this

/-- **Before a lane frees a stage, its poll of the stage's ready barrier succeeded.** -/
theorem ready_before_free (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {st : Fin 2} {i : Nat} {d : D} {e : Event}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g i = some (some (inj p L g d n)))
    (hs : d.site = .free st)
    (he : X.get (g, i) = some e) :
    ∃ j < i, 5 ≤ j ∧ ∃ pc q acq sc,
      X.get (g, j) = some ⟨pc, .wait (readyLoc L g st) q true acq sc⟩ :=
  ready_before hp hX hw hσ (by simp [acqd, hs]) he

/-- **A lane's first lookup** reads the word of its own lane's cumulative query offset, inside the
batch. -/
theorem first_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {j : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, j) = some ⟨2776, .rd a bs⟩) :
    laneOf L g ≤ p.batch ∧ a = wordAcc (p.cuQBase + 4 * laneOf L g) := by
  obtain ⟨-, d, cn, -, hF, hE, hpc⟩ := output_event (p := p) hp hX hw he
    (by show 2768 ≤ 2776; decide) (by rintro _ _ ⟨⟩)
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hpc
  cases s <;> simp only [Ev, isStore, reduceCtorEq, exists_false, Bool.false_eq_true] at hE
  all_goals try cases ‹Scan›
  all_goals try (simp [Site.pc, Scan.word] at hpc; done)
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨r, n0, v0, -, hR, -, -, -, hrd⟩ := hF
  have hr0 : r = 0 := by have := hR.2; simp_all
  subst hr0
  have hle := reqN_le hp hl hrd
  simp only [reqN, ↓reduceIte] at hle
  refine ⟨hle, ?_⟩
  rcases hE with ⟨bs', hk⟩ | h
  swap
  · exact h.elim
  simp only [Kind.rd.injEq] at hk
  rw [hk.1]
  congr 1
  simp only [rdAddr, laneW_W]
  exact addrU_toNat hp hle

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
