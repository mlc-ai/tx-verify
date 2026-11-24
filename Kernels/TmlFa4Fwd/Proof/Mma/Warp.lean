-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
public import Lemmas.Flow.AllocTmpl
public import Lemmas.Flow.Step.Alloc
public import Lemmas.Kernel.ElectSource
public import Lemmas.Kernel.Source.WarpColl
public import Lemmas.Step.WarpAppend
public import Lemmas.Step.WarpShfl
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Kernels.TmlFa4Fwd.Proof.Mma.FitsNext
import Kernels.TmlFa4Fwd.Proof.Mma.RefNext
import Kernels.TmlFa4Fwd.Proof.Mma.Startup
import Kernels.TmlFa4Fwd.Proof.Mma.Steps
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The lanes of the MMA warp are followed

Every lane of warp 12 is followed by the thread machine, and every state holds the reference
invariant (`good`): `Frame.followedOn` restricted to the lanes of warp 12, with the order by the
warp collectives up to an event (`μ`), as for the output warp.

**Reference invariant** (`Ref`). At a startup state the startup's words and counts (`StartAt` with
the warp index 12); at the allocation prefix (`S`) the startup's three shuffles and no ballot; at
a role state, unless an event so far was undefined behaviour, the ledger's closed forms
(`RefCounts` on the MMA classes of the thread's ledger, `rc`) and the reference values (`MFits`).
The guard is sound because no event of a thread follows an undefined-behaviour event
(`ub_last`): before every event the guard holds (`ub_zero`). The MMA warp's commit sites
continue on any event, so a commit that faults would break the commit counts.

**Sources.** What an event returns comes from its source (plan G5): the scheduler's loads from the
launch words (the output warp's `expect_word`, `expect_q`; the used-K word by `inputReadValue`),
the scan's shuffles and ballot from the lanes of the warp at the same instance (the output warp's
`expect_shfl_of_src`, `expect_vote_of_bits`), a pipeline broadcast from lane 0's operand, which
every shuffle site of the warp sends as a word (`sent_word`), and an election from the lane's own
earlier election (`elect_leader`).

**Positions.** The source lane of a collective is at the same instance; that it did not return
before it, and that it is at the same site, follows from the positions of the warp's common
sequence: the startup's three shuffles, the broadcast before the scan, the output warp's first
pass shifted by one, the pipeline's broadcasts, and the output warp's second pass shifted by one
plus the full pipeline's broadcasts of the picked tile (`pipeN`), which is the same on every lane
of the CTA (`shift_cmp`, `sh_band`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked chosen)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The reference invariant -/

/-- The lanes of warp 12. -/
abbrev Q (L : Launch) (g : Nat) : Prop := InWarp L 12 g

/-- The MMA warp's counts before its first role state. -/
def ZeroC (n : Cls → Nat) : Prop :=
  (∀ l, n (.mma (.acquire l)) = 0 ∧ n (.mma (.commit l)) = 0) ∧ n (.mma .won) = 0 ∧
    n (.mma .lost) = 0

/-- **The reference invariant of a lane of warp 12.** -/
def Ref (p : Params) (L : Launch) (g : Nat) :
    (Startup.D ⊕ (Σ i, (frag p L g i).D)) × (Cls → Nat) → Prop
  | (.inl s, n) => StartAt L 12 s n ∧ n .vote = 0 ∧ ZeroC n
  | (.inr ⟨.mma, .inl _⟩, n) => n .shfl = 3 ∧ n .vote = 0 ∧ ZeroC n
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, n) =>
      n .ub = 0 → RefCounts p L g (d, rc n) ∧ MFits p L g d (n .shfl) (n .vote)
  | (.inr ⟨.epilogue, _⟩, _) | (.inr ⟨.correction, _⟩, _) | (.inr ⟨.loader _, _⟩, _)
  | (.inr ⟨.stub _, _⟩, _) | (.inr ⟨.softmax, _⟩, _) => False

/-- Lane `g`'s state before its `k`-th event is followed and holds the reference invariant. -/
abbrev Good (p : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  Frame.FollowedAt (thread p L) (Ref p L) X g k

/-- The induction hypothesis: the lanes of warp 12 are followed at the positions with at most `n`
collectives before them. -/
abbrev GoodUpTo (p : Params) (L : Launch) (X : Execution) (n : Nat) : Prop :=
  Proof.GoodUpTo (Ref p L) X 12 n

theorem ref_init : Ref p L g (thread p L g).init := by
  show Ref p L g (.inl ⟨.sh 0, 0, 0, 0⟩, fun _ => 0)
  exact ⟨⟨rfl, rfl, by simp, by simp⟩, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl⟩

/-! ### Events at the MMA warp's states -/

/-- An event of no class the MMA warp's reference counts. -/
def Quiet (L : Launch) (g : Nat) (e : Event) : Prop :=
  Execution.isShfl e = false ∧ isFullVote e = false ∧ e.kind ≠ .exit ∧
    ∀ c, Proof.cls L g (Cls.mma c) e = false

/-- **The allocation prefix's events are quiet**: the `setmaxnreg`, the allocation request and
the address store, or undefined behaviour. -/
theorem s_quiet (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {s : Start} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inr ⟨.mma, .inl s⟩, n))) :
    Quiet L g e := by
  obtain ⟨t, ins, o, -, hi, hc, hf⟩ :=
    strict_fired_site hp hX he hσ rfl
  have key : ∀ tm : Tmpl, (AllocT tm ∨ ∃ inc n, tm = SetMaxNReg.tmpl t inc n) →
      Fires (Start.pc s) tm e o → Quiet L g e := by
    intro tm htm hf
    rcases htm with htm | ⟨inc, n, rfl⟩
    · cases tm with
      | ub f =>
        simp only [Fires] at hf
        obtain ⟨rfl, -⟩ := hf
        exact ⟨rfl, rfl, by simp, fun c => by cases c <;> rfl⟩
      | tc k u =>
        cases k <;> simp only [AllocT] at htm
        simp only [Fires] at hf
        obtain ⟨rfl, -⟩ := hf
        exact ⟨rfl, rfl, by simp, fun c => by cases c <;> rfl⟩
      | tcAllocStore dst u =>
        simp only [Fires] at hf
        obtain ⟨_, -, rfl, -⟩ := hf
        exact ⟨rfl, rfl, by simp, fun c => by cases c <;> rfl⟩
      | _ => exact htm.elim
    · simp only [SetMaxNReg.tmpl] at hf
      split at hf <;> simp only [Fires] at hf
      · obtain ⟨_, rfl, -⟩ := hf
        exact ⟨rfl, rfl, by simp, fun c => by cases c <;> rfl⟩
      · obtain ⟨rfl, -⟩ := hf
        exact ⟨rfl, rfl, by simp, fun c => by cases c <;> rfl⟩
  cases s with
  | set =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1907)
    exact key _ (.inr ⟨_, _, rfl⟩) hf
  | alloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1909)
    exact key _ (.inl allocT) hf
  | wr =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1909)
    exact key _ (.inl allocT) hf
  | enter => exact absurd hi.2 (by simp [Start.exit])

/-- **An event at a role state of the MMA warp has its site's shape**, and the role's machine
fires it from that state. -/
theorem mfired (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {d : D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) :
    Ev p L g d e ∧ ∃ o, (code p L g (ent p L)).toMachine.Fired (some d) e o := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := strict_fired hp hX he hσ rfl
  have hf' : (code p L g (ent p L)).toMachine.Fired (some d) e o := hf
  exact ⟨(Code.Shape.fired (shape hp) (stepAt hp hg) hf').1, o, hf'⟩

theorem next_minj (d : D) (n : Cls → Nat) (e : Event) :
    (thread p L g).next (minj p L g d n) e = ((code p L g (ent p L)).next d e).map
      (Option.map fun d' => minj p L g d' (Code.bump (Proof.cls L g) n e)) := by
  show ((((code p L g (ent p L)).next d e).map (Option.map fun d' =>
    (Sum.inr ⟨(), d'⟩ : (M p L g).D))).map (Option.map fun d' =>
      (Sum.inr ⟨Role.mma, d'⟩ : (glued p L g).D))).map
        (Option.map fun d' => (d', Code.bump (Proof.cls L g) n e)) = _
  rcases (code p L g (ent p L)).next d e with _ | _ | d' <;> rfl

/-- A followed state of a lane of warp 12 before an event that is no undefined behaviour: a
startup state, an allocation-prefix state, or a role state with its reference invariant. -/
theorem good_cases (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Good p L X g j) :
    (∃ s n, Frame.stateAt (thread p L) X g j = some (some (.inl s, n)) ∧
        StartAt L 12 s n ∧ n .vote = 0 ∧ ZeroC n) ∨
      (∃ s n, Frame.stateAt (thread p L) X g j = some (some (.inr ⟨.mma, .inl s⟩, n)) ∧
        n .shfl = 3 ∧ n .vote = 0 ∧ ZeroC n) ∨
      (∃ d n, Frame.stateAt (thread p L) X g j = some (some (minj p L g d n)) ∧ n .ub = 0 ∧
        RefCounts p L g (d, rc n) ∧ MFits p L g d (n .shfl) (n .vote)) := by
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub hG
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact .inl ⟨s, n, hσ, hR⟩
  · exact hR.elim
  · rcases d with s | ⟨⟨⟩, d⟩
    · exact .inr (.inl ⟨s, n, hσ, hR⟩)
    · have h0 := ub_zero hX he hσ
      exact .inr (.inr ⟨d, n, hσ, h0, hR h0⟩)
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-! ### Steps -/

theorem mfits_three {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) : 3 ≤ ns := by
  cases h : d.site.early
  · obtain ⟨h1, h2, -⟩ := mfits_main h hF
    have := Epilogue.fits_three h2
    omega
  · simp only [MFits, h, ↓reduceIte] at hF
    omega

/-- A role state of a lane of warp 12 before an event is past the startup's three shuffles. -/
theorem role_three (hX : Consistent L kernel Assumptions.all m X) {h j : Nat} {e : Event}
    {r : Role} {d : (frag p L h r).D} {n : Cls → Nat} (he : X.get (h, j) = some e)
    (hσ : Frame.stateAt (thread p L) X h j = some (some (.inr ⟨r, d⟩, n)))
    (hR : Ref p L h (.inr ⟨r, d⟩, n)) : 3 ≤ n .shfl := by
  rcases r with _ | _ | _ | _ | r | _
  on_goal 6 => exact hR.elim
  · exact hR.elim
  · rcases d with s | ⟨⟨⟩, d⟩
    · exact hR.1.ge
    · exact mfits_three (hR (ub_zero hX he hσ)).2
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- What a startup shuffle of a lane of warp 12 returns. -/
theorem start_recv12 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {s : Startup.D}
    {n : Cls → Nat} {j : Fin 3} {a r : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl .idx a 0 31 r ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hS : StartAt L 12 s n) (hv : n .vote = 0) (hs : s.site = .sh j)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → Q L j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L) X j) :
    r = b32 (if j.val = 0 then L.sharedBase else 12) :=
  start_recv (fun _ => ref_init) (fun _ _ _ h => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ he hσ h => role_three hX he hσ h) hp hX hg hw he hσ hS hv hs hprev

theorem zeroC_bump {n : Cls → Nat} {e : Event} (hZ : ZeroC n)
    (hq : ∀ c, c ≠ .bar → Proof.cls L g (Cls.mma c) e = false) :
    ZeroC (Code.bump (Proof.cls L g) n e) := by
  obtain ⟨h1, h2, h3⟩ := hZ
  refine ⟨fun l => ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [Code.bump, hq (.acquire l) (by simp), h1]
  · simp [Code.bump, hq (.commit l) (by simp), h1]
  · simp [Code.bump, hq .won (by simp), h2]
  · simp [Code.bump, hq .lost (by simp), h3]

/-- The MMA warp's counts stay zero through the startup. -/
theorem zeroC_start {n : Cls → Nat} {e : Event}
    (hn : ∀ c, ¬ StartCls c → Code.bump (Proof.cls L g) n e c = n c) (hZ : ZeroC n) :
    ZeroC (Code.bump (Proof.cls L g) n e) := by
  obtain ⟨h1, h2, h3⟩ := hZ
  exact ⟨fun l => ⟨(hn _ (by simp [StartCls])).trans (h1 l).1,
    (hn _ (by simp [StartCls])).trans (h1 l).2⟩, (hn _ (by simp [StartCls])).trans h2,
    (hn _ (by simp [StartCls])).trans h3⟩

set_option maxHeartbeats 1000000 in
/-- **The startup steps a lane of warp 12 well**, into the MMA warp's allocation prefix after
the barrier. -/
theorem start_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {k : Nat} {s : Startup.D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hR : Ref p L g (.inl s, n))
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → Q L j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L) X j) :
    Frame.StepGood (thread p L) (Ref p L) g (.inl s, n) e :=
  start_step_of (Z := ZeroC) hp hX hg hw (by decide) (by decide) (fun _ => ref_init)
    (fun _ _ => rfl) (fun _ _ _ h => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ he hσ h => role_three hX he hσ h)
    (fun _ _ hn hZ => zeroC_start hn hZ)
    (fun s n e hb hS hv hZ hE hn => by
      obtain ⟨site, x1, x2, x3⟩ := s
      simp only at hb
      subst hb
      simp only [StartAt] at hS
      simp only [Startup.Ev] at hE
      obtain ⟨h3, h4, rfl, rfl⟩ := hS
      have e2 : Epilogue.scmpi .ne .b (Epilogue.andi (12#64) (-2)) 14 = true := by decide
      have e3 : Epilogue.scmpi .eq .b (12#64) 13 = false := by decide
      have e4 : Epilogue.scmpi .ne .b (12#64) 12 = false := by decide
      simp only [Code.enter, exit, Startup.enterOf, e2, e3, e4, ↓reduceIte, Gate, roleOf,
        beq_self_eq_true, Bool.and_self, Bool.false_eq_true]
      refine ⟨?_, (hn _ (by simp [StartCls])).trans hv, ?_⟩
      · obtain ⟨pc, kind⟩ := e
        simp only at hE
        subst hE
        simp [Code.bump, Proof.cls, Execution.isShfl, h3]
      · exact zeroC_start hn hZ)
    he hσ hR hprev

/-- The counts of the role's first state. -/
theorem refc_init {n : Cls → Nat} (hZ : ZeroC n) :
    RefCounts p L g (⟨.bar1, {}⟩, rc n) := by
  obtain ⟨h1, h2, h3⟩ := hZ
  refine ⟨0, false, ⟨fun _ => rfl, fun h => by simp [Site.ord] at h,
    fun h => by simp [Site.ord] at h, fun h => by simp [Site.ord] at h, fun o => ?_,
    fun o => by simp [(h1 _).2], by simp [h2], by simp [h3, electAll, pq, Site.ord], rfl⟩,
    by simp [Site.ord, cmQ]⟩
  simp only [(h1 _).1, Site.ord]
  simp [acqAt, pq, ringAcq, ringCount]
  omega

/-- **The allocation prefix steps a lane of warp 12 well**, into the role's first state. -/
theorem s_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {s : Start} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inr ⟨.mma, .inl s⟩, n)))
    (hR : Ref p L g (.inr ⟨.mma, .inl s⟩, n)) :
    Frame.StepGood (thread p L) (Ref p L) g (.inr ⟨.mma, .inl s⟩, n) e := by
  obtain ⟨hs3, hv, hZ⟩ := hR
  obtain ⟨q1, q2, -, q4⟩ := s_quiet hp hX he hσ
  have hZ' := zeroC_bump hZ fun c _ => q4 c
  have hs' : Code.bump (Proof.cls L g) n e .shfl = 3 := by simp [Code.bump, Proof.cls, q1, hs3]
  have hv' : Code.bump (Proof.cls L g) n e .vote = 0 := by simp [Code.bump, Proof.cls, q2, hv]
  cases s <;>
    refine ⟨by simp [Code.glue, S], fun σ' h => ?_⟩ <;>
    simp only [Code.glue, S, Option.map_some, Option.some.injEq, reduceCtorEq,
      Option.map_none] at h <;> subst h
  · exact ⟨hs', hv', hZ'⟩
  · split
    · exact ⟨hs', hv', hZ'⟩
    · intro _
      refine ⟨refc_init hZ', ?_⟩
      simp [MFits, Site.early, hs', hv']
  · intro _
    refine ⟨refc_init hZ', ?_⟩
    simp [MFits, Site.early, hs', hv']

/-- What an event at a role state returns is accepted by the site's return kind, when it is what
the reference says. -/
theorem accepts_of {d : D} {ns nv : Nat} {e : Event} (hF : MFits p L g d ns nv)
    (hE : MExpect p L g d ns e) (hev : Ev p L g d e) : (ret d).accepts e := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  have sched : (s.sched || s == .tiles false) = true → s.scan = true ∨ s = .q0 ∨ s = .q1 →
      (ret ⟨s, v⟩).accepts ⟨pc, kind⟩ := by
    intro hs hsc
    have hE' := mexpect_sched hs hE
    have hF' := (mfits_main (sched_early hs).1 hF).2.1
    rcases hsc with hsc | rfl | rfl
    · have hev' : Epilogue.Ev p L g (toE ⟨s, v⟩) ⟨pc, kind⟩ := by
        have := toE_eq hsc
        cases s <;> simp_all [Ev, Site.scan, toE]
      have hne := Epilogue.next_ne (ent := fun _ => .pred false) hF' hE'
      have hacc : (Epilogue.ret (toE ⟨s, v⟩)).accepts ⟨pc, kind⟩ := by
        by_contra hc
        exact hne ((Epilogue.stop_iff _ trivial hev').mpr hc)
      cases s <;> simp_all [Site.scan, ret, Epilogue.ret, toE, Site.epi]
    all_goals
      simp only [Ev] at hev
      rcases hev with ⟨bs, rfl⟩ | ⟨f, rfl⟩
      · simp only [Epilogue.Expect, toE, Site.epi] at hE'
        intro x hx
        simp only [Flow.recvAll, Flow.recv, hE', Option.toList, List.mem_singleton] at hx
        subst hx
        exact ⟨_, rfl⟩
      · intro x hx
        simp [Flow.recvAll, Flow.recv] at hx
  cases s with
  | word _ | down _ | up _ _ | total _ | vote _ | pre _ =>
    exact sched (by simp [Site.sched]) (.inl rfl)
  | tiles l => exact sched (by cases l <;> rfl) (.inl rfl)
  | q0 => exact sched rfl (.inr (.inl rfl))
  | q1 => exact sched rfl (.inr (.inr rfl))
  | uk =>
    simp only [Ev] at hev
    rcases hev with ⟨bs, rfl⟩ | ⟨f, rfl⟩
    · simp only [MExpect] at hE
      intro x hx
      simp only [Flow.recvAll, Flow.recv, hE, Option.toList, List.mem_singleton] at hx
      subst hx
      exact ⟨_, rfl⟩
    · intro x hx
      simp [Flow.recvAll, Flow.recv] at hx
  | bcast | sh _ =>
    simp only [Ev] at hev
    obtain ⟨r, ok, rfl⟩ := hev
    obtain ⟨x, rfl⟩ := hE
    intro y hy
    simp only [Flow.recvAll, Flow.recv, Option.toList, List.mem_singleton] at hy
    subst hy
    exact ⟨_, rfl⟩
  | _ => exact RetKind.accepts_none _

/-- **A role state steps well on an event that returns what the reference says**: the counts and
the reference values continue (`ref_next`, `mfits_next`); after an undefined-behaviour event the
invariant's guard is false. -/
theorem role_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hR : Ref p L g (minj p L g d n))
    (hexp : (∀ f, e.kind ≠ .ub f) →
      MExpect p L g d (n .shfl) e ∧ ExpectElect L g (d, rc n) e) :
    Frame.StepGood (thread p L) (Ref p L) g (minj p L g d n) e := by
  obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
  have hev := (mfired hp hX he hσ).1
  show (thread p L g).next (minj p L g d n) e ≠ some none ∧ _
  rw [next_minj]
  by_cases hub : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hub
    have hacc : (ret d).accepts e := fun v hv => by
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      simp [Flow.recvAll, Flow.recv] at hv
    have hne := next_ne_stop (ent := ent p L) hev hacc
    rcases hn : (code p L g (ent p L)).next d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd hn hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro h1
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      simp [Code.bump, Proof.cls] at h1
  · have hub' : ∀ f, e.kind ≠ .ub f := fun f h => hub ⟨f, h⟩
    obtain ⟨hME, hEl⟩ := hexp hub'
    have hacc := accepts_of hF hME hev
    obtain ⟨hne, hJ'⟩ := ref_next (ent := ent p L) hp hJ ⟨hacc, hEl⟩ hev hub'
    rcases hn : (code p L g (ent p L)).next d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd (Code.counted_next_none_iff.mpr hn) hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro _
      refine ⟨hJ' _ ((Code.counted_next _ _ _).trans (by rw [hn]; rfl)), ?_⟩
      have := mfits_next hF hME hev hJ hn
      have h1 : Code.bump (Proof.cls L g) n e .shfl = n .shfl + Epilogue.sh e := rfl
      have h2 : Code.bump (Proof.cls L g) n e .vote = n .vote + Epilogue.vt e := rfl
      rw [h1, h2]
      exact this

/-! ### Positions, by pass (`Band.lean`) -/

/-- `omega` with the choice's position unfolded. -/
local macro "omg" : tactic => `(tactic| ((try unfold nC at *); omega))

/-! ### Positions of the MMA warp's states -/

/-- The MMA warp's shuffle sites: the broadcast before the scan, the pipeline's broadcasts and the
scan's shuffles. -/
def Site.msh : Site → Bool
  | .bcast | .sh _ => true
  | s => s.epi.shfl

theorem pipeN_cta {h R : Nat} {bal : BitVec 64} (hc : g / L.block = h / L.block) :
    pipeN p L g R bal = pipeN p L h R bal := by
  unfold pipeN refV Bs blocks coords Epilogue.ctaW
  rw [hc]

theorem shAt_100 (r : Nat) : shAt 100 r = 6 * r + 8 := by
  simp [shAt, pq]
  omega

theorem pipeN_ge {R : Nat} {bal : BitVec 64} : 8 ≤ pipeN p L g R bal := by
  unfold pipeN
  rw [shAt_100]
  omega

theorem picked_cta {h R R' : Nat} {bal bal' : BitVec 64} (hc : g / L.block = h / L.block)
    (h1 : Picked p L g R bal) (h2 : Picked p L h R' bal') :
    R' = R ∧ bal' = bal ∧ pipeN p L h R' bal' = pipeN p L g R bal := by
  obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc h1).unique h2
  exact ⟨rfl, rfl, (pipeN_cta hc).symm⟩

/-- **Where a state of the scheduler or the end stands**: in the first pass before the CTA's
choice (strictly at the scan, the ballot and the end), its ballot the warp's first; in the
second pass after the choice and the full pipeline's broadcasts. -/
theorem mband {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) (he : d.site.early = false)
    (hpp : d.site.pipe = false) :
    d.v.ps + 4 ≤ ns ∧
    ((d.site.late = false ∧ d.v.ps = 0 ∧ (d.site.epi.ballot = true → nv = 0) ∧
      ∀ R bal, Picked p L g R bal → ns ≤ nC R bal + 1 ∧
        (eColl d.site.epi = true → ns ≤ nC R bal) ∧ ∀ l, d.site.epi ≠ .exit l) ∨
    (d.site.late = true ∧ 1 ≤ nv ∧ ∃ R bal, Picked p L g R bal ∧ d.v.ps = pipeN p L g R bal ∧
      nC R bal + 1 + pipeN p L g R bal ≤ ns ∧
      (eEnd d.site.epi = true → nC R bal + 8 + pipeN p L g R bal ≤ ns))) := by
  obtain ⟨h1, h2, -, h4, h5⟩ := mfits_main he hF
  have h3 := Epilogue.fits_three h2
  refine ⟨by omega, ?_⟩
  have hne : d.site.epi ≠ .start := by cases hs : d.site <;> simp_all [Site.epi, Site.early]
  have hpass : ePass d.site.epi = d.site.late := by
    cases hs : d.site <;> simp_all [Site.epi, Site.early, Site.pipe, ePass, Site.late]
  rcases eband h2 hne with ⟨hp1, hb, hk⟩ | ⟨hp2, hnv, R, bal, hPk, h6, h7⟩
  · have hl : d.site.late = false := hpass ▸ hp1
    have h0 := h5 hpp hl
    refine .inl ⟨hl, h0, hb, fun R bal hPk => ?_⟩
    obtain ⟨k1, k2, k3⟩ := hk R bal hPk
    refine ⟨by omg, fun h => by have := k2 h; omg, k3⟩
  · have hl : d.site.late = true := hpass ▸ hp2
    obtain ⟨R', bal', hPk', hps⟩ := h4 hl
    obtain ⟨rfl, rfl⟩ := hPk.unique hPk'
    refine .inr ⟨hl, hnv, R, bal, hPk, hps, by omg, fun h => by have := h7 h; omg⟩

/-- **Where a pipeline broadcast stands**: after the CTA's choice, before the full pipeline's
broadcasts. -/
theorem sh_band {d : D} {ns nv : Nat} {cn : Cnt → Nat} {k : Fin 14} (hs : d.site = .sh k)
    (hF : MFits p L g d ns nv) (hJ : RefCounts p L g (d, cn)) :
    ∃ R bal, Picked p L g R bal ∧ ns = 1 + d.v.ps + nC R bal ∧
      d.v.ps < pipeN p L g R bal ∧ nv = 1 := by
  have hpm : d.site.pmid := pmid_of (by rw [hs]; rfl)
  obtain ⟨R, bal, hC, hB⟩ := bs_ref hpm hF
  obtain ⟨h1, -, -, -, -⟩ := mfits_main hpm.2.1 hF
  obtain ⟨hPk, -, -, -, -, -, -, hns, hnv⟩ := hC
  refine ⟨R, bal, hPk, by omg, ?_, hnv⟩
  obtain ⟨r, w, hQ, -⟩ := hJ
  simp only at hQ
  rw [hQ.ps, pipeN, ← hB]
  have hpre := hQ.pre
  have hloop := hQ.loop
  have htail := hQ.tail
  rw [hs] at hpre hloop htail ⊢
  fin_cases k <;> simp only [Site.ord, List.getD] at hpre hloop htail ⊢ <;>
    simp only [shAt, pq] <;> norm_num at hpre hloop htail ⊢ <;> omega

/-- **The first pass comes before the pipeline and the second pass**: shifting the output warp's
counts of two lanes of one CTA keeps their order. -/
theorem shift {h : Nat} {d d' : D} {ns nv ns' nv' : Nat} (hc : g / L.block = h / L.block)
    (hF : MFits p L g d ns nv) (hF' : MFits p L h d' ns' nv')
    (he : d.site.early = false) (hpp : d.site.pipe = false) (hco : eColl d.site.epi = true)
    (he' : d'.site.early = false) (hpp' : d'.site.pipe = false)
    (hco' : eColl d'.site.epi = true) :
    (ns - 1 - d.v.ps < ns' - 1 - d'.v.ps → ns < ns') ∧
      (ns = ns' → ns - 1 - d.v.ps = ns' - 1 - d'.v.ps ∧ d'.site.late = d.site.late) := by
  obtain ⟨b0, b1 | b2⟩ := mband hF he hpp <;> obtain ⟨b0', b1' | b2'⟩ := mband hF' he' hpp'
  · obtain ⟨l1, p1, -⟩ := b1
    obtain ⟨l1', p1', -⟩ := b1'
    exact ⟨fun h => by omega, fun h => ⟨by omega, by rw [l1, l1']⟩⟩
  · obtain ⟨l1, p1, -, k1⟩ := b1
    obtain ⟨l2', -, R, bal, hPk, -, q1, -⟩ := b2'
    have := (k1 R bal (Epilogue.Picked.cta hc.symm hPk)).2.1 hco
    exact ⟨fun _ => by omega, fun h => by omega⟩
  · obtain ⟨l2, -, R, bal, hPk, p2, q1, -⟩ := b2
    obtain ⟨l1', p1', -, k1'⟩ := b1'
    have := (k1' R bal (Epilogue.Picked.cta hc hPk)).2.1 hco'
    exact ⟨fun h => by omega, fun h => by omega⟩
  · obtain ⟨l2, -, R, bal, hPk, p2, -⟩ := b2
    obtain ⟨l2', -, R', bal', hPk', p2', -⟩ := b2'
    obtain ⟨rfl, rfl, hN⟩ := picked_cta hc hPk hPk'
    rw [hN] at p2'
    exact ⟨fun h => by omega, fun h => ⟨by omega, by rw [l2, l2']⟩⟩

/-- The output warp's site of a scan shuffle determines the MMA site. -/
theorem epi_shfl_inj {s s' : Site} (hs : s.epi.shfl = true) (h : s'.epi = s.epi) : s' = s := by
  cases s <;> simp [Site.epi, Epilogue.Site.shfl] at hs <;> cases s' <;>
    simp_all [Site.epi]


theorem shfl_epi {s : Site} (hs : s.epi.shfl = true) :
    s.early = false ∧ s.pipe = false ∧ eColl s.epi = true := by
  cases s <;> simp_all [Site.epi, Epilogue.Site.shfl, Site.early, Site.pipe, eColl]

theorem exit_epi {s : Site} {l : Bool} (hs : s.epi = .exit l) :
    s.early = false ∧ s.pipe = false ∧ eColl s.epi = true ∧ eEnd s.epi = true := by
  cases s <;> simp_all [Site.epi, Site.early, Site.pipe, eColl, eEnd]

theorem msh_cases {s : Site} (hs : s.msh = true) :
    s = .bcast ∨ (∃ k, s = .sh k) ∨ s.epi.shfl = true := by
  cases s <;> simp_all [Site.msh]

/-- The output warp's reference values of a scheduler or end state, at its shifted count. -/
theorem efits {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) (he : d.site.early = false) :
    Epilogue.Fits p L g (toE d) (ns - 1 - d.v.ps) nv :=
  (mfits_main he hF).2.1

theorem early_ns {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) (he : d.site.early = true) :
    ns = 3 ∧ nv = 0 := by
  simp only [MFits, he, ↓reduceIte] at hF
  exact ⟨hF.1, hF.2.1⟩

theorem epi_vote {d : D} {l : Bool} (hs : d.site = .vote l) : (toE d).site = .vote l := by
  simp [toE, hs, Site.epi]

variable {h : Nat} {d d' : D} {ns nv ns' nv' : Nat}

/-- **A shuffle state comes before every ballot state with at least its ballot count.** -/
theorem mshfl_lt_vote {cn : Cnt → Nat} {l : Bool} (hc : g / L.block = h / L.block)
    (hF : MFits p L g d ns nv) (hJ : RefCounts p L g (d, cn)) (hs : d.site.msh = true)
    (hF' : MFits p L h d' ns' nv') (hs' : d'.site = .vote l) (hv : nv ≤ nv') : ns < ns' := by
  have he' : d'.site.early = false := by rw [hs']; rfl
  have hpp' : d'.site.pipe = false := by rw [hs']; rfl
  have hb' : d'.site.epi.ballot = true := by rw [hs']; rfl
  have hE' : eEnd d'.site.epi = true := by rw [hs']; rfl
  obtain ⟨b0', b'⟩ := mband hF' he' hpp'
  rcases msh_cases hs with hb | ⟨k, hk⟩ | hse
  · have := early_ns hF (by rw [hb]; rfl); omega
  · obtain ⟨R, bal, hPk, hns, hlt, hnv⟩ := sh_band hk hF hJ
    rcases b' with ⟨-, -, hb0, -⟩ | ⟨-, -, R', bal', hPk', -, -, h8⟩
    · have := hb0 hb'; omega
    · obtain ⟨rfl, rfl, hN⟩ := picked_cta hc hPk hPk'
      have := h8 hE'
      omg
  · obtain ⟨he, hpp, hco⟩ := shfl_epi hse
    have := Epilogue.shfl_lt_vote (efits hF he) (efits hF' he') hc hse (epi_vote hs') hv
    exact (shift hc hF hF' he hpp hco he' hpp' (by rw [hs']; rfl)).1 this

/-- **A shuffle state comes before every return.** -/
theorem mshfl_lt_exit {cn : Cnt → Nat} {l : Bool} (hc : g / L.block = h / L.block)
    (hF : MFits p L g d ns nv) (hJ : RefCounts p L g (d, cn)) (hs : d.site.msh = true)
    (hF' : MFits p L h d' ns' nv') (hs' : d'.site.epi = .exit l) : ns < ns' := by
  obtain ⟨he', hpp', hco', hE'⟩ := exit_epi hs'
  obtain ⟨b0', b'⟩ := mband hF' he' hpp'
  rcases msh_cases hs with hb | ⟨k, hk⟩ | hse
  · have := early_ns hF (by rw [hb]; rfl); omega
  · obtain ⟨R, bal, hPk, hns, hlt, hnv⟩ := sh_band hk hF hJ
    rcases b' with ⟨-, -, -, k1⟩ | ⟨-, -, R', bal', hPk', -, -, h8⟩
    · exact absurd hs' ((k1 R bal (Epilogue.Picked.cta hc hPk)).2.2 l)
    · obtain ⟨rfl, rfl, hN⟩ := picked_cta hc hPk hPk'
      have := h8 hE'
      omg
  · obtain ⟨he, hpp, hco⟩ := shfl_epi hse
    have hx := efits hF' he'
    simp only [Epilogue.Fits, toE, hs'] at hx
    have := Epilogue.shfl_lt_exit (efits hF he) hc hse hx
    exact (shift hc hF hF' he hpp hco he' hpp' hco').1 this

/-- **No lane returns before a ballot that another lane of its warp makes.** -/
theorem mvote_exit {l l' : Bool} (hc : g / L.block = h / L.block)
    (hF : MFits p L g d ns nv) (hs : d.site = .vote l)
    (hF' : MFits p L h d' ns' nv') (hs' : d'.site.epi = .exit l') (hv : nv' ≤ nv) : False := by
  have hx := efits hF' (exit_epi hs').1
  simp only [Epilogue.Fits, toE, hs'] at hx
  exact Epilogue.vote_exit (efits hF (by rw [hs]; rfl)) hc (epi_vote hs) hx hv

/-- **Two lanes at shuffle states with one shuffle count**: the scan's shuffle of one is the same
site of the other, at the same shifted count. -/
theorem mshfl_same {cn' : Cnt → Nat} (hc : g / L.block = h / L.block)
    (hF : MFits p L g d ns nv) (hse : d.site.epi.shfl = true)
    (hF' : MFits p L h d' ns' nv') (hJ' : RefCounts p L h (d', cn')) (hs' : d'.site.msh = true)
    (hn : ns = ns') : d'.site = d.site ∧ ns' - 1 - d'.v.ps = ns - 1 - d.v.ps := by
  obtain ⟨he, hpp, hco⟩ := shfl_epi hse
  obtain ⟨b0, b⟩ := mband hF he hpp
  rcases msh_cases hs' with hb | ⟨k, hk⟩ | hse'
  · have := early_ns hF' (by rw [hb]; rfl); omega
  · obtain ⟨R, bal, hPk, hns, hlt, hnv⟩ := sh_band hk hF' hJ'
    exfalso
    rcases b with ⟨-, -, -, k1⟩ | ⟨-, -, R', bal', hPk', hps, h7, -⟩
    · have := (k1 R bal (Epilogue.Picked.cta hc.symm hPk)).2.1 hco
      omg
    · obtain ⟨rfl, rfl, hN⟩ := picked_cta hc.symm hPk hPk'
      omg
  · obtain ⟨he', hpp', hco'⟩ := shfl_epi hse'
    obtain ⟨hE, -⟩ := (shift hc hF hF' he hpp hco he' hpp' hco').2 hn
    have := Epilogue.shfl_same (efits hF he) (efits hF' he') hc hse hse' hE
    exact ⟨epi_shfl_inj hse this, hE.symm⟩

/-- **Two ballot states of lanes of one CTA with one ballot count are at one site**, at the same
shifted count. -/
theorem mvote_same {l l' : Bool} (hc : g / L.block = h / L.block)
    (hF : MFits p L g d ns nv) (hs : d.site = .vote l)
    (hF' : MFits p L h d' ns' nv') (hs' : d'.site = .vote l') (hv : nv = nv') :
    d'.site = d.site ∧ ns' - 1 - d'.v.ps = ns - 1 - d.v.ps := by
  obtain ⟨h1, h2⟩ := Epilogue.vote_same (efits hF (by rw [hs]; rfl))
    (efits hF' (by rw [hs']; rfl)) hc (epi_vote hs) (epi_vote hs') hv
  refine ⟨?_, h2⟩
  simp only [toE, hs, hs', Site.epi, Epilogue.Site.vote.injEq] at h1
  rw [hs, hs', h1]

/-! ### The sources of the MMA warp's collectives -/

local macro "fin3" : tactic => `(tactic| (refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  simp_all [Execution.isShfl, isFullVote, voteClass, Site.msh]))

/-- The kind of event a site fires, as far as the collectives and the return go. -/
theorem mev_coll {d : D} {e : Event} (hev : Ev p L g d e) :
    (Execution.isShfl e = true → d.site.msh = true) ∧
      (isFullVote e = true → ∃ l, d.site = .vote l) ∧ (e.kind = .exit → ∃ l, d.site = .exit l) := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Ev] at hev
  case word k | down k | up k j | total k | vote k | pre k | tiles k =>
    obtain ⟨h1, h2, h3⟩ := Epilogue.ev_class hev
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := h1 h; simp_all [Site.msh, Site.epi, Site.toE]
    · obtain ⟨l, hl⟩ := h2 h; simp_all [Site.toE]
    · obtain ⟨l, hl⟩ := h3 h; simp_all [Site.toE]
  case bcast | sh => obtain ⟨_, _, rfl⟩ := hev; fin3
  case bar1 | bar2 | exit => subst hev; fin3
  case ldAlloc | relinq | dealloc => rcases hev with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> fin3
  case q0 | q1 | uk | wt | mw => rcases hev with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> fin3
  case eq | ep | ce => rcases hev with ⟨_, _, -, rfl⟩ | ⟨_, rfl⟩ <;> fin3
  case qk | pv => rcases hev with ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ <;> fin3
  case cm => rcases hev with ⟨_, rfl, -⟩ | ⟨_, rfl⟩ <;> fin3

/-- At a scan site the MMA warp's event is the output warp's of its scan state. -/
theorem ev_toE {d : D} {e : Event} (hs : d.site.scan = true) (hev : Ev p L g d e) :
    Epilogue.Ev p L g (toE d) e := by
  obtain ⟨s, v⟩ := d
  have := toE_eq hs
  cases s <;> simp_all [Ev, Site.scan, toE]

/-- **A followed lane of warp 12 at a ballot, a return, or a shuffle past the startup's is at a
role state.** -/
theorem role_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    {e : Event} (he : X.get (h, j) = some e) (hG : Good p L X h j)
    (hk : isFullVote e = true ∨ e.kind = .exit ∨
      (Execution.isShfl e = true ∧ 3 ≤ ((X.tr h).take j).countP Execution.isShfl)) :
    ∃ d n, Frame.stateAt (thread p L) X h j = some (some (minj p L h d n)) ∧
      RefCounts p L h (d, rc n) ∧ MFits p L h d (n .shfl) (n .vote) ∧ Ev p L h d e ∧
      ((X.tr h).take j).countP Execution.isShfl = n .shfl ∧
      ((X.tr h).take j).countP isFullVote = n .vote := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    rcases hk with h | h | ⟨h, -⟩ <;> simp [isFullVote, voteClass, Execution.isShfl] at h
  rcases good_cases hp hX he hub hG with ⟨s, n, hσ, hS, -⟩ | ⟨s, n, hσ, -⟩ |
    ⟨d, n, hσ, -, hJ, hF⟩
  · exfalso
    obtain ⟨h1, h2, h3, -⟩ := start_kind hS (start_fired hp hX he hσ).1
    have hc := (counts hσ).1
    rcases hk with h | h | ⟨h, h'⟩
    · rw [h1] at h; cases h
    · exact h2 h
    · have := h3 h; omega
  · exfalso
    obtain ⟨q1, q2, q3, -⟩ := s_quiet hp hX he hσ
    rcases hk with h | h | ⟨h, -⟩
    · rw [q2] at h; cases h
    · exact q3 h
    · rw [q1] at h; cases h
  · exact ⟨d, n, hσ, hJ, hF, (mfired hp hX he hσ).1, (counts hσ).1, (counts hσ).2⟩

/-- **Every shuffle of a followed lane of warp 12 sends a 32-bit word.** -/
theorem sent_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L h = 12) {j pc : Nat} {mode : ShflMode} {a r : Value} {b c : Nat}
    {o : Bool} (he : X.get (h, j) = some ⟨pc, .shfl mode a b c r o⟩) (hG : Good p L X h j) :
    ∃ x, a = .bits 32 x := by
  rcases good_cases hp hX he (by rintro _ _ ⟨⟩) hG with ⟨s, n, hσ, hS, -⟩ | ⟨s, n, hσ, -⟩ |
    ⟨d, n, hσ, -, hJ, hF⟩
  · have hE := (start_fired hp hX he hσ).1
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case sh i =>
      obtain ⟨r', ok', hk⟩ := start_sent hp hw hS rfl hE
      simp only [Kind.shfl.injEq] at hk
      exact ⟨_, hk.2.1⟩
    all_goals simp only [StartAt] at hS
    all_goals simp [Startup.Ev] at hE
  · exact absurd (s_quiet hp hX he hσ).1 (by simp [Execution.isShfl])
  · have hev := (mfired hp hX he hσ).1
    rcases msh_cases ((mev_coll hev).1 rfl) with hs | ⟨k, hs⟩ | hse
    · simp only [Ev, hs, Kind.shfl.injEq] at hev
      obtain ⟨_, _, -, h, -⟩ := hev
      exact ⟨_, h⟩
    · simp only [Ev, hs, Kind.shfl.injEq] at hev
      obtain ⟨_, _, -, h, -⟩ := hev
      exact ⟨_, h⟩
    · have hsc : d.site.scan = true := by
        obtain ⟨s, v⟩ := d; cases s <;> simp_all [Site.epi, Epilogue.Site.shfl, Site.scan]
      exact ⟨_, Epilogue.ev_opnd (ev_toE hsc hev)⟩

/-- **The source of a shuffle of a lane of warp 12 at a role state**: the source lane made the
shuffle of the same instance from a followed state, with the received value as its operand. -/
theorem mshfl_src (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {mode : ShflMode}
    {a recv : Value} {b c : Nat} {ok : Bool} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hJ : RefCounts p L g (d, rc n)) (hF : MFits p L g d (n .shfl) (n .vote))
    (IH : GoodUpTo p L X (n .shfl + n .vote)) :
    ∃ j pc' b' c' r' o',
      X.get (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) =
        some ⟨pc', .shfl mode recv b' c' r' o'⟩ ∧
      Good p L X (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j ∧
      ((X.tr (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)).take j).countP
        Execution.isShfl = n .shfl := by
  have hs := (mev_coll (mfired hp hX he hσ).1).1 rfl
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs, -⟩ := shfl_src hp hX hg hw he (counts hσ).1 IH
    (fun h j0 e0 _ hc he0 hv0 hG hs0 hc0 => by
      obtain ⟨d0, n0, -, -, hF0, hE0, hs0', hv0'⟩ := role_at hp hX he0 hG (.inl hv0)
      obtain ⟨l, hl⟩ := (mev_coll hE0).2.1 hv0
      simp only [Frame.cnt] at hs0 hc0
      have := mshfl_lt_vote hc.symm hF hJ hs hF0 hl (by omega)
      omega)
    (fun h kx pcx _ hc hx hG hsx hvx => by
      obtain ⟨dx, nx, -, -, hFx, hEx, hsx', -⟩ := role_at hp hX hx hG (.inr (.inl rfl))
      obtain ⟨l, hl⟩ := (mev_coll hEx).2.2 rfl
      simp only [Frame.cnt] at hsx
      have := mshfl_lt_exit hc.symm hF hJ hs hFx (by rw [hl]; rfl)
      omega)
  exact ⟨j, pc', b', c', r', o', hj, hG, hjs⟩

/-- Only a ballot site fires a ballot. -/
theorem ev_vote {d : D} {e : Event} {mk : Nat} {a : Bool} {b : BitVec 32} (hev : Ev p L g d e)
    (hk : e.kind = .vote mk a b) : ∃ l, d.site = .vote l := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases s
  case vote l => exact ⟨l, rfl⟩
  all_goals exfalso; simp [Ev, Site.toE, Epilogue.Ev] at hev

set_option maxHeartbeats 1000000 in
/-- **A ballot's bits are the predicates of all lanes at the same ballot**, in the output warp's
terms of their scan states. -/
theorem mvote_bits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {k pc mask : Nat} {a : Bool}
    {bv : BitVec 32} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .vote mask a bv⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hF : MFits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L X (n .shfl + n .vote)) :
    ∀ i < 32, ∃ di nvi, Epilogue.Fits p L (g - laneOf L g + i) (toE di)
        (n .shfl - 1 - d.v.ps) nvi ∧ (toE di).site = (toE d).site ∧
      bv.getLsbD i = Epilogue.votePred p L (g - laneOf L g + i) (toE di) := by
  have hev := (mfired hp hX he hσ).1
  have hsite : ∃ l, d.site = .vote l := ev_vote hev rfl
  obtain ⟨l, hl⟩ := hsite
  have hE0 := ev_toE (by rw [hl]; rfl) hev
  have hmask : mask = 2 ^ 32 - 1 := by
    simp only [Epilogue.Ev, toE, hl, Site.epi] at hE0
    obtain ⟨_, h⟩ := hE0
    simp only [Kind.vote.injEq] at h
    exact h.1
  subst hmask
  have h3 := mfits_three hF
  intro i hi
  exact vote_src (P := fun h b => ∃ di nvi, Epilogue.Fits p L h (toE di)
      (n .shfl - 1 - d.v.ps) nvi ∧ (toE di).site = (toE d).site ∧
        b = Epilogue.votePred p L h (toE di)) hp hX hg hw he (counts hσ).2 IH
    (fun h j1 e1 _ hc he1 hs1 hG hv1 hc1 => by
      simp only [Frame.cnt] at hv1 hc1
      obtain ⟨d1, n1, -, hJ1, hF1, hE1, hs1', hv1'⟩ :=
        role_at hp hX he1 hG (.inr (.inr ⟨hs1, by omega⟩))
      have := mshfl_lt_vote hc hF1 hJ1 ((mev_coll hE1).1 hs1) hF hl (by omega)
      omega)
    (fun h kx pcx _ hc hx hG hsx hvx => by
      simp only [Frame.cnt] at hsx hvx
      obtain ⟨dx, nx, -, -, hFx, hEx, -, hvx'⟩ := role_at hp hX hx hG (.inr (.inl rfl))
      obtain ⟨lx, hlx⟩ := (mev_coll hEx).2.2 rfl
      exact mvote_exit hc.symm hF hl hFx (by rw [hlx]; rfl) (by omega))
    (fun h j ej _ hc hej hfv hG hsj hcnt => by
      simp only [Frame.cnt] at hsj hcnt
      obtain ⟨di, ni, -, -, hFi, hEi, hsi, hvi⟩ := role_at hp hX hej hG (.inl hfv)
      obtain ⟨li, hli⟩ := (mev_coll hEi).2.1 hfv
      obtain ⟨hsite, hns⟩ := mvote_same hc.symm hF hl hFi hli (by omega)
      have hFi' := efits hFi (by rw [hli]; rfl)
      rw [hns] at hFi'
      have hEi' := ev_toE (by rw [hli]; rfl) hEi
      obtain ⟨pcj, kj⟩ := ej
      simp only [Epilogue.Ev, toE, hli, Site.epi] at hEi'
      obtain ⟨bj, hkj⟩ := hEi'
      subst hkj
      exact ⟨pcj, _, bj, rfl, di, _, hFi', by simp [toE, hsite], rfl⟩) i hi

/-! ### What the MMA warp's events return -/

/-- Only an election site fires an election, with the full mask. -/
theorem ev_elect {d : D} {e : Event} {mk inst ld : Nat} (hev : Ev p L g d e)
    (hk : e.kind = .elect mk inst ld) : mk = 2 ^ 32 - 1 := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases s
  case eq | ep | ce =>
    simp only [Ev] at hev
    rcases hev with ⟨_, _, -, h⟩ | ⟨_, h⟩ <;> simp only [Kind.elect.injEq, reduceCtorEq] at h
    exact h.1
  all_goals exfalso; simp [Ev, Site.toE, Epilogue.Ev] at hev

/-- **An election returns what the lane's earlier elections returned** (Core's election rule:
every election of a warp with one mask returns one leader). -/
theorem expect_elect (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) :
    ExpectElect L g (d, rc n) e := by
  have hg := Frame.lt_of_get hX he
  have hev := (mfired hp hX he hσ).1
  intro mk inst ld hk
  have hm := ev_elect hev hk
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk hm
  have hw : SameWarp L g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨j, -, ⟨pc', kind'⟩, hf, hc⟩ := exists_of_count hσ h0
    cases kind' <;> simp [Proof.cls, Mma.cls] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact (elect_leader hX hf he hw).symm
  · obtain ⟨j, -, ⟨pc', kind'⟩, hf, hc⟩ := exists_of_count hσ h0
    cases kind' <;> simp [Proof.cls, Mma.cls] at hc
    obtain ⟨rfl, hne⟩ := hc
    rw [← elect_leader hX hf he hw]
    exact hne

/-- **The read of the used-K length returns the launch word of the chosen request.** -/
theorem expect_uk (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : D} {ns nv : Nat} {e : Event} (he : X.get (g, k) = some e) (hs : d.site = .uk)
    (hF : MFits p L g d ns nv) (hev : Ev p L g d e) : MExpect p L g d ns e := by
  have hb := Epilogue.batch_lt hp
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  have hFE := efits hF (by rw [hs]; rfl)
  simp only [Epilogue.Fits, toE, hs, Site.epi] at hFE
  obtain ⟨R, bal, hC, -, -⟩ := hFE
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  obtain ⟨pc, kind⟩ := e
  simp only [Ev, hs] at hev
  have hc : chosen d.v.sc = W i := by simpa only [toE] using hi
  rcases hev with ⟨bs, rfl⟩ | ⟨f, rfl⟩
  swap
  · simp [MExpect, hs, Site.sched]
  simp only [MExpect, hs]
  have haddr : (reqAddr p d.v .uk).toNat = p.usedKBase + 4 * i := by
    rw [show reqAddr p d.v .uk = truncBits 64 (Epilogue.vbits (Epilogue.addrS p.usedKBase
      (chosen d.v.sc))) + BitVec.ofInt 64 0 from rfl, hc]
    exact addrK_toNat hp hroom (by omega)
  rw [haddr] at he
  have hin : ∀ j < 4, ∃ r ∈ p.inputRegions,
      r.Contains ((globalLoc (p.usedKBase + 4 * i)).at j) := by
    intro j hj
    refine ⟨⟨p.usedKBase, 4 * p.batch⟩, by simp [Params.inputRegions], ?_⟩
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    omega
  rw [inputReadValue hp hX (i := (g, k)) ⟨pc, he⟩ rfl hin (hp.usedK i (by omega)),
    show Value.bits 32 (BitVec.ofNat 64 (p.kLength i)) = b32 (p.kLength i) from rfl, rebuild_b32]
  simp only [b32, ukv, hc, r32_W (show i < 2 ^ 32 by omega),
    toNat_W (show i < 2 ^ 64 by omega)]

set_option maxHeartbeats 1000000 in
/-- **What every event of a lane of warp 12 at a role state returns is what the reference
says**, from the launch words and the lanes of its warp before it. -/
theorem mexpect (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 12) {k : Nat} {d : D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hJ : RefCounts p L g (d, rc n)) (hF : MFits p L g d (n .shfl) (n .vote))
    (IH : isColl e = true → GoodUpTo p L X (n .shfl + n .vote)) :
    MExpect p L g d (n .shfl) e := by
  have hev := (mfired hp hX he hσ).1
  obtain ⟨pc, kind⟩ := e
  -- a scan shuffle: the source lane's value at the same site
  have scan : d.site.epi.shfl = true → ∀ mode a b c recv ok, kind = .shfl mode a b c recv ok →
      Epilogue.Expect p L g (toE d) (n .shfl - 1 - d.v.ps) ⟨pc, kind⟩ := by
    intro hse mode a b c recv ok hk
    subst hk
    have hsc : d.site.scan = true := by
      obtain ⟨s, v⟩ := d; cases s <;> simp_all [Site.epi, Epilogue.Site.shfl, Site.scan]
    have hsl := Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c
    obtain ⟨hsT, hsW, hsC, -, -⟩ := lane_facts hp hg hw hsl
    obtain ⟨j, pc', b', c', r', o', hj, hG, hcj⟩ := mshfl_src hp hX hg hw he hσ hJ hF
      (IH rfl)
    obtain ⟨d1, n1, -, hJ1, hF1, hE1, hs1, -⟩ :=
      role_at hp hX hj hG (.inr (.inr ⟨rfl, by have := mfits_three hF; omega⟩))
    obtain ⟨hsite, hns⟩ := mshfl_same hsC.symm hF hse hF1 hJ1 ((mev_coll hE1).1 rfl)
      (by omega)
    refine Epilogue.expect_shfl_of_src hp hg hw (ev_toE hsc hev) ⟨toE d1, n1 .vote, ?_, ?_, ?_⟩
    · have := efits hF1 (shfl_epi (by rw [hsite]; exact hse)).1
      rwa [hns] at this
    · simp [toE, hsite]
    · have hsc1 : d1.site.scan = true := by rw [hsite]; exact hsc
      exact Epilogue.ev_opnd (ev_toE hsc1 hE1)
  cases hs : d.site
  case uk => exact expect_uk hp hX he hs hF hev
  case bcast | sh =>
    simp only [Ev, hs] at hev
    obtain ⟨recv, ok, rfl⟩ := hev
    simp only [MExpect, hs]
    have hsl := Step.shflSource_lt .idx (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
    obtain ⟨hsT, hsW, -, -, -⟩ := lane_facts hp hg hw hsl
    obtain ⟨j, pc', b', c', r', o', hj, hG, -⟩ := mshfl_src hp hX hg hw he hσ hJ hF
      (IH rfl)
    exact sent_word hp hX hsW hj hG
  case word k' =>
    simp only [MExpect, hs]
    intro _
    exact Epilogue.expect_word hp hReads he
      (show (toE d).site = .word k' by simp [toE, hs, Site.epi])
      (efits hF (by rw [hs]; rfl)) (ev_toE (by rw [hs]; rfl) hev)
  case q0 | q1 =>
    simp only [MExpect, hs]
    intro _
    exact Epilogue.expect_q hp hReads he (by simp [toE, hs, Site.epi])
      (efits hF (by rw [hs]; rfl)) (by
        simp only [Epilogue.Ev, toE, hs, Site.epi]
        simp only [Ev, hs] at hev
        rcases hev with ⟨bs, h⟩ | ⟨f, h⟩
        · exact .inl ⟨bs, h⟩
        · exact .inr ⟨f, h⟩)
  case vote l =>
    simp only [MExpect, hs]
    intro _
    have hE0 := ev_toE (by rw [hs]; rfl) hev
    simp only [Epilogue.Ev, toE, hs, Site.epi] at hE0
    obtain ⟨b, hb⟩ := hE0
    subst hb
    have hb := mvote_bits hp hX hg hw he hσ hF (IH isColl_vote)
    exact Epilogue.expect_vote_of_bits hp hg hw (epi_vote hs) fun i hi => by
      obtain ⟨di, nvi, h1, h2, h3⟩ := hb i hi
      exact ⟨toE di, nvi, h1, h2, h3⟩
  case down | up | total | pre | tiles =>
    have hse : d.site.epi.shfl = true := by rw [hs]; rfl
    have hE0 := ev_toE (by rw [hs]; rfl) hev
    simp only [MExpect, hs]
    intro _
    simp only [Epilogue.Ev, toE, hs, Site.epi] at hE0
    obtain ⟨recv, ok, hk⟩ := hE0
    exact scan hse _ _ _ _ _ _ hk
  all_goals simp [MExpect, hs, Site.sched]

set_option maxHeartbeats 1000000 in
/-- **Every event of a lane of warp 12 at a state that holds `Ref` makes a good step** once no
lane of warp 12 is bad at an earlier collective position. -/
theorem step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (g k : Nat) (σ : (thread p L g).D) (e : Event)
    (hQ : Q L g) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hR : Ref p L g σ)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → Q L j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L) X j) :
    Frame.StepGood (thread p L) (Ref p L) g σ e := by
  obtain ⟨hg, hw⟩ := hQ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_step hp hX hg hw he hσ hR hprev
  · exact hR.elim
  · rcases d with s | ⟨⟨⟩, d⟩
    · exact s_step hp hX he hσ hR
    · refine role_step hp hX he hσ hR fun hub => ⟨?_, expect_elect hp hX he hσ⟩
      obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
      obtain ⟨hcs, hcv⟩ := counts hσ
      refine mexpect hp hX hReads hg hw he hσ hJ hF fun hce h j hh hj => ?_
      refine upTo_of_prev (fun _ => ref_init) he hce hprev h j hh ?_
      rw [countColl ((X.tr g).take k), hcs, hcv]
      exact hj
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- **Every lane of warp 12 is followed, and its states hold the reference invariant**: by the
order induction on the collectives up to an event, restricted to the lanes of warp 12. -/
theorem good (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 12) (k : Nat) : Good p L X g k :=
  Frame.followedOn (C := thread p L) (J := Ref p L) (Q := Q L) (Frame.inductive_lex (μ X))
    (fun _ _ => ref_init) (step hp hX hReads) ⟨hg, hw⟩ k

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
