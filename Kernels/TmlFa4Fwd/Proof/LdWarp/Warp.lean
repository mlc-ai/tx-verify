-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Expect
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Pos
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.ShapeAll
public import Lemmas.Kernel.Followed
public import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Handoff
import Kernels.TmlFa4Fwd.Proof.Loader.RefNext
import Kernels.TmlFa4Fwd.Proof.Loader.RefRows
import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Lemmas.Flow.AllocTmpl
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The lanes of the loader warps are followed

Every lane of loader warp `w` (14 or 15) is followed by the thread machine, and every state holds
the reference invariant (`good`): `Frame.followedOn` restricted to the lanes of warp `w`, with the
order by the warp collectives up to an event (`μ`), as for the output, MMA and correction warps.

**Reference invariant** (`Ref`). At a startup state the startup's words and counts (`StartAt` with
the warp index `w`) and zero loader counts; at a role state, unless an event so far was undefined
behaviour, the loader lane's invariant (`Loader.Ref`: the ledger's closed forms on the loader
classes of the thread's ledger) and the reference values (`LFits`, with the thread's shuffles,
ballots and commits).

**Sources.** The scheduler's reads come from the launch words (the output warp's `expect_word`,
`expect_q`; the used-K word by `inputReadValue`), the scan's shuffles and ballot from the lanes of
the warp at the same instance (`Common/Coll.lean`, with the positions of `Pos.lean`), and a
packet's row shuffles receive the source lane's word. The lane's local words are in `Mem.lean`;
`Src.lean` assembles the expectations and the never-dropped theorem `good`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-! ### The reference invariant -/

/-- The loader counts before the role's first state. -/
def ZeroL (n : Cls → Nat) : Prop := ∀ c, n (.load c) = 0

/-- **The reference invariant of a lane of loader warp `w`.** -/
def Ref (p : Params) (L : Launch) (w g : Nat) :
    (Startup.D ⊕ (Σ i, (frag p L g i).D)) × (Cls → Nat) → Prop
  | (.inl s, n) => StartAt L w s n ∧ n .vote = 0 ∧ ZeroL n
  | (.inr ⟨.loader b, d⟩, n) => wOf b = w ∧ (n .ub = 0 →
      Loader.Ref p L g w (d, lcn n) ∧ LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
  | (.inr ⟨.epilogue, _⟩, _) | (.inr ⟨.mma, _⟩, _) | (.inr ⟨.correction, _⟩, _)
  | (.inr ⟨.stub _, _⟩, _) | (.inr ⟨.softmax, _⟩, _) => False

/-- Lane `g`'s state before its `k`-th event is followed and holds the reference invariant. -/
abbrev Good (p : Params) (L : Launch) (w : Nat) (X : Execution) (g k : Nat) : Prop :=
  Frame.FollowedAt (thread p L) (Ref p L w) X g k

/-- The induction hypothesis: the lanes of warp `w` are followed at the positions with at most
`n` collectives before them. -/
abbrev GoodUpTo (p : Params) (L : Launch) (w : Nat) (X : Execution) (n : Nat) : Prop :=
  Proof.GoodUpTo (Ref p L w) X w n

theorem ref_init : Ref p L w g (thread p L g).init := by
  show Ref p L w g (.inl ⟨.sh 0, 0, 0, 0⟩, fun _ => 0)
  exact ⟨⟨rfl, rfl, by simp, by simp⟩, rfl, fun _ => rfl⟩

/-! ### Events at the loader warps' states -/

theorem lfired (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {e : Event} {d : D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n))) :
    Ev p L g (wOf b) d e ∧ (Loader.F p L g b).inv d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, -, hinv, -, -⟩ :=
    strict_fired_site hp hX he hσ rfl
  obtain ⟨o, hf⟩ := strict_fired hp hX he hσ rfl
  have hf' : (Loader.F p L g b).toMachine.Fired (some d) e o := hf
  exact ⟨(Code.Shape.fired (Loader.shape hp) (Loader.steps hp hg b) hf').1, hinv⟩

theorem next_linj (b : Bool) (d : D) (n : Cls → Nat) (e : Event) :
    (thread p L g).next (linj p L g b d n) e = ((Loader.F p L g b).next d e).map
      (Option.map fun d' => linj p L g b d' (Code.bump (Proof.cls L g) n e)) := by
  show ((((Loader.F p L g b).next d e).map (Option.map fun d' =>
    (Sum.inr ⟨Role.loader b, d'⟩ : (glued p L g).D))).map
        (Option.map fun d' => (d', Code.bump (Proof.cls L g) n e))) = _
  rcases (Loader.F p L g b).next d e with _ | _ | d' <;> rfl

/-- A followed state of a loader lane before an event that is no undefined behaviour: a startup
state, or a role state with its reference invariant. -/
theorem good_cases (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Good p L w X g j) :
    (∃ s n, Frame.stateAt (thread p L) X g j = some (some (.inl s, n)) ∧
        StartAt L w s n ∧ n .vote = 0 ∧ ZeroL n) ∨
      (∃ b d n, Frame.stateAt (thread p L) X g j = some (some (linj p L g b d n)) ∧
        wOf b = w ∧ n .ub = 0 ∧ Loader.Ref p L g w (d, lcn n) ∧
        LFits p L g d (n .shfl) (n .vote) (n (.load .commit))) := by
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub hG
  rcases σ with s | ⟨_ | _ | _ | b | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact .inl ⟨s, n, hσ, hR⟩
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · have h0 := ub_zero hX he hσ
    exact .inr ⟨b, d, n, hσ, hR.1, h0, hR.2 h0⟩
  · exact hR.elim

/-- The kind of event a loader site fires, as far as the collectives and the return go. -/
theorem lev_class {d : D} {e : Event} (hev : Ev p L g w d e) :
    (Execution.isShfl e = true → d.site.lsh = true) ∧
      (isFullVote e = true → ∃ l, d.site = .vote l) ∧ (e.kind = .exit → d.site = .exit) := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case word k | down k | up k j | total k | vote k | pre k | tiles k =>
    simp only [Ev] at hev
    obtain ⟨h1, h2, h3⟩ := Epilogue.ev_class hev
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := h1 h; simp_all [Site.lsh, Site.pkt, Site.epi, Site.toE]
    · obtain ⟨l, hl⟩ := h2 h; simp_all [Site.toE]
    · obtain ⟨l, hl⟩ := h3 h; simp_all [Site.toE]
  all_goals
    simp only [Ev] at hev
    shape_destruct hev
    all_goals subst_vars
    all_goals refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    all_goals first
      | rfl
      | (simp [Execution.isShfl, isFullVote, voteClass] at h; done)
      | (simp at h; done)
      | simp_all [Execution.isShfl, isFullVote, voteClass, Site.lsh, Site.pkt]

/-- **A followed lane of a loader warp at a ballot, a return, or a shuffle past the startup's is
at a role state.** -/
theorem role_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    {e : Event} (he : X.get (h, j) = some e) (hG : Good p L w X h j)
    (hk : isFullVote e = true ∨ e.kind = .exit ∨
      (Execution.isShfl e = true ∧ 3 ≤ ((X.tr h).take j).countP Execution.isShfl)) :
    ∃ b d n, Frame.stateAt (thread p L) X h j = some (some (linj p L h b d n)) ∧ wOf b = w ∧
      Loader.Ref p L h w (d, lcn n) ∧ LFits p L h d (n .shfl) (n .vote) (n (.load .commit)) ∧
      Ev p L h w d e ∧
      ((X.tr h).take j).countP Execution.isShfl = n .shfl ∧
      ((X.tr h).take j).countP isFullVote = n .vote := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    rcases hk with h | h | ⟨h, -⟩ <;> simp [isFullVote, voteClass, Execution.isShfl] at h
  rcases good_cases hp hX he hub hG with ⟨s, n, hσ, hS, -⟩ | ⟨b, d, n, hσ, hb, -, hJ, hF⟩
  · exfalso
    obtain ⟨h1, h2, h3, -⟩ := start_kind hS (start_fired hp hX he hσ).1
    have hc := (counts hσ).1
    rcases hk with h | h | ⟨h, h'⟩
    · rw [h1] at h; cases h
    · exact h2 h
    · have := h3 h; omega
  · have hev := (lfired hp hX he hσ).1
    rw [hb] at hev
    exact ⟨b, d, n, hσ, hb, hJ, hF, hev, (counts hσ).1, (counts hσ).2⟩

/-! ### The startup -/

theorem enterOf_ld {s : Startup.D} (hw : w = 14 ∨ w = 15) (h3 : s.x3 = BitVec.ofNat 64 w) :
    Startup.enterOf s = { s with site := .enter .loader } := by
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at h3
  subst h3
  unfold Startup.enterOf
  rcases hw with rfl | rfl <;> (dsimp only; simp (config := { decide := true }))

theorem lfits_three {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc) : 3 ≤ ns := by
  unfold LFits at hF
  split at hF
  · omega
  · exact Epilogue.fits_three hF.2
  · exact Epilogue.fits_three hF.2.1
  · have := Epilogue.fits_three hF.2.1; omega
  · have := Epilogue.fits_three hF.2.1; omega
  · obtain ⟨l, h1, h2, -⟩ := hF; have := Epilogue.fits_three h2; omega

/-- The commit count after an event is the commit count before it plus its commit. -/
theorem bump_commit (n : Cls → Nat) (e : Event) :
    Code.bump (Proof.cls L g) n e (.load .commit) = n (.load .commit) + cm e := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> rfl

/-- **The startup steps a lane of loader warp `w` well**, into the role's first state after the
barrier. -/
theorem start_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) (hw14 : w = 14 ∨ w = 15) {k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hR : Ref p L w g (.inl s, n))
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L w) X j) :
    Frame.StepGood (thread p L) (Ref p L w) g (.inl s, n) e :=
  start_step_of (Z := ZeroL) hp hX hg hw (by omega) (by omega) (fun _ => ref_init)
    (fun _ _ => rfl) (fun _ _ _ h => ⟨h.1, h.2.1⟩)
    (fun h j e r d n he hσ hR => by
      rcases r with _ | _ | _ | b | r | _
      on_goal 6 => exact hR.elim
      · exact hR.elim
      · exact hR.elim
      · exact hR.elim
      · exact lfits_three (hR.2 (ub_zero hX he hσ)).2
      · exact hR.elim)
    (fun _ _ hn hZ c => (hn _ (by simp [StartCls])).trans (hZ c))
    (fun s n e hb hS hv hZ hE hn => by
      have hZ' : ZeroL (Code.bump (Proof.cls L g) n e) := fun c =>
        (hn _ (by simp [StartCls])).trans (hZ c)
      have hv' : Code.bump (Proof.cls L g) n e .vote = 0 :=
        (hn _ (by simp [StartCls])).trans hv
      obtain ⟨site, x1, x2, x3⟩ := s
      simp only at hb
      subst hb
      simp only [StartAt] at hS
      simp only [Startup.Ev] at hE
      obtain ⟨h3, h4, rfl, rfl⟩ := hS
      rw [enterOf_ld hw14 rfl]
      have hgate : Gate L g .loader ⟨.enter .loader, BitVec.ofNat 64 L.sharedBase, x2,
          BitVec.ofNat 64 w⟩ = true := by
        rcases hw14 with rfl | rfl <;> simp [Gate]
      simp only [Code.enter, exit, hgate, roleOf, ↓reduceIte]
      have hb : wOf (BitVec.ofNat 64 w == BitVec.ofNat 64 15) = w := by
        rcases hw14 with rfl | rfl <;> decide
      refine ⟨hb, fun _ => ⟨?_, ?_⟩⟩
      · have : lcn (Code.bump (Proof.cls L g) n e) = fun _ => 0 := funext hZ'
        rw [this]
        have := Loader.ref_init (p := p) (L := L) (g := g) (w := w) (ent := ent p L)
        exact this
      · obtain ⟨pc, kind⟩ := e
        simp only at hE
        subst hE
        refine ⟨?_, hv', hZ' .commit⟩
        simp [Code.bump, Proof.cls, Execution.isShfl, h3])
    he hσ hR hprev

/-! ### The role's steps -/

/-- Every expectation of the loader lane holds for an undefined-behaviour event. -/
theorem expect_ub {dn : D × (Cnt → Nat)} {e : Event} (hub : ∃ f, e.kind = .ub f) :
    Loader.Expect dn e := by
  obtain ⟨f, hf⟩ := hub
  intro v hv
  obtain ⟨pc, kind⟩ := e
  simp only at hf
  subst hf
  simp [recvAll, recv] at hv

/-- **A role state steps well on an event that returns what the references say**: the loader
lane's invariant and the reference values continue (`ref_next`, `lfits_next`); after an
undefined-behaviour event the invariant's guard is false. -/
theorem role_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hR : Ref p L w g (linj p L g b d n))
    (hexp : (∀ f, e.kind ≠ .ub f) →
      LExpect p L g d (n .shfl) (n (.load .commit)) e ∧ Loader.Expect (d, lcn n) e) :
    Frame.StepGood (thread p L) (Ref p L w) g (linj p L g b d n) e := by
  obtain ⟨hb, hR⟩ := hR
  subst hb
  obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
  obtain ⟨hev, hinv⟩ := lfired hp hX he hσ
  have hw : wOf b = 14 ∨ wOf b = 15 := by cases b <;> simp [wOf]
  show (thread p L g).next (linj p L g b d n) e ≠ some none ∧ _
  rw [next_linj]
  have hinv' : (MC p L g (wOf b) (ent p L)).inv (d, lcn n) := hinv
  by_cases hub : ∃ f, e.kind = .ub f
  · have hne : (Loader.F p L g b).next d e ≠ some none := fun h =>
      next_ne_stop hinv hev (expect_ub (dn := (d, lcn n)) hub) h
    rcases hn : (Loader.F p L g b).next d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd hn hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨rfl, fun h1 => ?_⟩
      obtain ⟨f, hf⟩ := hub
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      simp [Code.bump, Proof.cls] at h1
  · have hub' : ∀ f, e.kind ≠ .ub f := fun f h => hub ⟨f, h⟩
    obtain ⟨hLE, hED⟩ := hexp hub'
    obtain ⟨hne, hJ'⟩ := Loader.ref_next hp hw hinv' hJ hED hev hub'
    rcases hn : (Loader.F p L g b).next d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd (Code.counted_next_none_iff.mpr hn) hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨rfl, fun _ => ⟨hJ' _ ((Code.counted_next _ _ _).trans (by rw [hn]; rfl)), ?_⟩⟩
      have := lfits_next hF hLE hev hn
      have h1 : Code.bump (Proof.cls L g) n e .shfl = n .shfl + Epilogue.sh e := rfl
      have h2 : Code.bump (Proof.cls L g) n e .vote = n .vote + Epilogue.vt e := rfl
      rw [h1, h2, bump_commit]
      exact this

/-! ### The sources of the loader warps' collectives -/

/-- At a scan site the loader's event is the output warp's of its scan state. -/
theorem ev_toE {d : D} {e : Event} (hs : d.site.scan = true) (hev : Ev p L g w d e) :
    Epilogue.Ev p L g (toE d) e := by
  obtain ⟨s, v, kk⟩ := d
  have := toE_eq hs
  cases s <;> simp_all [Ev, Site.scan, toE]

theorem shfl_scan {s : Site} (h : s.epi.shfl = true) : s.scan = true := by
  cases s <;> simp_all [Site.epi, Epilogue.Site.shfl, Site.scan]

/-- **Every shuffle of a followed lane of loader warp `w` sends a 32-bit word.** -/
theorem sent_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h : Nat}
    (hw : Prologue.warpIndex L h = w) {j pc : Nat} {mode : ShflMode} {a r : Value} {b c : Nat}
    {o : Bool} (he : X.get (h, j) = some ⟨pc, .shfl mode a b c r o⟩) (hG : Good p L w X h j) :
    ∃ x, a = .bits 32 x := by
  rcases good_cases hp hX he (by rintro _ _ ⟨⟩) hG with ⟨s, n, hσ, hS, -⟩ |
    ⟨bb, d, n, hσ, -, -, -, -⟩
  · have hE := (start_fired hp hX he hσ).1
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case sh i =>
      obtain ⟨r', ok', hk⟩ := start_sent hp hw hS rfl hE
      simp only [Kind.shfl.injEq] at hk
      exact ⟨_, hk.2.1⟩
    all_goals simp only [StartAt] at hS
    all_goals simp [Startup.Ev] at hE
  · have hev := (lfired hp hX he hσ).1
    obtain ⟨s, v, kk⟩ := d
    cases s
    case word _ | down _ | up _ _ | total _ | vote _ | pre _ | tiles _ =>
      simp only [Ev] at hev
      exact ⟨_, Epilogue.ev_opnd hev⟩
    case xl _ _ _ | xh _ _ _ =>
      simp only [Ev] at hev
      obtain ⟨_, _, h⟩ := hev
      simp only [Kind.shfl.injEq] at h
      exact ⟨_, h.2.1⟩
    all_goals (simp only [Ev] at hev; shape_destruct hev; all_goals simp_all)

/-- **The source of a shuffle of a loader lane at a role state**: the source lane made the
shuffle of the same instance from a followed state, with the received value as its operand. -/
theorem lshfl_src (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc : Nat} {mode : ShflMode}
    {a recv : Value} {b c : Nat} {ok : Bool} {bb : Bool} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g bb d n)))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
    (IH : GoodUpTo p L w X (n .shfl + n .vote)) :
    ∃ j pc' b' c' r' o',
      X.get (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) =
        some ⟨pc', .shfl mode recv b' c' r' o'⟩ ∧
      Good p L w X (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j ∧
      ((X.tr (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)).take j).countP
        Execution.isShfl = n .shfl := by
  have hs := (lev_class (lfired hp hX he hσ).1).1 rfl
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs, -⟩ := shfl_src hp hX hg hw he (counts hσ).1 IH
    (fun h j0 e0 _ hc he0 hv0 hG hs0 hc0 => by
      obtain ⟨b0, d0, n0, -, -, -, hF0, hE0, hs0', hv0'⟩ := role_at hp hX he0 hG (.inl hv0)
      obtain ⟨l, hl⟩ := (lev_class hE0).2.1 hv0
      simp only [Frame.cnt] at hs0 hc0
      have := lshfl_lt_vote hc.symm hF hs hF0 hl (by omega)
      omega)
    (fun h kx pcx _ hc hx hG hsx hvx => by
      obtain ⟨bx, dx, nx, -, -, -, hFx, hEx, hsx', -⟩ := role_at hp hX hx hG (.inr (.inl rfl))
      have hl := (lev_class hEx).2.2 rfl
      simp only [Frame.cnt] at hsx
      have := lshfl_lt_exit hc.symm hF hs hFx hl
      omega)
  exact ⟨j, pc', b', c', r', o', hj, hG, hjs⟩

set_option maxHeartbeats 1000000 in
/-- **A ballot's bits are the predicates of all lanes at the same ballot**, in the output warp's
terms of their scan states. -/
theorem lvote_bits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc : Nat} {a : Bool}
    {bv : BitVec 32} {bb : Bool} {d : D} {n : Cls → Nat} {l : Bool} (hl : d.site = .vote l)
    (he : X.get (g, k) = some ⟨pc, .vote (2 ^ 32 - 1) a bv⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g bb d n)))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
    (IH : GoodUpTo p L w X (n .shfl + n .vote)) :
    ∀ i < 32, ∃ di nvi, Epilogue.Fits p L (g - laneOf L g + i) (toE di)
        (n .shfl - 32 * n (.load .commit)) nvi ∧ (toE di).site = (toE d).site ∧
      bv.getLsbD i = Epilogue.votePred p L (g - laneOf L g + i) (toE di) := by
  have h3 := lfits_three hF
  intro i hi
  exact vote_src (P := fun h b => ∃ di nvi, Epilogue.Fits p L h (toE di)
      (n .shfl - 32 * n (.load .commit)) nvi ∧ (toE di).site = (toE d).site ∧
        b = Epilogue.votePred p L h (toE di)) hp hX hg hw he (counts hσ).2 IH
    (fun h j1 e1 _ hc he1 hs1 hG hv1 hc1 => by
      simp only [Frame.cnt] at hv1 hc1
      obtain ⟨b1, d1, n1, -, -, -, hF1, hE1, hs1', hv1'⟩ :=
        role_at hp hX he1 hG (.inr (.inr ⟨hs1, by omega⟩))
      have := lshfl_lt_vote hc hF1 ((lev_class hE1).1 hs1) hF hl (by omega)
      omega)
    (fun h kx pcx _ hc hx hG hsx hvx => by
      simp only [Frame.cnt] at hsx hvx
      obtain ⟨bx, dx, nx, -, -, -, hFx, hEx, -, hvx'⟩ := role_at hp hX hx hG (.inr (.inl rfl))
      exact lvote_exit hc.symm hF hl hFx ((lev_class hEx).2.2 rfl) (by omega))
    (fun h j ej _ hc hej hfv hG hsj hcnt => by
      simp only [Frame.cnt] at hsj hcnt
      obtain ⟨bi, di, ni, -, -, -, hFi, hEi, hsi, hvi⟩ := role_at hp hX hej hG (.inl hfv)
      obtain ⟨li, hli⟩ := (lev_class hEi).2.1 hfv
      obtain ⟨hsite, hns⟩ := lvote_same hc.symm hF hl hFi hli (by omega)
      have hFi' := (sched_fits (by rw [hli]; rfl) hFi).2.1
      rw [hns] at hFi'
      have hEi' := ev_toE (by rw [hli]; rfl) hEi
      obtain ⟨pcj, kj⟩ := ej
      simp only [Epilogue.Ev, toE, hli, Site.epi] at hEi'
      obtain ⟨bj, hkj⟩ := hEi'
      subst hkj
      exact ⟨pcj, _, bj, rfl, di, _, hFi', by simp [toE, hsite], rfl⟩) i hi

/-! ### What the loader warps' events return -/

theorem acc_rd {e : Event} {a : Acc} {bs : List (Option Byte)} {x : BitVec 64}
    (hk : e.kind = .rd a bs) (h : rebuild 3 bs = .ok (.bits 32 x)) :
    (RetKind.word 32).accepts e := by
  intro v hv
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  simp only [recvAll, recv, h, Option.toList_some, List.mem_singleton] at hv
  exact ⟨_, hv⟩

theorem acc_shfl {e : Event} {md : ShflMode} {a : Value} {b c : Nat} {x : BitVec 64} {ok : Bool}
    (hk : e.kind = .shfl md a b c (.bits 32 x) ok) : (RetKind.word 32).accepts e := by
  intro v hv
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  simp only [recvAll, recv, Option.toList_some, List.mem_singleton] at hv
  exact ⟨_, hv⟩

theorem acc_ub {k : RetKind} {e : Event} (hk : ∃ f, e.kind = .ub f) : k.accepts e := by
  intro v hv
  obtain ⟨f, hk⟩ := hk
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  simp [recvAll, recv] at hv

/-- The request's first two reads address the output warp's words. -/
theorem ev_q {d : D} {e : Event} (hq : d.site = .q0 ∨ d.site = .q1) (hev : Ev p L g w d e) :
    Epilogue.Ev p L g (toE d) e := by
  obtain ⟨s, v, kk⟩ := d
  have hc : ∀ s', chosen { v.sc with site := s' } = chosen v.sc := fun _ => rfl
  rcases hq with h | h <;> simp only at h <;> subst h <;>
    simp [Ev, Epilogue.Ev, toE, Site.epi, Epilogue.rdAddr, rv, reqRegs, valueOf, values,
      valuesReq, lookupLit, truncBits64, hc, Epilogue.wordAcc, wordAcc, globalLoc,
      BitVec.toNat_add, BitVec.toNat_ofInt] at hev ⊢ <;> exact hev

/-- **The used-K read returns the chosen request's launch word.** -/
theorem expect_uk (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : D} {ns nv nc : Nat} {e : Event} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some e) (hs : d.site = .uk) (hF : LFits p L g d ns nv nc)
    (hev : Ev p L g w d e) (hk : e.kind = .rd a bs) :
    rebuild 3 bs = .ok (.bits 32 (ukv p (chosen d.v.sc))) := by
  have hb := Epilogue.batch_lt hp
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  have hF' := hF
  unfold LFits at hF'
  rw [show lc d.site = .req by rw [hs]; rfl] at hF'
  obtain ⟨-, hFE, -⟩ := hF'
  simp only [Epilogue.Fits, toE, hs, Site.epi] at hFE
  obtain ⟨R, bal, hC, -, -⟩ := hFE
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  have hc : chosen d.v.sc = W i := by simpa only using hi
  obtain ⟨s, v, kk⟩ := d
  simp only at hs
  subst hs
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  simp only [Ev] at hev
  rcases hev with ⟨bs', hk'⟩ | ⟨f, hk'⟩
  swap
  · cases hk'
  simp only [Kind.rd.injEq] at hk'
  obtain ⟨rfl, rfl⟩ := hk'
  have haddr : (rv p L g w ⟨.uk, v, kk⟩ (reqRegs .uk).1 + BitVec.ofInt 64 (reqRegs .uk).2).toNat =
      p.usedKBase + 4 * i := by
    have : rv p L g w ⟨.uk, v, kk⟩ (reqRegs .uk).1 + BitVec.ofInt 64 (reqRegs .uk).2 =
        truncBits 64 (Epilogue.vbits (Epilogue.addrS p.usedKBase (chosen v.sc))) +
          BitVec.ofInt 64 0 := by
      simp [rv, reqRegs, valueOf, values, valuesReq, lookupLit, truncBits64]
    rw [this]
    simp only at hc
    rw [hc]
    exact Mma.addrK_toNat hp hroom (by omega)
  rw [haddr] at he
  have hin : ∀ j < 4, ∃ r ∈ p.inputRegions,
      r.Contains ((globalLoc (p.usedKBase + 4 * i)).at j) := by
    intro j hj
    refine ⟨⟨p.usedKBase, 4 * p.batch⟩, by simp [Params.inputRegions], ?_⟩
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    omega
  rw [inputReadValue hp hX (i := (g, k)) ⟨pc, he⟩ rfl hin (hp.usedK i (by omega)),
    show Value.bits 32 (BitVec.ofNat 64 (p.kLength i)) = b32 (p.kLength i) from rfl, rebuild_b32]
  simp only at hc
  simp only [b32, ukv, hc, r32_W (show i < 2 ^ 32 by omega),
    toNat_W (show i < 2 ^ 64 by omega)]

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
