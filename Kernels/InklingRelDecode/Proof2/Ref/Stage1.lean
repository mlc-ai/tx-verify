-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Ref.Early
public import Kernels.InklingRelDecode.Proof2.Ref.Input
public import Kernels.InklingRelDecode.Proof2.Ref.Codes
public import Lemmas.Kernel.FollowedUntil

@[expose] public section

/-! # The first stage of the following over the recorded base word

The reference `Ref1` is `Ref` with the base word the startup recorded (`tm`) in place of the
base word 0: the startup's states carry no condition on it, the prologue's reference is
`ProA.PRef` at the recorded number and value and the workers' is `WRef` at the recorded value.
The states where a step needs the base word 0 owe nothing (`S1`, `Frame.followedUntil`): the
softmax–epilogue fragment and the stubs (entered only through gates on the base word 0 or the
warp index), and the dispatch's role-byte load whose base word fails `WComp.baseOk` (the MMA
role's entry). So this stage needs no source of the base word: it is the
following that `BaseRead` is proved from.

`start_followed1`: before its shuffle, every thread is followed with `Ref1` (no source at all;
the startup does not stop on any value before it). This is what the warp collective source of
the startup's shuffle asks of the source lanes (`start_recv1`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The startup's reference over the recorded base word: not an exit, no shuffle, no barrier-1
event and no proxy fence yet. -/
abbrev StartRef1 (s : Startup.D) (n : Cls → Nat) : Prop :=
  (∀ r, s.site ≠ .enter r) ∧ n .shfl = 0 ∧ n (.bar 1) = 0 ∧ n .fence = 0

/-- A worker state at the dispatch loop's head or its barrier (before the first barrier-1 event
of the loop's first round). -/
def WEarly : Proof.WComp.WSt → Prop
  | .worker w => w.site = .loop ∨ w.site = .bar2
  | _ => False

/-- The ledger's count of a class an event is not in does not change. -/
theorem bump_eq {c : Cls} {n : Cls → Nat} {e : Event} (h : cls c e = false) :
    Code.bump cls n e c = n c := by
  simp [Code.bump, h]

theorem bump_ge (c : Cls) (n : Cls → Nat) (e : Event) : n c ≤ Code.bump cls n e c := by
  simp only [Code.bump]; omega

/-- A startup step to a state that is no exit at an event of none of the three classes keeps
`StartRef1`. -/
theorem keepS {s s' : Startup.D} {n : Cls → Nat} {e : Event} (hR : StartRef1 s n)
    (hs' : ∀ r, s'.site ≠ .enter r) (h1 : Execution.isShfl e = false)
    (h2 : cls (.bar 1) e = false) (h3 : cls .fence e = false) :
    StartRef1 s' (Code.bump cls n e) :=
  ⟨hs', by rw [bump_eq (c := .shfl) (by simpa [cls] using h1)]; exact hR.2.1,
    by rw [bump_eq h2]; exact hR.2.2.1, by rw [bump_eq h3]; exact hR.2.2.2⟩

/-- **The first stage's reference.** -/
def Ref1 (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inl s, n) => StartRef1 s n
  | (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) => 1 ≤ n .shfl ∧ ProA.PRef Q L g tm bw d ∧
      (179 < d.site.pc → 1 ≤ n .fence ∨ 1 ≤ n .ub)
  | (.inr ⟨.inl (.dp _ _), .inr _⟩, n) =>
      (1 ≤ n .fence ∨ 1 ≤ n .ub) ∧ (1 ≤ n (.bar 1) ∨ 1 ≤ n .ub)
  | (.inr ⟨.inl (.worker bw), σ⟩, n) => 1 ≤ n .shfl ∧ WRef bw σ ∧
      (WEarly σ ∨ 1 ≤ n (.bar 1) ∨ 1 ≤ n .ub) ∧ 4 ≤ g % L.block / 32
  | (.inr ⟨.inr _, _⟩, _) => False

/-- **The states that owe nothing in the first stage.** -/
def S1 (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inr _⟩, _) => True
  | (.inr ⟨.inl (.worker _), .worker w⟩, _) => w.site = .ldRole ∧ ¬ Proof.WComp.baseOk w.P
  | _ => False

theorem ref1_init : Ref1 Q L g (thread Q L g).init := by
  show Ref1 Q L g (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
    (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => 0)
  rw [enter_inl enterOf_init]
  unfold Startup.init
  split <;> exact ⟨fun _ h => (by cases h), rfl, rfl, rfl⟩

/-- The startup's events are no exit, and the only shuffles are the shuffle sites'. -/
theorem start_kind1 {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartRef1 s n)
    (hE : Startup.Ev L g s e) :
    e.kind ≠ .exit ∧ (Execution.isShfl e = true →
      ∃ recv ok, e = ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩) := by
  obtain ⟨site, tm, x, bw⟩ := s
  cases site
  case enter r => exact absurd rfl (hS.1 r)
  all_goals simp only [Startup.Ev] at hE
  all_goals first
    | (subst hE; exact ⟨by simp, by simp [Execution.isShfl]⟩)
    | (obtain ⟨col, -, rfl⟩ := hE; exact ⟨by simp, by simp [Execution.isShfl]⟩)
    | (obtain ⟨ac, bs, rfl, -⟩ := hE; exact ⟨by simp, by simp [Execution.isShfl]⟩)

theorem bump_shfl1 {n : Cls → Nat} {e : Event} (h : Execution.isShfl e = false) :
    Code.bump cls n e .shfl = n .shfl := by
  simp [Code.bump, cls, h]

/-- An event of a startup state is no barrier-1 event and no proxy fence. -/
theorem start_cls {s : Startup.D} {n : Cls → Nat} {e : Event} (hR : StartRef1 s n)
    (hev : (∀ f, e.kind ≠ .ub f) → Startup.Ev L g s e) :
    cls (.bar 1) e = false ∧ cls .fence e = false := by
  by_cases hu : ∀ f, e.kind ≠ .ub f
  · have hE := hev hu
    obtain ⟨site, tm, x, bw⟩ := s
    cases site
    case enter r => exact absurd rfl (hR.1 r)
    all_goals simp only [Startup.Ev] at hE
    all_goals first
      | (subst hE; exact ⟨rfl, rfl⟩)
      | (obtain ⟨_, _, rfl⟩ := hE; exact ⟨rfl, rfl⟩)
      | (obtain ⟨_, _, rfl, _⟩ := hE; exact ⟨rfl, rfl⟩)
  · simp only [not_forall, not_not] at hu
    obtain ⟨f, hf⟩ := hu
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    exact ⟨rfl, rfl⟩

/-- **A startup step at an event that is no shuffle** keeps `StartRef1` (or kills the thread). -/
theorem start_next1 {s : Startup.D} {n : Cls → Nat} {e : Event} (hR : StartRef1 s n)
    (hev : (∀ f, e.kind ≠ .ub f) → Startup.Ev L g s e) (hes : Execution.isShfl e = false)
    (hb1 : cls (.bar 1) e = false) (hfe : cls .fence e = false) :
    (thread Q L g).next (.inl s, n) e = none ∨
      ∃ s' n', (thread Q L g).next (.inl s, n) e = some (some (.inl s', n')) ∧ StartRef1 s' n' := by
    obtain ⟨site, tm, x, bw⟩ := s
    cases site with
    | enter r => exact absurd rfl (hR.1 r)
    | alloc =>
      by_cases hl : laneOf L g = 0
      · exact .inr ⟨_, _, to_state (s' := ⟨.allocWr, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
          keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
      · exact .inr ⟨_, _, to_state (s' := ⟨.bar0, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
          keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
    | allocWr => exact .inr ⟨_, _, to_state (s' := ⟨.bar0, tm, x, bw⟩) (by simp [Startup.succ]) rfl,
        keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
    | bar0 => exact .inr ⟨_, _, to_state (s' := ⟨.ld0, tm, x, bw⟩) (by simp [Startup.succ]) rfl,
        keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
    | ld0 =>
      by_cases hu : ∀ f, e.kind ≠ .ub f
      · obtain ⟨ac, bs, rfl, -⟩ := hev hu
        cases hr : rebuild 3 bs with
        | error f => exact .inl (by rw [next_start]; simp [Startup.succ, hr])
        | ok v =>
          cases hw : Proof.ProA.word32 v with
          | none => exact .inr ⟨_, _, to_state (s' := ⟨.bar1, 0, x, v⟩)
              (by simp [Startup.succ, hr, hw]) rfl,
              keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
          | some w => exact .inr ⟨_, _, to_state (s' := ⟨.bar1, w, x, v⟩)
              (by simp [Startup.succ, hr, hw]) rfl,
              keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
      · simp only [not_forall, not_not] at hu
        obtain ⟨f, hf⟩ := hu
        obtain ⟨pc, kd⟩ := e
        simp only at hf
        subst hf
        exact .inl (by rw [next_start]; simp [Startup.succ])
    | bar1 =>
      by_cases hl : g % L.block < 32
      · exact .inr ⟨_, _, to_state (s' := ⟨.relinq, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
          keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
      · exact .inr ⟨_, _, to_state (s' := ⟨.shfl, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl,
          keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
    | relinq => exact .inr ⟨_, _, to_state (s' := ⟨.shfl, tm, x, bw⟩) (by simp [Startup.succ]) rfl,
        keepS hR (fun _ h => by cases h) hes hb1 hfe⟩
    | shfl =>
      by_cases hu : ∀ f, e.kind ≠ .ub f
      · obtain ⟨recv, ok, rfl⟩ := hev hu
        simp [Execution.isShfl] at hes
      · simp only [not_forall, not_not] at hu
        obtain ⟨f, hf⟩ := hu
        obtain ⟨pc, kd⟩ := e
        simp only at hf
        subst hf
        exact .inl (by rw [next_start]; simp [Startup.succ])

/-- **Before its shuffle, every thread is followed with `Ref1`**: its machine is dead or at a
startup state with the reference. -/
theorem start_followed1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, ((X.tr g).take k).countP Execution.isShfl = 0 →
      Frame.stateAt (thread Q L) X g k = none ∨
        ∃ s n, Frame.stateAt (thread Q L) X g k = some (some (.inl s, n)) ∧ StartRef1 s n := by
  intro k
  induction k with
  | zero =>
    intro _
    refine .inr ⟨Startup.init L g, fun _ => 0, ?_, ?_⟩
    · rw [Frame.stateAt_zero]
      show some (some (Code.enter (Startup.code Q L g)
        (Code.withStubs (frag Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => 0)) = _
      rw [enter_inl enterOf_init]
    · unfold Startup.init
      split <;> exact ⟨fun _ h => (by cases h), rfl, rfl, rfl⟩
  | succ k ih =>
    intro hc
    have hc' : ((X.tr g).take k).countP Execution.isShfl = 0 := by
      have := (List.take_sublist_take_left (l := X.tr g) (show k ≤ k + 1 by omega)).countP_le
        (p := Execution.isShfl)
      omega
    by_cases hk : (X.tr g).length ≤ k
    · rw [Frame.stateAt_of_le (show (X.tr g).length ≤ k + 1 by omega), ← Frame.stateAt_of_le hk]
      exact ih hc'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hes : Execution.isShfl e = false := by
      have h1 : ((X.tr g).take (k + 1)).countP Execution.isShfl =
          ((X.tr g).take k).countP Execution.isShfl + if Execution.isShfl e then 1 else 0 := by
        rw [List.take_add_one, he, Option.toList_some, List.countP_append]
        by_cases hb : Execution.isShfl e <;> simp [hb]
      cases hb : Execution.isShfl e
      · rfl
      · rw [hb] at h1; simp at h1; omega
    rw [Frame.stateAt_succ he]
    rcases ih hc' with h0 | ⟨s, n, hσ, hR⟩
    · left; rw [h0]; rfl
    rw [hσ]
    simp only [Option.bind_some]
    change (thread Q L g).next (.inl s, n) e = none ∨
      ∃ s' n', (thread Q L g).next (.inl s, n) e = some (some (.inl s', n')) ∧ StartRef1 s' n'
    have hc2 := start_cls hR (start_ev hp hX he hσ)
    exact start_next1 hR (start_ev hp hX he hσ) hes hc2.1 hc2.2

/-- **Before its shuffle every thread is followed** with `Ref1`. -/
theorem start_fol1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hc : ((X.tr g).take k).countP Execution.isShfl = 0) :
    Frame.FollowedAt (thread Q L) (fun g => Ref1 Q L g) X g k := by
  rcases start_followed1 hp hX k hc with h0 | ⟨s, n, hσ, hR⟩
  · exact ⟨by rw [h0]; simp, fun d hd => by rw [h0] at hd; cases hd⟩
  · refine ⟨by rw [hσ]; simp, fun d hd => ?_⟩
    rw [hσ] at hd
    cases hd
    exact hR

/-- A position with no shuffle before it is a startup state with `StartRef1` and, for an event
that is no undefined behaviour, the startup's shape. -/
theorem start_at1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    {e : Event} (he : X.get (h, j) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hc : ((X.tr h).take j).countP Execution.isShfl = 0) :
    ∃ s n, Frame.stateAt (thread Q L) X h j = some (some (.inl s, n)) ∧ StartRef1 s n ∧
      Startup.Ev L h s e := by
  rcases start_followed1 hp hX j hc with h0 | ⟨s, n, hσ, hR⟩
  · rcases Frame.fired (C := thread Q L) (fun g hg => thread_sound hp hg) hX he with
      ⟨σ, o, hσ', -⟩ | ⟨-, pc, f, hf⟩
    · rw [h0] at hσ'; cases hσ'
    · exact absurd (by rw [hf]) (hu f)
  · exact ⟨s, n, hσ, hR, start_ev hp hX he hσ hu⟩

/-- **What the startup's shuffle receives**, in the first stage: lane 0's warp index. -/
theorem start_recv1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : DpLane L g) {k : Nat} {recv : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩)
    (hc : ((X.tr g).take k).countP Execution.isShfl = 0) :
    recv = b32 (g % L.block / 32) := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have hcv : ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1)) = 0 :=
    List.countP_eq_zero.mpr fun e he' => by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he')
      simp [novote hX (i := (g, i)) hi]
  have IH : Frame.GoodUpTo (thread Q L) (fun g => Ref1 Q L g) X (g % L.block / 32) (0 + 0) := by
    intro h j _ hj
    apply start_fol1 hp hX
    have : ((X.tr h).take j).countP Execution.isShfl ≤
        ((X.tr h).take j).countP Frame.isColl :=
      List.countP_mono_left fun e _ hs => by simp [Frame.isColl, hs]
    omega
  obtain ⟨j, pc', b', c', r', o', hget, hG, hcs, -⟩ := Frame.shfl_src (C := thread Q L)
    (J := fun g => Ref1 Q L g) hb hX hg.1 rfl he hc IH
    (fun _ _ _ _ _ he' hv _ _ _ => by rw [novote hX he'] at hv; cases hv)
    (fun _ _ _ _ _ he' hG' hs _ => by
      obtain ⟨s, n, -, hS, hE⟩ :=
        start_at1 hp hX he' (by simp) (by unfold Frame.cnt at hs; omega)
      exact (start_kind1 hS hE).1 rfl)
  have hsl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨-, hsW, -, -, -⟩ := Frame.lane_facts hb hg.1 rfl hsl
  obtain ⟨s, n, -, hS, hE⟩ := start_at1 hp hX hget (by simp) hcs
  obtain ⟨recv', ok', heq⟩ := (start_kind1 hS hE).2 (by simp [Execution.isShfl])
  simp only [Event.mk.injEq, Kind.shfl.injEq] at heq
  rw [heq.2.2.1, hsW]


/-! ### The steps of the first stage -/

/-- An event of a startup state other than the shuffles is no shuffle. -/
theorem start_noShfl {s : Startup.D} {n : Cls → Nat} {e : Event} (hR : StartRef1 s n)
    (hs : s.site ≠ .shfl)
    (hev : (∀ f, e.kind ≠ .ub f) → Startup.Ev L g s e) : Execution.isShfl e = false := by
  by_cases hu : ∀ f, e.kind ≠ .ub f
  · have hE := hev hu
    obtain ⟨site, tm, x, bw⟩ := s
    simp only at hs
    cases site
    case enter r => exact absurd rfl (hR.1 r)
    all_goals simp only [Startup.Ev] at hE
    all_goals first
      | exact absurd rfl hs
      | (subst hE; rfl)
      | (obtain ⟨_, _, rfl⟩ := hE; rfl)
      | (obtain ⟨_, _, rfl, _⟩ := hE; rfl)
  · simp only [not_forall, not_not] at hu
    obtain ⟨f, hf⟩ := hu
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    rfl

/-- **The startup steps a lane well in the first stage**: into the prologue or the worker
fragment with the recorded base word after the shuffle, whose received word is the warp index
(`start_recv1`). -/
theorem start_step1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : DpLane L g) {k : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n))) (hR : StartRef1 s n) :
    Frame.StepGood (thread Q L) (fun g => Ref1 Q L g) g (.inl s, n) e := by
  have hev : (∀ f, e.kind ≠ .ub f) → Startup.Ev L g s e := start_ev hp hX he hσ
  by_cases hs : s.site = .shfl
  · obtain ⟨site, tm, x, bw⟩ := s
    simp only at hs
    subst hs
    have h0 : n .shfl = 0 := hR.2.1
    by_cases hu : ∀ f, e.kind ≠ .ub f
    · obtain ⟨recv, ok, rfl⟩ := hev hu
      have hcnt : ((X.tr g).take k).countP Execution.isShfl = 0 := by
        have := fcount hσ .shfl
        simp only [cls] at this
        omega
      have hrv := start_recv1 hp hX hg he hcnt
      subst hrv
      by_cases h4 : g % L.block / 32 < 4
      · have hw4 : Arith32.scmpi .lt .u (BitVec.ofNat 64 (g % L.block / 32)) 4 = true := by
          generalize g % L.block / 32 = w at h4 ⊢
          interval_cases w <;> decide
        have hgate : Gate L g ⟨.enter .dp, tm, BitVec.ofNat 64 (g % L.block / 32), bw⟩ = true := by
          simp only [Gate, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
          omega
        have hn : (thread Q L g).next (.inl ⟨.shfl, tm, x, bw⟩, n)
            ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 (b32 (g % L.block / 32)) ok⟩ =
            some (some (.inr ⟨.inl (.dp tm bw), (frag Q L g (.dp tm bw)).init⟩,
              Code.bump cls n ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31
                (b32 (g % L.block / 32)) ok⟩)) := by
          simp only [thread, Code.roleThread, Code.counted, Code.glue, Startup.code]
          simp [Startup.succ, b32, Startup.entryOf, hw4, Code.enter, Code.gatedExit,
            Startup.enterOf, sel, hgate]
        refine ⟨by rw [hn]; simp, fun σ' h' => ?_⟩
        rw [hn] at h'
        cases h'
        exact ⟨by simp [Code.bump, cls, Execution.isShfl], ProA.pref_init _ rfl,
          fun h => absurd h (show ¬ 179 < 27 by decide)⟩
      · have hw4 : Arith32.scmpi .lt .u (BitVec.ofNat 64 (g % L.block / 32)) 4 = false := by
          have h8 := hg.2
          generalize g % L.block / 32 = w at h4 h8 ⊢
          interval_cases w <;> first | omega | decide
        have hgate : WGate L g ⟨.enter .worker, tm, BitVec.ofNat 64 (g % L.block / 32), bw⟩ =
            true := by
          simp only [WGate, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
          omega
        have hn : (thread Q L g).next (.inl ⟨.shfl, tm, x, bw⟩, n)
            ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 (b32 (g % L.block / 32)) ok⟩ =
            some (some (.inr ⟨.inl (.worker bw), (frag Q L g (.worker bw)).init⟩,
              Code.bump cls n ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31
                (b32 (g % L.block / 32)) ok⟩)) := by
          simp only [thread, Code.roleThread, Code.counted, Code.glue, Startup.code]
          simp [Startup.succ, b32, Startup.entryOf, hw4, Code.enter, Code.gatedExit,
            Startup.enterOf, sel, hgate]
        refine ⟨by rw [hn]; simp, fun σ' h' => ?_⟩
        rw [hn] at h'
        cases h'
        show 1 ≤ Code.bump cls n _ .shfl ∧
          WRef bw (.worker ⟨.loop, Worker.workerPro Q L g bw⟩) ∧ _
        exact ⟨by simp [Code.bump, cls, Execution.isShfl], ⟨⟨Or.inl rfl,
          by simp [Worker.workerPro]⟩, rfl⟩, .inl (.inl rfl), by omega⟩
    · simp only [not_forall, not_not] at hu
      obtain ⟨f, hf⟩ := hu
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      refine ⟨?_, fun σ' h' => ?_⟩ <;>
        simp [thread, Code.roleThread, Code.counted, Code.glue, Startup.code, Startup.succ] at *
  · have hc2 := start_cls hR hev
    rcases start_next1 hR hev (start_noShfl hR hs hev) hc2.1 hc2.2 with h | ⟨s', n', h, hR'⟩
    · exact ⟨by rw [h]; simp, fun σ' h' => by rw [h] at h'; cases h'⟩
    · refine ⟨by rw [h]; simp, fun σ' h' => ?_⟩
      rw [h] at h'
      cases h'
      exact hR'

/-- **The prologue steps a lane well in the first stage**, over the recorded base word; at its
exit the thread enters the softmax–epilogue fragment or the stub, which owe nothing. -/
theorem pro_step1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hR : 1 ≤ n .shfl ∧ ProA.PRef Q L g tm bw d ∧
      (179 < d.site.pc → 1 ≤ n .fence ∨ 1 ≤ n .ub)) :
    Frame.StepGood (thread Q L) (fun g => Ref1 Q L g) g (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) e := by
  obtain ⟨hn1, hP, hF⟩ := hR
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, -, ⟨hi, hx⟩, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) = d.site.pc := rfl
  rw [hpc] at hc hf
  have hfnc : d.site = .fnc0 → cls .fence e = true := by
    intro hs
    rw [hs] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
    rw [Proof.EvD.fires_fenceProxy_async hf]
    rfl
  have hbar : d.site = .bar18 → cls (.bar 1) e = true := by
    intro hs
    rw [hs] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_573)
    rw [Proof.EvD.fires_barSync_imm (by decide) hf]
    rfl
  have hx' : d.site ≠ .exit := fun h => by simp [Code.gatedExit, ProA.exitOf, h] at hx
  obtain ⟨hns, hsucc⟩ := ProA.ref_next hp hg hP (pro_expect hp hX he hσ hP) hx'
  have hb : 1 ≤ Code.bump cls n e .shfl := by simp only [Code.bump]; omega
  have hfge := bump_ge .fence n e
  have hbge := bump_ge (.bar 1) n e
  have huge := bump_ge .ub n e
  unfold Frame.StepGood
  rw [next_pro]
  rcases h : ProA.next L g d e with _ | _ | d'
  · simp
  · exact absurd h hns
  · refine ⟨by simp, fun σ' h' => ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h'
    subst h'
    have hP' := hsucc d' h
    cases hxo : ProA.exitOf d' with
    | none =>
      rw [Code.enter_none (by simp [Code.gatedExit, hxo])]
      refine ⟨hb, hP', fun hd => ?_⟩
      by_cases hd0 : 179 < d.site.pc
      · rcases hF hd0 with h1 | h1
        · exact .inl (by omega)
        · exact .inr (by omega)
      · have hs := cross_fnc0 h (by omega) hd
        left
        simp only [Code.bump, hfnc hs, ↓reduceIte]
        omega
    | some u =>
      have hxs : d'.site = .exit := by
        obtain ⟨site, dt⟩ := d'
        cases site <;> simp_all [ProA.exitOf]
      have hs := exit_from_bar18 h hxs
      have hF' := hF (by rw [hs]; decide)
      unfold Code.enter
      split
      · refine ⟨?_, ?_⟩
        · rcases hF' with h1 | h1
          · exact .inl (by omega)
          · exact .inr (by omega)
        · left
          simp only [Code.bump, hbar hs, ↓reduceIte]
          omega
      · rename_i hge
        simp [Code.gatedExit, hxo] at hge

/-- **The worker fragment steps a lane well in the first stage**, at a state where the dispatch
does not enter the MMA role with a base word failing `baseOk`. -/
theorem worker_step1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {tm : Value} {σ : Proof.WComp.WSt} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.worker tm), σ⟩, n)))
    (hR : 1 ≤ n .shfl ∧ WRef tm σ ∧ (WEarly σ ∨ 1 ≤ n (.bar 1) ∨ 1 ≤ n .ub) ∧
      4 ≤ g % L.block / 32)
    (hnS : ¬ S1 Q L g (.inr ⟨.inl (.worker tm), σ⟩, n)) :
    Frame.StepGood (thread Q L) (fun g => Ref1 Q L g) g (.inr ⟨.inl (.worker tm), σ⟩, n) e := by
  obtain ⟨hn1, hW, hE, hw4⟩ := hR
  have hb : 1 ≤ Code.bump cls n e .shfl := by simp only [Code.bump]; omega
  have hbge := bump_ge (.bar 1) n e
  have huge := bump_ge .ub n e
  have hok : ∀ w, σ = .worker w → w.site = .ldRole → Proof.WComp.baseOk w.P := by
    intro w hw hs
    subst hw
    by_contra hc
    exact hnS ⟨hs, hc⟩
  unfold Frame.StepGood
  rw [next_worker]
  have hne := wnext_ne_of (L := L) (g := g) (e := e) hW.1 hok
  rcases h : Proof.WComp.next L g σ e with _ | _ | σ'
  · simp
  · exact absurd h hne
  · refine ⟨by simp, fun σ'' h' => ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h'
    subst h'
    refine ⟨hb, wnext_ref hW h, ?_, hw4⟩
    rcases hE with hE | h1 | h1
    · cases σ with
      | worker w =>
        obtain ⟨s, P⟩ := w
        simp only [WEarly] at hE
        rcases hE with hs | hs
        · subst hs
          simp only [Proof.WComp.next, Proof.Worker.next, Option.map_some,
            Option.some.injEq] at h
          subst h
          exact .inl (.inr rfl)
        · subst hs
          obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
            Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
          have hpc : (thread Q L g).pc (.inr ⟨.inl (.worker tm), .worker ⟨.bar2, P⟩⟩, n) =
              2338 := rfl
          rw [hpc] at hc hf
          obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_27)
          have he' := Proof.EvD.fires_barSync_imm (by decide) hf
          subst he'
          right; left
          simp only [Code.bump, cls, beq_self_eq_true, ↓reduceIte]
          omega
      | _ => exact hE.elim
    · exact .inr (.inl (by omega))
    · exact .inr (.inr (by omega))

/-- **The first stage of the following**: every lane of the launch is followed with `Ref1` at
every position before which it has not been at a state of `S1`. No source of the base word is
used. -/
theorem good1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : DpLane L g) (k : Nat) (hB : Frame.Before (thread Q L) (fun g => S1 Q L g) X g k) :
    Frame.FollowedAt (thread Q L) (fun g => Ref1 Q L g) X g k :=
  Frame.followedUntilOn (Q := DpLane L) (Frame.inductive_lex (Frame.collUpTo X))
    (fun _ _ => ref1_init)
    (fun g k σ e hg he hσ hR hnS _ => by
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · exact start_step1 hp hX hg he hσ hR
      · rename_i i
        cases i with
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · exact pro_step1 hp hX he hσ hR
          · exact absurd trivial hnS
          · exact absurd trivial hnS
        | worker tm => exact worker_step1 hp hX he hσ hR hnS
      · exact hR.elim) hg k hB

end
end PTX.Kernels.InklingRelDecode.Proof2
