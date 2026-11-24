-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Race
public import Lemmas.Flow.ElectLead

@[expose] public section

/-! # The KV ring's per-slot counts along the loader and the MMA warp

The KV ring of a CTA has three slots `s`, each with a full barrier `kv_ready s` and an empty
barrier `kv_empty s`. The ring's protocol (`SingleTmaRing`) bounds a producer's or consumer's
operations on a slot by its successful polls of the other barrier, and fixes the parity of each
successful poll by the poller's earlier ones. These are counts of a thread's events; here they
are closed forms of the thread's state, kept along the thread like `ld_page`:

* **the loader** (`LdCnt`): at iteration `i` (from `num_pre` on) the thread's successful polls of
  `kv_empty s` are the iterations of slot `s` before `i` (`slotCnt num_pre i s`), plus one past the
  poll of iteration `i` when `i % 3 = s`; its arrivals on `kv_ready s` and its copies completing on
  it are at most one and eight per such iteration;
* **the MMA warp** (`MmCnt`): at iteration `i` its successful polls of `kv_ready s` are the
  iterations of slot `s` before `i` (`cnt0 i s`), plus one past the poll of iteration `i`; its
  commits to `kv_empty s` are at most one per earlier PV half of slot `s`;
* before either role a worker thread has made no event that uses an mbarrier (`objN`), which is
  how both forms start: a worker reaches the dispatch's role entry at barrier-1 count 1, before
  any role.

The pure steps are `ldCnt_step` and `mmCnt_step`; `kc_inv` keeps the invariant along every
thread. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Counts -/

/-- An event that may use an mbarrier object of the ring: an arrival, a poll, a tensor copy or a
commit. -/
def isObjEv (e : Event) : Bool :=
  match e.kind with
  | .arrive .. | .wait .. | .tensorIssue .. | .tc (.commit _) => true
  | _ => false

/-- The thread's events that may use a ring object. -/
def objN (es : List Event) : Nat := es.countP isObjEv

/-- The iterations below `i` of slot `s` (for `s < 3`). -/
def cnt0 (i s : Nat) : Nat := (i + 2 - s) / 3

/-- The iterations in `[a, i)` of slot `s`. -/
def slotCnt (a i s : Nat) : Nat := cnt0 i s - cnt0 a s

theorem cnt0_succ {i s : Nat} (hs : s < 3) :
    cnt0 (i + 1) s = cnt0 i s + if i % 3 = s then 1 else 0 := by
  unfold cnt0; split <;> omega

theorem slotCnt_succ {a i s : Nat} (hs : s < 3) (ha : a ≤ i) :
    slotCnt a (i + 1) s = slotCnt a i s + if i % 3 = s then 1 else 0 := by
  unfold slotCnt cnt0; split <;> omega

theorem slotCnt_self (a s : Nat) : slotCnt a a s = 0 := by simp [slotCnt]

/-- The parity of the loader's successful poll: with `δ` the slot's preload, the polls before
iteration `i` of slot `i % 3` have the parity `1 - (i / 3) % 2` less `1 - δ`. -/
theorem slotCnt_parity {a i : Nat} (ha : a ≤ 3) (hai : a ≤ i) :
    (1 - i / 3 % 2) % 2 = (slotCnt a i (i % 3) + (1 - if i % 3 < a then 1 else 0)) % 2 := by
  unfold slotCnt cnt0; split <;> omega

theorem cnt0_parity (i : Nat) : i / 3 % 2 = (cnt0 i (i % 3) + 0) % 2 := by
  unfold cnt0; omega

theorem countP_le_objN {p : Event → Bool} (hp : ∀ e, p e = true → isObjEv e = true)
    (es : List Event) : es.countP p ≤ objN es :=
  List.countP_mono_left fun e _ h => hp e h

theorem okPoll_obj (m : Loc) : ∀ e, okPoll m e = true → isObjEv e = true := by
  intro e h
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [okPoll, sourceWaitSuccess, isObjEv]

theorem arrivesOn_obj (m : Loc) : ∀ e, arrivesOn m e = true → isObjEv e = true := by
  intro e h
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [arrivesOn, sourceArrive, isObjEv]

theorem issuesTo_obj (m : Loc) : ∀ e, issuesTo m e = true → isObjEv e = true := by
  intro e h
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [issuesTo, isObjEv]

theorem commitsTo_obj (m : Loc) : ∀ e, commitsTo m e = true → isObjEv e = true := by
  intro e h
  obtain ⟨pc, k⟩ := e
  cases k with
  | tc t => cases t <;> simp_all [commitsTo, isObjEv]
  | _ => simp_all [commitsTo]

theorem okPolls_zero {m : Loc} {es : List Event} (h : objN es = 0) : okPolls m es = 0 := by
  have := countP_le_objN (okPoll_obj m) es
  unfold okPolls; omega

theorem arrivals_zero {m : Loc} {es : List Event} (h : objN es = 0) : arrivals m es = 0 := by
  have := countP_le_objN (arrivesOn_obj m) es
  unfold arrivals; omega

theorem issues_zero {m : Loc} {es : List Event} (h : objN es = 0) :
    es.countP (issuesTo m) = 0 := by
  have := countP_le_objN (issuesTo_obj m) es
  omega

theorem commits_zero {m : Loc} {es : List Event} (h : objN es = 0) :
    es.countP (commitsTo m) = 0 := by
  have := countP_le_objN (commitsTo_obj m) es
  omega

/-! ### The ring's barriers -/

theorem kvReady_inj {c a b : Nat} : Proof.EvW.kvReady L c a = Proof.EvW.kvReady L c b ↔ a = b := by
  simp only [Proof.EvW.kvReady, Proof.EvW.barLoc, Proof.EvW.kvReadyOff, Loc.mk.injEq, true_and]
  omega

theorem kvEmpty_inj {c a b : Nat} : Proof.EvW.kvEmpty L c a = Proof.EvW.kvEmpty L c b ↔ a = b := by
  simp only [Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff, Loc.mk.injEq, true_and]
  omega

/-- The prologue's `num_pre` of a thread's CTA. -/
abbrev npOf (Q : Params) (L : Launch) (g : Nat) : Nat :=
  Proof.ProA.numPre Q (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)

/-! ### The loader -/

/-- The loop sites after the iteration's successful poll. -/
def polledS : Proof.Loader.Site → Bool
  | .wb0 | .arrive | .ldb0 | .wb1 | .el0 | .cp0a | .cp0b | .wb2 | .el1 | .cp1a | .cp1b | .ldb1
  | .wb3 | .el2 | .cp2a | .cp2b | .wb4 | .el3 | .cp3a | .cp3b => true
  | _ => false

/-- The loop sites after the iteration's arrival. -/
def arrivedS : Proof.Loader.Site → Bool
  | .ldb0 | .wb1 | .el0 | .cp0a | .cp0b | .wb2 | .el1 | .cp1a | .cp1b | .ldb1
  | .wb3 | .el2 | .cp2a | .cp2b | .wb4 | .el3 | .cp3a | .cp3b => true
  | _ => false

/-- The copies of the iteration before a loop site. -/
def cpDoneS : Proof.Loader.Site → Nat
  | .cp0b => 1 | .wb2 | .el1 | .cp1a => 2 | .cp1b => 3 | .ldb1 | .wb3 | .el2 | .cp2a => 4
  | .cp2b => 5 | .wb4 | .el3 | .cp3a => 6 | .cp3b => 7
  | _ => 0

/-- **The loader's counts on its CTA's ring** at state `d`, after the events `es`. -/
structure LdCnt (Q : Params) (L : Launch) (g : Nat) (d : Proof.Loader.D) (es : List Event) :
    Prop where
  pre : d.site.inLoop = false → d.site ≠ .bar1 → d.site ≠ .setMaxInc → objN es = 0
  i0 : d.site = .ld1 ∨ d.site = .bar0 → d.i = npOf Q L g
  lo : d.site.inLoop = true → npOf Q L g ≤ d.i
  P : d.site.inLoop = true → ∀ s < 3,
    okPolls (Proof.EvW.kvEmpty L (g / L.block) s) es =
      slotCnt (npOf Q L g) d.i s + if polledS d.site ∧ d.i % 3 = s then 1 else 0
  A : d.site.inLoop = true → ∀ s < 3,
    arrivals (Proof.EvW.kvReady L (g / L.block) s) es ≤
      slotCnt (npOf Q L g) d.i s + if arrivedS d.site ∧ d.i % 3 = s then 1 else 0
  C : d.site.inLoop = true → ∀ s < 3,
    es.countP (issuesTo (Proof.EvW.kvReady L (g / L.block) s)) ≤
      8 * slotCnt (npOf Q L g) d.i s + if d.i % 3 = s then cpDoneS d.site else 0
  /-- For a lane that leads its elections the copies are exact: it takes every copy branch. -/
  CE : d.site.inLoop = true → ∀ s < 3, ElectLead L g es →
    es.countP (issuesTo (Proof.EvW.kvReady L (g / L.block) s)) =
      8 * slotCnt (npOf Q L g) d.i s + if d.i % 3 = s then cpDoneS d.site else 0

/-- An election event a leading lane's run ends with returned its lane. -/
theorem lead_ld {es : List Event} {pc mk inst ld : Nat}
    (h : ElectLead L g (es ++ [⟨pc, .elect mk inst ld⟩])) : ld = laneOf L g :=
  ((electLead_snoc_elect rfl).mp h).2

theorem arrivals_snoc (m : Loc) (es : List Event) (e : Event) :
    arrivals m (es ++ [e]) = arrivals m es + if arrivesOn m e then 1 else 0 := by
  simp only [arrivals, List.countP_append, List.countP_singleton]

theorem countP_snoc' (p : Event → Bool) (es : List Event) (e : Event) :
    (es ++ [e]).countP p = es.countP p + if p e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

/-- **A loop step of the loader**, same iteration, by the count changes of its event. -/
theorem ldCnt_loop {d d' : Proof.Loader.D} {e : Event} {es : List Event}
    (hR : LdCnt Q L g d es) (hin : d.site.inLoop = true) (hin' : d'.site.inLoop = true)
    (hi : d'.i = d.i)
    (hP : ∀ s < 3, ((if polledS d.site ∧ d.i % 3 = s then 1 else 0) +
      if okPoll (Proof.EvW.kvEmpty L (g / L.block) s) e then 1 else 0) =
        (if polledS d'.site ∧ d.i % 3 = s then 1 else 0))
    (hA : ∀ s < 3, ((if arrivedS d.site ∧ d.i % 3 = s then 1 else 0) +
      if arrivesOn (Proof.EvW.kvReady L (g / L.block) s) e then 1 else 0) ≤
        (if arrivedS d'.site ∧ d.i % 3 = s then 1 else 0))
    (hC : ∀ s < 3, ((if d.i % 3 = s then cpDoneS d.site else 0) +
      if issuesTo (Proof.EvW.kvReady L (g / L.block) s) e then 1 else 0) ≤
        (if d.i % 3 = s then cpDoneS d'.site else 0))
    (hCE : ∀ s < 3, ElectLead L g (es ++ [e]) →
      ((if d.i % 3 = s then cpDoneS d.site else 0) +
        if issuesTo (Proof.EvW.kvReady L (g / L.block) s) e then 1 else 0) =
        (if d.i % 3 = s then cpDoneS d'.site else 0)) :
    LdCnt Q L g d' (es ++ [e]) where
  pre h := by rw [hin'] at h; cases h
  i0 h := by rcases h with h | h <;> rw [h] at hin' <;> cases hin'
  lo _ := hi ▸ hR.lo hin
  P _ s hs := by
    have := hR.P hin s hs
    have := hP s hs
    rw [okPolls_snoc, hi]
    omega
  A _ s hs := by
    have := hR.A hin s hs
    have := hA s hs
    rw [arrivals_snoc, hi]
    omega
  C _ s hs := by
    have := hR.C hin s hs
    have := hC s hs
    rw [countP_snoc', hi]
    omega
  CE _ s hs hl := by
    have := hR.CE hin s hs hl.of_snoc
    have := hCE s hs hl
    rw [countP_snoc', hi]
    omega

/-- **The end of an iteration**: the next iteration's poll, or the loop's exit. -/
theorem ldCnt_iter {d : Proof.Loader.D} {e : Event} {es : List Event}
    (hR : LdCnt Q L g d es) (hin : d.site.inLoop = true) (hpol : polledS d.site = true)
    (harr : arrivedS d.site = true) (hcp : cpDoneS d.site + 1 ≤ 8)
    (hP : ∀ s < 3, okPoll (Proof.EvW.kvEmpty L (g / L.block) s) e = false)
    (hA : ∀ s < 3, arrivesOn (Proof.EvW.kvReady L (g / L.block) s) e = false)
    (hC : ∀ s < 3, issuesTo (Proof.EvW.kvReady L (g / L.block) s) e = true → s = d.i % 3)
    (hCE : ∀ s < 3, ElectLead L g (es ++ [e]) →
      ((if d.i % 3 = s then cpDoneS d.site else 0) +
        if issuesTo (Proof.EvW.kvReady L (g / L.block) s) e then 1 else 0) =
        (if d.i % 3 = s then 8 else 0)) :
    LdCnt Q L g (Proof.Loader.afterIter d) (es ++ [e]) := by
  have hlo := hR.lo hin
  simp only [Proof.Loader.afterIter]
  split
  · refine ⟨fun _ h => absurd rfl h, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; rcases h with h | h <;> cases h
    all_goals intro h; cases h
  · refine ⟨?_, ?_, ?_, fun _ s hs => ?_, fun _ s hs => ?_, fun _ s hs => ?_,
      fun _ s hs hl => ?_⟩
    · intro h; cases h
    · intro h; rcases h with h | h <;> cases h
    · intro _; simp only; omega
    · have := hR.P hin s hs
      simp only [hpol, true_and] at this
      rw [okPolls_snoc, hP s hs, slotCnt_succ hs hlo]
      simp only [polledS, Bool.false_eq_true, false_and, ite_false]
      by_cases h : d.i % 3 = s <;> simp only [h, ite_true, ite_false] at this ⊢ <;> omega
    · have := hR.A hin s hs
      simp only [harr, true_and] at this
      rw [arrivals_snoc, hA s hs, slotCnt_succ hs hlo]
      simp only [arrivedS, Bool.false_eq_true, false_and, ite_false]
      by_cases h : d.i % 3 = s <;> simp only [h, ite_true, ite_false] at this ⊢ <;> omega
    · have := hR.C hin s hs
      have hc := hC s hs
      rw [countP_snoc', slotCnt_succ hs hlo]
      simp only [cpDoneS]
      by_cases h : d.i % 3 = s
      · simp only [h, ite_true] at this ⊢
        split <;> omega
      · simp only [h, ite_false] at this ⊢
        cases hq : issuesTo (Proof.EvW.kvReady L (g / L.block) s) e
        · simp only [Bool.false_eq_true, ite_false]; omega
        · exact absurd (hc hq).symm h
    · have h1 := hR.CE hin s hs hl.of_snoc
      have hc := hCE s hs hl
      rw [countP_snoc', slotCnt_succ hs hlo]
      simp only [cpDoneS, ite_self, Nat.add_zero]
      by_cases h : d.i % 3 = s
      · simp only [h, ite_true] at h1 hc ⊢; omega
      · simp only [h, ite_false] at h1 hc ⊢; omega

theorem objN_snoc (es : List Event) (e : Event) :
    objN (es ++ [e]) = objN es + if isObjEv e then 1 else 0 := countP_snoc' _ _ _

/-- The loader's states after the loop carry no counts. -/
theorem ldCnt_after {d : Proof.Loader.D} {es : List Event}
    (h : d.site = .bar1 ∨ d.site = .setMaxInc) : LdCnt Q L g d es := by
  have hin : d.site.inLoop = false := by rcases h with h | h <;> rw [h] <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ h1 h2; rcases h with h | h <;> simp_all
  · intro h'; rcases h with h | h <;> rcases h' with h' | h' <;> simp_all
  all_goals intro h'; rw [hin] at h'; cases h'

/-- A step before the loop, by an event that uses no object. -/
theorem ldCnt_pre {d' : Proof.Loader.D} {e : Event} {es : List Event} (h0 : objN es = 0)
    (he : isObjEv e = false) (hin : d'.site.inLoop = false)
    (hi : d'.site = .ld1 ∨ d'.site = .bar0 → d'.i = npOf Q L g) :
    LdCnt Q L g d' (es ++ [e]) := by
  refine ⟨?_, hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _; rw [objN_snoc, h0, he]; rfl
  all_goals intro h; rw [hin] at h; cases h

/-- The loop's first poll. -/
theorem ldCnt_start {d' : Proof.Loader.D} {e : Event} {es : List Event} (h0 : objN es = 0)
    (he : isObjEv e = false) (hs : d'.site = .wait) (hi : d'.i = npOf Q L g) :
    LdCnt Q L g d' (es ++ [e]) := by
  have h1 : objN (es ++ [e]) = 0 := by rw [objN_snoc, h0, he]; rfl
  refine ⟨?_, ?_, ?_, fun _ s hs' => ?_, fun _ s hs' => ?_, fun _ s hs' => ?_,
    fun _ s hs' _ => ?_⟩
  · intro h; rw [hs] at h; cases h
  · intro h; rcases h with h | h <;> rw [hs] at h <;> cases h
  · intro _; rw [hi]
  · rw [okPolls_zero h1, hi, hs, slotCnt_self]; simp [polledS]
  · rw [arrivals_zero h1]; omega
  · rw [issues_zero h1]; omega
  · rw [issues_zero h1, hi, hs, slotCnt_self]; simp [cpDoneS]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **One step of the loader keeps its counts.** -/
theorem ldCnt_step {d d' : Proof.Loader.D} {e : Event} {es : List Event}
    (hR : LdCnt Q L g d es) (hsh : Proof.EvW.LdShape Q L g d e)
    (hn : Proof.Loader.next L g d e = some (some d'))
    (hi0 : d.site = .ld0 → d'.i = npOf Q L g) :
    LdCnt Q L g d' (es ++ [e]) := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  have hpre := hR.pre
  have hi0' := hR.i0
  simp only at hpre hi0' hi0
  cases site
  all_goals simp only [Proof.EvW.LdShape] at hsh
  case setMaxDec =>
    obtain ⟨inst, rfl⟩ := hsh
    simp only [Proof.Loader.next, Option.some.injEq] at hn
    subst hn
    exact ldCnt_pre (hpre rfl (by decide) (by decide)) rfl rfl (by simp)
  case ld0 =>
    obtain ⟨ac, bs, rfl, -⟩ := hsh
    have hi := hi0 rfl
    simp only [Proof.Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact ldCnt_pre (hpre rfl (by decide) (by decide)) rfl rfl (fun _ => hi)
    · cases hn
  case ld1 =>
    obtain ⟨ac, bs, rfl, -⟩ := hsh
    simp only [Proof.Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact ldCnt_pre (hpre rfl (by decide) (by decide)) rfl rfl
        (fun _ => hi0' (.inl rfl))
    · cases hn
  case bar0 =>
    subst hsh
    simp only [Proof.Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split
      · exact ldCnt_after (.inl rfl)
      · exact ldCnt_start (hpre rfl (by decide) (by decide)) rfl rfl (hi0' (.inr rfl))
    · cases hn
  case bar1 =>
    simp only [Proof.Loader.next, Option.some.injEq] at hn
    subst hn
    exact ldCnt_after (.inr rfl)
  case setMaxInc =>
    simp only [Proof.Loader.next] at hn
    cases hn
  case wait =>
    obtain ⟨ok, rfl⟩ := hsh
    simp only [Proof.Loader.next] at hn
    cases ok
    · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at hn
      subst hn
      refine ldCnt_loop hR rfl rfl rfl ?_ ?_ ?_ ?_ <;> intro s hs <;>
        simp [okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo]
    · simp only [ite_true, Option.some.injEq] at hn
      subst hn
      refine ldCnt_loop hR rfl rfl rfl ?_ ?_ ?_ ?_ <;> intro s hs <;>
        simp [okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo, polledS, arrivedS,
          cpDoneS, kvEmpty_inj]
  case arrive =>
    subst hsh
    simp only [Proof.Loader.next, Option.some.injEq] at hn
    subst hn
    refine ldCnt_loop hR rfl rfl rfl ?_ ?_ ?_ ?_ <;> intro s hs <;>
      simp [okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo, polledS, arrivedS,
        cpDoneS, kvReady_inj]
  all_goals first
    | (obtain ⟨b, hb, rfl⟩ := hsh)
    | (obtain ⟨inst, ld, rfl⟩ := hsh)
    | (obtain ⟨ac, bs, rfl, -⟩ := hsh)
    | (obtain ⟨inst, rfl⟩ := hsh)
  all_goals simp only [Proof.Loader.next] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn
       subst hn
       first
         | (refine ldCnt_loop hR rfl rfl rfl ?_ ?_ ?_ ?_ <;> intro s hs <;>
            (try (intro hEL; have hld := lead_ld hEL; revert hld)) <;>
            simp [okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo, polledS,
              arrivedS, cpDoneS, Proof.EvW.ldCopy, Proof.EvW.kvCopySpec, kvReady_inj] <;>
            (try split_ifs) <;> omega)
         | (refine ldCnt_iter hR rfl rfl rfl (by simp [cpDoneS]) ?_ ?_ ?_ ?_ <;> intro s hs <;>
            (try (intro hEL; have hld := lead_ld hEL; revert hld)) <;>
            simp [okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo, cpDoneS,
              Proof.EvW.ldCopy, Proof.EvW.kvCopySpec, kvReady_inj] <;> (try split_ifs) <;>
            omega))

/-! ### The MMA warp -/

/-- The sites of an iteration (its QK or PV half). -/
def iterS : Proof.Mma.Site → Bool
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2
  | .pvSkip => true
  | _ => false

/-- The sites before the loop. -/
def preS : Proof.Mma.Site → Bool
  | .setMaxReg | .ldNum | .bar0 => true
  | _ => false

/-- The state is past its iteration's successful poll of `kv_ready`: past it in the QK half, and
in the PV half of an iteration that had a QK half. -/
def qkDoneS (d : Proof.Mma.D) : Bool :=
  match d.site with
  | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => true
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2
  | .pvSkip => decide (d.i < d.n)
  | _ => false

/-- **The MMA warp's counts on its CTA's ring** at state `d`, after the events `es`. -/
structure MmCnt (L : Launch) (g : Nat) (d : Proof.Mma.D) (es : List Event) : Prop where
  pre : preS d.site = true → objN es = 0
  F : iterS d.site = true → ∀ s < 3,
    okPolls (Proof.EvW.kvReady L (g / L.block) s) es =
      cnt0 d.i s + if qkDoneS d = true ∧ d.i % 3 = s then 1 else 0
  M : iterS d.site = true → ∀ s < 3,
    es.countP (commitsTo (Proof.EvW.kvEmpty L (g / L.block) s)) ≤
      cnt0 (d.i - 1) s + if d.site = .pvCommit2 ∧ (d.i - 1) % 3 = s then 1 else 0

theorem mmCnt_end {d : Proof.Mma.D} {es : List Event} (h1 : preS d.site = false)
    (h2 : iterS d.site = false) : MmCnt L g d es := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [h1] at h; cases h
  all_goals intro h; rw [h2] at h; cases h

/-- A step within an iteration, by the count changes of its event. -/
theorem mmCnt_loop {d d' : Proof.Mma.D} {e : Event} {es : List Event}
    (hR : MmCnt L g d es) (hin : iterS d.site = true) (hin' : iterS d'.site = true)
    (hi : d'.i = d.i)
    (hF : ∀ s < 3, ((if qkDoneS d = true ∧ d.i % 3 = s then 1 else 0) +
      if okPoll (Proof.EvW.kvReady L (g / L.block) s) e then 1 else 0) =
        (if qkDoneS d' = true ∧ d.i % 3 = s then 1 else 0))
    (hM : ∀ s < 3, ((if d.site = .pvCommit2 ∧ (d.i - 1) % 3 = s then 1 else 0) +
      if commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e then 1 else 0) ≤
        (if d'.site = .pvCommit2 ∧ (d.i - 1) % 3 = s then 1 else 0)) :
    MmCnt L g d' (es ++ [e]) := by
  refine ⟨?_, fun _ s hs => ?_, fun _ s hs => ?_⟩
  · intro h; cases hs' : d'.site <;> simp_all [preS, iterS]
  · have := hR.F hin s hs
    have := hF s hs
    rw [okPolls_snoc, hi]
    omega
  · have := hR.M hin s hs
    have := hM s hs
    rw [countP_snoc', hi]
    omega

/-- **The end of an iteration**: the next iteration's first site, or the loop's end. -/
theorem mmCnt_iter {d : Proof.Mma.D} {e : Event} {es : List Event}
    (hR : MmCnt L g d es) (hin : iterS d.site = true)
    (hq : d.i < d.n → qkDoneS d = true) (hle : d.i ≤ d.n) (hi1 : d.site = .pvCommit2 → 1 ≤ d.i)
    (hF : ∀ s < 3, okPoll (Proof.EvW.kvReady L (g / L.block) s) e = false)
    (hM : ∀ s < 3, commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e = false) :
    MmCnt L g (Proof.Mma.iterNext d) (es ++ [e]) := by
  simp only [Proof.Mma.iterNext]
  split
  · exact mmCnt_end rfl rfl
  · rename_i hne
    have hlt : d.i < d.n := by omega
    have hqd := hq hlt
    refine ⟨?_, fun _ s hs => ?_, fun _ s hs => ?_⟩
    · intro h; split at h <;> cases h
    · have := hR.F hin s hs
      simp only [hqd, true_and] at this
      rw [okPolls_snoc, hF s hs, cnt0_succ hs]
      by_cases h2 : d.i + 1 < d.n <;> by_cases h : d.i % 3 = s <;>
        simp [h2, h, qkDoneS] at this ⊢ <;> omega
    · have hMo := hR.M hin s hs
      rw [countP_snoc', hM s hs]
      have hm : cnt0 (d.i - 1) s ≤ cnt0 d.i s := by unfold cnt0; omega
      have hgoal : List.countP (commitsTo (Proof.EvW.kvEmpty L (g / L.block) s)) es ≤
          cnt0 d.i s := by
        by_cases hc2 : d.site = .pvCommit2 ∧ (d.i - 1) % 3 = s
        · have h1 := hi1 hc2.1
          have := cnt0_succ (i := d.i - 1) hs
          rw [show d.i - 1 + 1 = d.i by omega] at this
          simp only [hc2.2, ite_true] at this
          simp only [hc2, and_self, ite_true] at hMo
          omega
        · simp only [hc2, ite_false] at hMo
          omega
      by_cases h2 : d.i + 1 < d.n <;> simp [h2] <;> omega

/-- A step before the loop, by an event that uses no object. -/
theorem mmCnt_pre {d' : Proof.Mma.D} {e : Event} {es : List Event} (h0 : objN es = 0)
    (he : isObjEv e = false) (hp : preS d'.site = true) : MmCnt L g d' (es ++ [e]) := by
  have hit : iterS d'.site = false := by cases hs : d'.site <;> simp_all [preS, iterS]
  refine ⟨?_, ?_, ?_⟩
  · intro _; rw [objN_snoc, h0, he]; rfl
  all_goals intro h; rw [hit] at h; cases h

/-- The loop's first state. -/
theorem mmCnt_start {d' : Proof.Mma.D} {e : Event} {es : List Event} (h0 : objN es = 0)
    (he : isObjEv e = false) (hs : d'.site = .qkBar) (hi : d'.i = 0) :
    MmCnt L g d' (es ++ [e]) := by
  have h1 : objN (es ++ [e]) = 0 := by rw [objN_snoc, h0, he]; rfl
  refine ⟨?_, fun _ s hs' => ?_, fun _ s hs' => ?_⟩
  · intro h; rw [hs] at h; cases h
  · rw [okPolls_zero h1, hi]; simp [qkDoneS, hs, cnt0]; omega
  · rw [commits_zero h1]; omega

/-- The barriers of the MMA warp's other polls and commits are no barrier of the ring. -/
theorem pReady_ne {c b s : Nat} (hb : b < 2) (hs : s < 3) :
    Proof.EvW.pReady L c b ≠ Proof.EvW.kvReady L c s := by
  simp only [Proof.EvW.pReady, Proof.EvW.kvReady, Proof.EvW.barLoc, Proof.EvW.pReadyOff,
    Proof.EvW.kvReadyOff, ne_eq, Loc.mk.injEq, true_and]
  omega

theorem sReady_ne {c b s : Nat} (hb : b < 2) (hs : s < 3) :
    Proof.EvW.sReady L c b ≠ Proof.EvW.kvEmpty L c s := by
  simp only [Proof.EvW.sReady, Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.sReadyOff,
    Proof.EvW.kvEmptyOff, ne_eq, Loc.mk.injEq, true_and]
  omega

theorem oDone_ne {c s : Nat} (hs : s < 3) :
    Proof.EvW.oDone L c ≠ Proof.EvW.kvEmpty L c s := by
  simp only [Proof.EvW.oDone, Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.oDoneOff,
    Proof.EvW.kvEmptyOff, ne_eq, Loc.mk.injEq, true_and]
  omega

theorem oFinal_ne {c s : Nat} (hs : s < 3) :
    Proof.EvW.oFinal L c ≠ Proof.EvW.kvEmpty L c s := by
  simp only [Proof.EvW.oFinal, Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.oFinalOff,
    Proof.EvW.kvEmptyOff, ne_eq, Loc.mk.injEq, true_and]
  omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
/-- **One step of the MMA warp keeps its counts.** -/
theorem mmCnt_step {d d' : Proof.Mma.D} {e : Event} {es : List Event}
    (hR : MmCnt L g d es) (hsh : Proof.EvW.MmShape L g d e) (hI : Proof.Mma.Inv d)
    (hn : Proof.Mma.next L g d e = some (some d')) : MmCnt L g d' (es ++ [e]) := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  have hpre := hR.pre
  simp only at hpre
  have hb2 : ∀ x, x % 2 < 2 := fun x => Nat.mod_lt _ (by omega)
  cases site
  all_goals simp only [Proof.EvW.MmShape] at hsh
  case bar0 =>
    subst hsh
    simp only [Proof.Mma.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      simp only [Proof.Mma.start]
      split
      · exact mmCnt_end rfl rfl
      · exact mmCnt_start (hpre rfl) rfl rfl (hI.pre trivial)
    · cases hn
  all_goals first
    | (obtain ⟨da, db, dsc, h1, h2, h3, rfl⟩ := hsh)
    | (obtain ⟨db, dsc, h1, h2, rfl⟩ := hsh)
    | (obtain ⟨recv, ok, rfl⟩ := hsh)
    | (obtain ⟨inst, ld, rfl⟩ := hsh)
    | (obtain ⟨ac, bs, rfl, -⟩ := hsh)
    | (obtain ⟨ok, rfl⟩ := hsh)
    | (obtain ⟨inst, rfl⟩ := hsh)
    | subst hsh
  all_goals simp only [Proof.Mma.next, Proof.Mma.afterQk, Proof.Mma.qkNext,
    Proof.Mma.pvNext] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn
       subst hn
       first
         | exact mmCnt_end rfl rfl
         | exact mmCnt_pre (hpre rfl) rfl rfl
         | (refine mmCnt_loop hR rfl rfl rfl ?_ ?_ <;> intro s hs <;>
            (try have := hI.qk True.intro) <;>
            (try have := hI.pv True.intro) <;>
            simp_all [okPoll, sourceWaitSuccess, commitsTo, qkDoneS, Proof.EvW.commitSpec,
              kvReady_inj, kvEmpty_inj, pReady_ne (hb2 _) hs, sReady_ne (hb2 _) hs,
              oDone_ne hs] <;>
            (try split_ifs) <;> omega)
         | (refine mmCnt_iter hR rfl ?_ ?_ ?_ ?_ ?_ <;>
            (try intro s hs) <;>
            (try have := hI.qk True.intro) <;>
            (try have := hI.pv True.intro) <;>
            simp_all [okPoll, sourceWaitSuccess, commitsTo, qkDoneS, Proof.EvW.commitSpec,
              oDone_ne, sReady_ne] <;> omega))

/-! ### Along a thread -/

/-- The positions of the instructions whose events may use an mbarrier object. -/
def objPcs : List Nat :=
  [134, 138, 142, 146, 150, 154, 158, 162, 166, 170, 174, 178, 193, 211, 217, 226, 231, 237, 253,
    259, 268, 273, 279, 295, 301, 310, 315, 1013, 1257, 2239, 2374, 2378, 2389, 2391, 2394, 2396,
    2404, 2406, 2410, 2412, 2462, 2499, 2510, 2546, 2548, 2553, 2565]

theorem kernel_obj_pcs : OpPcsFast kernel.code objectOp objPcs = true := by decide +kernel

/-- An event that may use a ring object is fired by an object instruction. -/
theorem obj_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (he : isObjEv e = true) :
    pc ∈ objPcs := by
  refine OpPcsFast.mem kernel_obj_pcs hc ?_
  cases hop : objectOp ins.op
  · exfalso
    refine notObject_of_op hop hf ?_
    obtain ⟨epc, k⟩ := e
    cases k with
    | tc tk => cases tk <;> simp_all [isObjEv, ObjectKind]
    | _ => simp_all [isObjEv, ObjectKind]
  · rfl

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_obj : ∀ s : Startup.Site, s.pc ∈ objPcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem worker_obj : ∀ s : Proof.Worker.Site, s.pc ∈ objPcs → False := by site_none

/-- A worker step from the dispatch into the MMA warp enters it at its first site. -/
theorem w_next_mma {w : Proof.Worker.D} {e : Event} {d' : Proof.Mma.D} {P' : Proof.Loader.Pro}
    (h : Proof.WComp.next L g (.worker w) e = some (some (.mma d' P'))) :
    d'.site = .setMaxReg := by
  by_cases hs : w.site = .ldRole
  · obtain ⟨site, P⟩ := w
    simp only at hs
    subst hs
    change Proof.WComp.dispatch L g P e = _ at h
    unfold Proof.WComp.dispatch at h
    split at h
    · rename_i d0 hd
      rcases (Proof.EvW.ldRole_next hd).2 with hs | hs | hs | hs | hs <;> rw [hs] at h <;>
        simp only [Proof.WComp.roleStart] at h
      all_goals (repeat' split at h)
      all_goals first
        | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
        | (simp only [Option.some.injEq, Proof.WComp.WSt.mma.injEq] at h
           obtain ⟨rfl, -⟩ := h
           rfl)
    · cases h
    · cases h
  · rw [Proof.EvW.next_worker_map hs] at h
    obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
    cases ha

/-- **The ring's counts along a thread**: zero in the startup and in the dispatch before any
role, the loader's and the MMA warp's closed forms in their roles. -/
def KC (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → List Event → Prop
  | (.inl _, _), es => objN es = 0
  | (.inr ⟨.inl (.worker _), .worker _⟩, _), es => es.countP (Execution.isBarId 1) ≤ 1 → objN es = 0
  | (.inr ⟨.inl (.worker _), .loader d _⟩, _), es => LdCnt Q L g d es
  | (.inr ⟨.inl (.worker _), .mma d _⟩, _), es => MmCnt L g d es
  | _, _ => True

/-- A role's last step returns to the loop's head at barrier-1 count at least 3. -/
theorem loop_c1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k + 1 < (X.tr g).length) {tm : Value}
    {σ : Proof.WComp.WSt} {n n' : Cls → Nat} {P : Proof.Loader.Pro} (hr : isRole σ = true)
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), σ⟩, n)))
    (hσ' : Frame.stateAt (thread Q L) X g (k + 1) =
      some (some (.inr ⟨.inl (.worker tm), .worker ⟨.loop, P⟩⟩, n'))) :
    3 ≤ ((X.tr g).take (k + 1)).countP (Execution.isBarId 1) := by
  have h1 := role_count hp hX hg (by omega) hr hσ
  have h2 : _ % 3 = _ := w1_inv hp hX hg (k + 1) hk _ hσ'
  have h3 := countP_take_mono (Execution.isBarId 1) (X.tr g) (show k ≤ k + 1 by omega)
  simp only [wph] at h2
  have : 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) := by rw [h1]; split <;> omega
  omega

set_option maxHeartbeats 400000 in
/-- **The ring's counts along every thread.** -/
theorem kc_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      KC Q L g σ ((X.tr g).take k) := by
  have hb : L.block = 256 := hp.block
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rfl
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hσ'0 := hσ'
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
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
      have hget : X.get (g, k) = some e := he
      -- an event at a state whose site is no object position uses no object
      have hno : (thread Q L g).pc σ ∉ objPcs → isObjEv e = false := by
        intro hpc
        cases hq : isObjEv e
        · rfl
        · exact absurd (obj_pc hc hf hq) hpc
      have hc1 := countP_take_mono (Execution.isBarId 1) (X.tr g) (show k ≤ k + 1 by omega)
      rw [htake] at hc1 ⊢
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup
        have he0 : isObjEv e = false := hno (fun h => startup_obj st.site h)
        have h0 : objN ((X.tr g).take k ++ [e]) = 0 := by
          rw [objN_snoc, hR0, he0]; rfl
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · trivial
          · intro _; exact h0
          · trivial
        · exact h0
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => trivial
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          have hkk : k + 1 < (X.tr g).length := hk
          cases d with
          | worker ww =>
            have he0 : isObjEv e = false := hno (fun h => worker_obj ww.site h)
            have hR0' : _ ≤ 1 → objN _ = 0 := hR0
            have h0 : ((X.tr g).take k).countP (Execution.isBarId 1) ≤ 1 →
                objN ((X.tr g).take k ++ [e]) = 0 := by
              intro h1; rw [objN_snoc, hR0' h1, he0]; rfl
            cases σw' with
            | worker w' => exact fun h1 => h0 (by omega)
            | loader d' P' =>
              have hs := (w_next_loader hσw).resolve_right (by
                rintro ⟨_, h, -⟩; cases h)
              have hrc := role_count hp hX hg hk rfl hσ'0
              simp only [wph, ldPh, hs] at hrc
              rw [htake] at hrc
              exact ldCnt_pre (hR0' (by simp at hrc; omega)) he0 (by rw [hs]; rfl)
                (by intro h; rcases h with h | h <;> rw [hs] at h <;> cases h)
            | mma d' P' =>
              have hs := w_next_mma hσw
              have hrc := role_count hp hX hg hk rfl hσ'0
              simp only [wph, mmPh, hs] at hrc
              rw [htake] at hrc
              exact mmCnt_pre (hR0' (by simp at hrc; omega)) he0 (by rw [hs]; rfl)
            | _ => trivial
          | loader d P =>
            rcases role_succ (σ := .loader d P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : d.site ≠ .setMaxInc := by intro h; simp [wph, ldPh, h] at hph
              rw [Proof.EvW.next_loader_map P hs] at hσw
              obtain ⟨d', hld, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              have hR0' : LdCnt Q L g d ((X.tr g).take k) := hR0
              refine ldCnt_step hR0' (ld_shape hp hX hget hnE hk0) hld ?_
              intro h0
              have hsh := ld_shape hp hX hget hnE hk0
              unfold Proof.EvW.LdShape at hsh
              rw [h0] at hsh
              obtain ⟨ac, bs, rfl, hloc, hsz, -⟩ := hsh
              have hw : 128 ≤ g % L.block := by
                have : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlt _ hk0).2
                omega
              have hbs := pair_read hp hX hget hw 0 (by rw [hloc]; simp) hsz
              obtain ⟨site, pro, i, nn, p0, p1, ln⟩ := d
              simp only at h0
              subst h0
              simp only [Proof.Loader.next, hbs, pairVal, rebuild_b32, Option.some.injEq] at hld
              subst hld
              have := numPre_le3 Q (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)
              simp only [Proof.Loader.readI, Proof.Raw.word32Of_b32, Option.getD_some, npOf]
              omega
            · intro _
              exfalso
              have := loop_c1 hp hX hg hk rfl hk0 hσ'0
              rw [htake] at this
              omega
          | mma d P =>
            rcases role_succ (σ := .mma d P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : d.site ≠ .setMaxRegInc := by intro h; simp [wph, mmPh, h] at hph
              rw [Proof.EvW.next_mma_map P hs] at hσw
              obtain ⟨d', hmn, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              have hR0' : MmCnt L g d ((X.tr g).take k) := hR0
              cases o with
              | none => exact absurd (fires_none_ends hf) hnE
              | some u =>
                have hsh : Proof.EvW.MmShape L g d e := frag_ev hp hg hJ hat hi hc hf
                exact mmCnt_step hR0' hsh (hi : Proof.WComp.Inv L g (.mma d P)).1 hmn
            · intro _
              exfalso
              have := loop_c1 hp hX hg hk rfl hk0 hσ'0
              rw [htake] at this
              omega
          | idle d =>
            rcases role_succ (σ := .idle d) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : d.site ≠ .inc := by intro h; simp [wph, idPh, h] at hph
              rw [Proof.EvW.next_idle_map hs] at hσw
              obtain ⟨a, -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              trivial
            · intro _
              exfalso
              have := loop_c1 hp hX hg hk rfl hk0 hσ'0
              rw [htake] at this
              omega
          | exit x =>
            obtain ⟨x', rfl⟩ := exit_succ hσw
            trivial
      · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
