-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollStep0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Recv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 1's lanes: the states of the head and the dispatch

Facts shared by the classes of warps 4 to 7: no state of a thread is at an exit of the head
(`head_noExit`: the exits are entered at once), the head's `setmaxnreg` leads to its shuffle, whose
dispatch (on the launch's warp word, `head_recv_follow`) leads to the sub-role of the lane's warp
(`hsh_next`), and a lane at the head's shuffle has made its register request (`hsh_req`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

theorem enter_inl {s s' : Wg1.Site}
    (h : Code.enter (wg1HeadCode P L x) (Code.withStubsAt (subFrag P L x) (SubEntry.pc P L x))
      (Code.gatedExit (wg1Enter P L x) (subSel P L x)) s' = .inl s) :
    s = s' ∧ Wg1.exitOf s = none := by
  unfold Code.enter at h
  cases hg : Code.gatedExit (wg1Enter P L x) (subSel P L x) s' with
  | none =>
    rw [hg] at h
    simp only [Sum.inl.injEq] at h
    subst h
    exact ⟨rfl, by simpa [wg1Enter] using Code.gatedExit_none.mp hg⟩
  | some i => rw [hg] at h; cases h

theorem stub_next (r : SubEntry)
    (d : (Code.withStubsAt (subFrag P L x) (SubEntry.pc P L x) (.inr r)).D) (n e)
    (σ' : (thread P L x).D) :
    (thread P L x).next (.inr ⟨.inl .wg1, .inr ⟨.inr r, d⟩⟩, n) e ≠ some (some σ') := by
  rw [next_frag]
  simp [frag, wg1Code, Code.roleLoop, Code.loopGlue, Code.withStubsAt,]

theorem stub_next0 (r : Entry) (d : (Code.withStubs (frag P L x) Entry.pc (.inr r)).D)
   (n e) (σ' : (thread P L x).D) :
   (thread P L x).next (.inr ⟨.inr r, d⟩, n) e ≠ some (some σ') := by
  simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs]

theorem backEnter_inl {i : SubEntry} {d : (subFrag P L x i).D} {s : Wg1.Site}
    (h : Code.backEnter (wg1HeadCode P L x) (Code.withStubsAt (subFrag P L x) (SubEntry.pc P L x))
      (Code.gatedExit (wg1Enter P L x) (subSel P L x))
      (fun | .inl i => subBack P L x i | .inr _ => fun _ => none) (.inl i) d = .inl s) :
    Wg1.exitOf s = none := by
  unfold Code.backEnter at h
  cases hb : subBack P L x i d with
  | none => simp [hb] at h
  | some p =>
    simp only [hb] at h
    have := (enter_inl h).2
    exact this

/-- No state of a thread is at an exit of the head. -/
theorem head_noExit {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) {s : Wg1.Site} {n : Cls → Nat}
    (hs : σ = (.inr ⟨.inl .wg1, .inl s⟩, n)) : Wg1.exitOf s = none := by
  induction k generalizing σ s n with
  | zero =>
    rw [Frame.stateAt_zero] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rw [thread_init] at hs
    cases hs
  | succ k ih =>
    by_cases hk : k < (X.tr x).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr x)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      obtain ⟨σm, hm, hn⟩ := prev_state he hσ
      subst hs
      rcases σm with ⟨d | ⟨e0 | r, d⟩, n0⟩
      · rw [next_startup] at hn
        rcases hsu : Startup.succ L x d e with _ | _ | d'
        · rw [hsu] at hn; cases hn
        · rw [hsu] at hn; cases hn
        · rw [hsu] at hn
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
          obtain ⟨hn, -⟩ := hn
          unfold Code.enter at hn
          cases hg : Code.gatedExit (startupEnter P L x) (sel P L x) d' with
          | none => rw [hg] at hn; cases hn
          | some i =>
            rw [hg] at hn
            rcases i with i | i
            · simp only [Sum.inr.injEq, Sigma.mk.injEq] at hn
              obtain ⟨h1, h2⟩ := hn
              cases h1
              have h3 : (Code.withStubs (frag P L x) Entry.pc (Sum.inl Entry.wg1)).init =
                  Sum.inl Wg1.Site.smr :=
                (Code.enter_none (Code.gatedExit_none.mpr rfl) :
                  Code.enter (wg1HeadCode P L x)
                    (Code.withStubsAt (subFrag P L x) (SubEntry.pc P L x))
                    (Code.gatedExit (wg1Enter P L x) (subSel P L x)) Wg1.Site.smr =
                  Sum.inl Wg1.Site.smr)
              rw [h3] at h2
              obtain rfl := Sum.inl.inj (eq_of_heq h2)
              rfl
            · cases hn
      · cases e0 with
        | wg0 =>
          rw [next_frag] at hn
          cases hq : (frag P L x .wg0).next d e with
          | none => rw [hq] at hn; cases hn
          | some o =>
            cases o with
            | none => rw [hq] at hn; cases hn
            | some d' => rw [hq] at hn; simp at hn
        | dequant =>
          rw [next_frag] at hn
          cases hq : (frag P L x .dequant).next d e with
          | none => rw [hq] at hn; cases hn
          | some o =>
            cases o with
            | none => rw [hq] at hn; cases hn
            | some d' => rw [hq] at hn; simp at hn
        | wg1 =>
          rcases d with s0 | ⟨i | r, d0⟩
          · rw [next_head] at hn
            rcases hs0 : Wg1.succ s0 e with _ | _ | s'
            · rw [hs0] at hn; cases hn
            · rw [hs0] at hn; cases hn
            · rw [hs0] at hn
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
              obtain ⟨hn, -⟩ := hn
              simp only [Sum.inr.injEq, Sigma.mk.injEq, true_and, heq_eq_eq] at hn
              exact (enter_inl hn).2
          · rw [next_sub] at hn
            cases hq : (subFrag P L x i).next d0 e with
            | none => rw [hq] at hn; cases hn
            | some o =>
              cases o with
              | none => rw [hq] at hn; cases hn
              | some d' =>
                rw [hq] at hn
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
                obtain ⟨hn, -⟩ := hn
                simp only [Sum.inr.injEq, Sigma.mk.injEq, true_and, heq_eq_eq]
                  at hn
                exact backEnter_inl hn
          · exact absurd hn (stub_next _ _ _ _ _)
      · exact absurd hn (stub_next0 _ _ _ _ _)
    · have hk' : (X.tr x).length ≤ k := by omega
      have : Frame.stateAt (thread P L) X x (k + 1) = Frame.stateAt (thread P L) X x k := by
        unfold Frame.stateAt
        rw [List.take_of_length_le hk', List.take_of_length_le (by omega)]
      rw [this] at hσ
      exact ih hσ hs

/-- **The head's shuffle returns the launch's warp word**, under `Follow`. -/
theorem head_recv_follow (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k pc : Nat} {a r : Value} {ok : Bool}
    (he : X.get (x, k) = some ⟨pc, .shfl .idx a 0 31 r ok⟩)
    (hc : Frame.cnt X Execution.isShfl x k = 2) (hwg : wgOf L x = 1) :
    r = w32 (warpW L x) := by
  have hF := follow_iff.mp hFw
  exact head_recv hp hX he hc hwg fun h j hw _ => hF h hw.1 j

/-- **The dispatch of the head** on the launch's warp word: the sub-role of the lane's warp. -/
theorem hsh_succ (hp : Pre P L m) (hw : 4 ≤ warpOf L x ∧ warpOf L x < 8) {e : Event} {s' : Wg1.Site}
    {a r : Value} {ok : Bool} (hk : e.kind = .shfl .idx a 0 31 r ok) (hr : r = w32 (warpW L x))
    (hs : Wg1.succ .hsh e = some (some s')) :
    (warpOf L x = 4 → s' = .mma) ∧ (warpOf L x = 5 → s' = .tma) ∧
      (warpOf L x = 6 → s' = .idle) ∧ (warpOf L x = 7 → s' = .index) := by
  subst hr
  have hlt : warpOf L x < 2 ^ 32 := by have := warpOf_lt (g := x) hp; omega
  have e7 : scmpi .eq .b (warpW L x) 7 = decide (warpOf L x = 7) :=
    scmpi_eq_b_W hlt (by decide) (by decide)
  have e5 : scmpi .eq .b (warpW L x) 5 = decide (warpOf L x = 5) :=
    scmpi_eq_b_W hlt (by decide) (by decide)
  have e4 : scmpi .ne .b (warpW L x) 4 = decide (warpOf L x ≠ 4) :=
    scmpi_ne_b_W hlt (by decide) (by decide)
  simp only [Wg1.succ, hk, Wg1.dispatch, e7, e5, e4, decide_eq_true_eq] at hs
  split_ifs at hs with h7 h5 h4' <;> simp only [Option.some.injEq] at hs <;> subst hs <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> first | rfl | omega

theorem gate_mma (h : warpOf L x = 4) :
    Code.gatedExit (wg1Enter P L x) (subSel P L x) Wg1.Site.mma = some (.inl .mma) := by
  simp [Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, subOk, h]

theorem gate_tma (h : warpOf L x = 5) :
    Code.gatedExit (wg1Enter P L x) (subSel P L x) Wg1.Site.tma = some (.inl .tma) := by
  simp [Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, subOk, h]

theorem gate_index (h : warpOf L x = 7) :
    Code.gatedExit (wg1Enter P L x) (subSel P L x) Wg1.Site.index = some (.inl .index) := by
  simp [Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, subOk, h]

theorem gate_idle (h : 4 ≤ warpOf L x ∧ warpOf L x < 7) :
    Code.gatedExit (wg1Enter P L x) (subSel P L x) Wg1.Site.idle = some (.inl .idle) := by
  simp [Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, subOk, h.1, h.2]

/-- **The head's `setmaxnreg` leads to its shuffle.** -/
theorem smr_next {n : Cls → Nat} {e : Event} {σ' : (thread P L x).D}
    (hn : (thread P L x).next (.inr ⟨.inl .wg1, .inl .smr⟩, n) e = some (some σ')) :
    σ' = (.inr ⟨.inl .wg1, .inl .hsh⟩, Code.bump cls n e) := by
  rw [next_head] at hn
  simp only [Wg1.succ, Option.map_some, Option.some.injEq] at hn
  rw [← hn]
  have hg : Code.gatedExit (wg1Enter P L x) (subSel P L x) Wg1.Site.hsh = none :=
    Code.gatedExit_none.mpr rfl
  simp only [Code.enter, hg]

/-- **The head's shuffle leads to the first state of the lane's warp's sub-role.** -/
theorem hsh_next (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} (hub : NoUbBefore X x (k + 1)) (hx : x < L.threads)
    (hw : 4 ≤ warpOf L x ∧ warpOf L x < 8) {n : Cls → Nat} {e : Event}
    {σ' : (thread P L x).D} (he : X.get (x, k) = some e)
    (hσ : Frame.stateAt (thread P L) X x k = some (some (.inr ⟨.inl .wg1, .inl .hsh⟩, n)))
    (hn : (thread P L x).next (.inr ⟨.inl .wg1, .inl .hsh⟩, n) e = some (some σ')) :
    (warpOf L x = 4 → σ' = (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, (subFrag P L x .mma).init⟩⟩,
      Code.bump cls n e)) ∧
    (warpOf L x = 5 → σ' = (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, (subFrag P L x .tma).init⟩⟩,
      Code.bump cls n e)) ∧
    (warpOf L x = 6 → σ' = (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, (subFrag P L x .idle).init⟩⟩,
      Code.bump cls n e)) ∧
    (warpOf L x = 7 → σ' = (.inr ⟨.inl .wg1, .inr ⟨.inl .index, (subFrag P L x .index).init⟩⟩,
      Code.bump cls n e)) := by
  have hne : ∀ f, e.kind ≠ .ub f := hub.ne (Nat.lt_succ_self k) he
  obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
  rw [hσ] at hσ0
  obtain rfl := Option.some.inj (Option.some.inj hσ0)
  have hJ := (follow_iff.mp hFw x hx k).2 _ hσ
  obtain ⟨-, hJ1, -, -⟩ := hJ
  change Wg1.HRef L x .hsh (n .shfl) at hJ1
  obtain ⟨hsh, hwg⟩ := hJ1
  have hev' : Wg1.Ev L x .hsh e := hev
  obtain ⟨r, ok, hk⟩ := hev'
  have hc : Frame.cnt X Execution.isShfl x k = 2 := by
    rw [← hsh]
    exact (state_count hσ .shfl).symm
  have hr : r = w32 (warpW L x) := by
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    exact head_recv_follow hp hX hFw he hc hwg
  rw [next_head] at hn
  rcases hsu : Wg1.succ .hsh e with _ | _ | s'
  · rw [hsu] at hn; cases hn
  · rw [hsu] at hn; cases hn
  · rw [hsu] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    obtain ⟨h4, h5, h6, h7⟩ := hsh_succ hp hw hk hr hsu
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain rfl := h4 h
      rw [← hn, Code.enter_some (gate_mma h)]
    · obtain rfl := h5 h
      rw [← hn, Code.enter_some (gate_tma h)]
    · obtain rfl := h6 h
      rw [← hn, Code.enter_some (gate_idle ⟨by omega, by omega⟩)]
    · obtain rfl := h7 h
      rw [← hn, Code.enter_some (gate_index h)]

/-- **A lane of warpgroup 1 at the head's shuffle has made its register request.** -/
theorem hsh_req (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X x (X.tr x).length =
      some (some (.inr ⟨.inl .wg1, .inl .hsh⟩, n))) :
    ∃ j pc inc n' i, X.get (x, j) = some ⟨pc, .setMaxReg inc n' i⟩ := by
  have hlr := low_or_req hp hX hFw hub hx (X.tr x).length le_rfl _ hσ
  have hm : measure P L x (.inr ⟨.inl .wg1, .inl .hsh⟩, n) = fragBase + 1 := rfl
  rw [hm, List.take_length] at hlr
  have hpos : 0 < (X.tr x).countP SetMaxNReg.isRequest := by
    rcases hlr with h | h
    · omega
    · exact h
  obtain ⟨a, ha, hra⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨pc, kd⟩ := a
  cases kd <;> simp [SetMaxNReg.isRequest] at hra
  rename_i inc n' i
  exact ⟨j, pc, inc, n', i, hj⟩

/-- **A state of a lane of warps 4 to 7** is a startup state before its hand-over, a state of the
head before its shuffle's dispatch (never at an exit), or a state of a sub-role its warp selects. -/
theorem wg1_cls (hFw : Follow P L X) (hx : x < L.threads)
    (hw : 4 ≤ warpOf L x ∧ warpOf L x < 8) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
    (∃ s n, σ = (.inr ⟨.inl .wg1, .inl s⟩, n) ∧ (s = .smr ∨ s = .hsh)) ∨
      ∃ i d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl i, d⟩⟩, n) ∧ subOk L x i = true := by
  have hJ := (follow_iff.mp hFw x hx k).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · obtain ⟨-, hW, -⟩ := hJ
    exact .inl ⟨d, n, rfl, hW, by simpa [startupEnter] using glue_gate hσ⟩
  · cases e with
    | wg0 | dequant =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warpOf, tidOf] at hw
      omega
    | wg1 =>
      obtain ⟨-, hJ1, -, -⟩ := hJ
      rcases d with s | ⟨i | r, d⟩
      · refine .inr (.inl ⟨s, n, rfl, ?_⟩)
        have hne := head_noExit hσ rfl
        cases s
        · exact .inl rfl
        · exact .inr rfl
        all_goals simp [Wg1.exitOf] at hne
      · refine .inr (.inr ⟨i, d, n, rfl, ?_⟩)
        cases i
        · exact hJ1.2.1
        · exact hJ1.2.1
        · exact hJ1.2.1
        · exact hJ1.2
      · exact hJ1.elim
  · exact hJ.elim

theorem ncW_head (hw : 4 ≤ warpOf L x ∧ warpOf L x < 8) :
    ncW (warpOf L x) 1842 = 2 ∧ ncW (warpOf L x) 1843 = 2 := by
  obtain ⟨h1, h2⟩ := hw
  generalize warpOf L x = w at h1 h2 ⊢
  interval_cases w <;> decide

theorem Code.backEnter_none {P : Code kernel Assumptions.all L x} {ι : Type}
    {R : ι → Code kernel Assumptions.all L x} {exit : P.D → Option ι}
    {back : (i : ι) → (R i).D → Option P.D} {i : ι} {d : (R i).D} (h : back i d = none) :
    Code.backEnter P R exit back i d = .inr ⟨i, d⟩ := by
  unfold Code.backEnter
  simp only [h]

theorem Code.backEnter_some {P : Code kernel Assumptions.all L x} {ι : Type}
    {R : ι → Code kernel Assumptions.all L x} {exit : P.D → Option ι}
    {back : (i : ι) → (R i).D → Option P.D} {i : ι} {d : (R i).D} {p : P.D}
    (h : back i d = some p) : Code.backEnter P R exit back i d = Code.enter P R exit p := by
  unfold Code.backEnter
  simp only [h]

theorem ncT_headS (hw : 4 ≤ warpOf L x ∧ warpOf L x < 8) {s : Wg1.Site} (hs : s = .smr ∨ s = .hsh)
    (n : Cls → Nat) : ncT P L x (.inr ⟨.inl .wg1, .inl s⟩, n) = 2 := by
  obtain ⟨h1, h2⟩ := ncW_head hw
  unfold ncT
  rcases hs with rfl | rfl
  · exact h1
  · exact h2

theorem pc_hsh (n : Cls → Nat) :
    (thread P L x).pc (.inr ⟨.inl .wg1, .inl .hsh⟩, n) = 1843 := rfl

theorem pc_smr (n : Cls → Nat) :
    (thread P L x).pc (.inr ⟨.inl .wg1, .inl .smr⟩, n) = 1842 := rfl

/-- The state of the idle code. -/
abbrev idleS (P : Params) (L : Launch) (x : Nat) (d : IdleSite) (n : Cls → Nat) :
    (thread P L x).D := (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, d⟩⟩, n)

/-- **A step of the idle code stays in it.** -/
theorem idleD_next {d : IdleSite} {n : Cls → Nat} {e : Event} {σ' : (thread P L x).D}
    (hn : (thread P L x).next (idleS P L x d n) e = some (some σ')) :
    ∃ d', σ' = idleS P L x d' (Code.bump cls n e) := by
  rw [next_sub] at hn
  rcases hq : (subFrag P L x .idle).next d e with _ | _ | d'
  · rw [hq] at hn; cases hn
  · rw [hq] at hn; cases hn
  · rw [hq] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    subst hn
    refine ⟨d', ?_⟩
    rw [Code.backEnter_none (by show subBack P L x .idle d' = none; rfl)]

/-- **After a blocking event of the idle code** the machine runs on, in the idle code (its only
blocking event is the barrier). -/
theorem idleD_last {d : IdleSite} {n : Cls → Nat} {e : Event} (hev : Wg1.IEv d e)
    (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next (idleS P L x d n) e ≠ none ∧ ∀ σ', (thread P L x).next (idleS P L x d n) e
      = some (some σ') → ∃ d', σ' = idleS P L x d' (Code.bump cls n e) := by
  cases d with
  | ldA => exfalso; rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> rw [hk] at hb <;>
      simp [Sched.Unblocking] at hb
  | ldB => exfalso; rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> rw [hk] at hb <;>
      simp [Sched.Unblocking] at hb
  | ret => exfalso; rw [hev] at hb; simp [Sched.Unblocking] at hb
  | bar =>
    have hs : (subFrag P L x .idle).next .bar e = some (some .ret) := rfl
    exact ⟨by rw [next_sub, hs]; simp, fun σ' hn => idleD_next hn⟩

/-- **After a blocking event of the idle code** the lane's pc is still in it. -/
theorem idleD_blocking (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) {k : Nat} {d : IdleSite} {n : Cls → Nat} {e : Event}
    (he : X.get (x, k) = some e)
    (hσ : Frame.stateAt (thread P L) X x k = some (some (idleS P L x d n)))
    (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next (idleS P L x d n) e ≠ none ∧ ∀ σ', (thread P L x).next (idleS P L x d n) e
      = some (some σ') → 2596 ≤ (thread P L x).pc σ' := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
  rw [hσ] at hσ0
  obtain rfl := Option.some.inj (Option.some.inj hσ0)
  obtain ⟨h1, h2⟩ := idleD_last (P := P) (L := L) (x := x) (n := n) (show Wg1.IEv d e from hev) hb
  refine ⟨h1, fun σ' hn => ?_⟩
  obtain ⟨d', rfl⟩ := h2 σ' hn
  exact idle_pc_ge d'

/-- **After a blocking event of the head** (its `setmaxnreg`; the shuffle does not block) the
lane is at the head's shuffle, at which every lane of its warp that is at a collective of the
same count has made its register request (`hreq`, the class's classification). -/
theorem head_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hw : 4 ≤ warpOf L x ∧ warpOf L x < 8) {k : Nat}
    {s : Wg1.Site} {n : Cls → Nat} {e : Event} (A : Nat → Prop) (he : X.get (x, k) = some e)
    (hs : s = .smr ∨ s = .hsh)
    (hσ : Frame.stateAt (thread P L) X x k = some (some (.inr ⟨.inl .wg1, .inl s⟩, n)))
    (hb : ¬ Sched.Unblocking e.kind)
    (hreq : ∀ y σy, A y → Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) →
      CollAt P L y σy → ncT P L y σy = 2 →
        ∃ j pc inc n i, X.get (y, j) = some ⟨pc, .setMaxReg inc n i⟩) :
    (thread P L x).next (.inr ⟨.inl .wg1, .inl s⟩, n) e ≠ none ∧
      ∀ σ', (thread P L x).next (.inr ⟨.inl .wg1, .inl s⟩, n) e = some (some σ') →
        ¬ CollAt P L x σ' ∨ ((∃ inc n i, e.kind = .setMaxReg inc n i) ∧
          ∀ y σy, A y → SameWarp L y x →
            Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
            ncT P L y σy = ncT P L x σ' → ∃ j pc inc n i,
              X.get (y, j) = some ⟨pc, .setMaxReg inc n i⟩) := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
  rw [hσ] at hσ0
  obtain rfl := Option.some.inj (Option.some.inj hσ0)
  rcases hs with rfl | rfl
  · have hev' : Wg1.Ev L x .smr e := hev
    obtain ⟨inst, hk⟩ := hev'
    refine ⟨by rw [next_head]; simp [Wg1.succ], fun σ' hn => .inr ⟨⟨_, _, _, hk⟩, ?_⟩⟩
    rw [smr_next hn]
    intro y σy hy _ hσy hcy hny
    rw [ncT_headS hw (.inr rfl)] at hny
    exact hreq y σy hy hσy hcy hny
  · have hev' : Wg1.Ev L x .hsh e := hev
    obtain ⟨r, ok, hk⟩ := hev'
    rw [hk] at hb
    simp [Sched.Unblocking] at hb

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
