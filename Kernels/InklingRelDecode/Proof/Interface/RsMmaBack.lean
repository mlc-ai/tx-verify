-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeMma
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv

@[expose] public section

/-!
# The MMA warp's earlier PV step (backward over the loop)

The thread-layer half of `Result.Mma.OAcc.base` and of `Out.Inputs.oSource`: if the MMA warp is
at a state of iteration `i`, or past the PV half of iteration `i0 < i`, then an earlier event
fired from step 7 of the PV half of iteration `i0`, with the same Tensor Memory base and the same
`num_iters`. The election of the MMA warp's lane is the premise `ElectLead` (every election of the
thread returned its lane): without it the lane would skip the MMA blocks of an iteration and go on
to the next.

* `Past i0 d`: the state is after step 7 of the PV half of iteration `i0`.
* `next_past`: one step of the machine either keeps `Past i0` backwards or is the step out of
  step 7 of iteration `i0`.
* `exists_pv7`: the backward induction along the thread's trace.
* `fin_iter`: a state of the loop's end (after the last iteration) is at iteration `num_iters + 1`
  when `1 ≤ num_iters ≤ 2147483646`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- The MMA warp's state is after step 7 of the PV half of iteration `i0`: in a later iteration,
or in the iteration at one of the two commits that follow the eight MMAs. -/
def Past (i0 : Nat) (d : Mma.D) : Prop :=
  i0 < d.i ∨ (d.i = i0 ∧ (d.site = .pvCommit1 ∨ d.site = .pvCommit2))

/-- **One step of the MMA machine, backwards.** If the successor state is past step 7 of
iteration `i0 ≥ 1`, the state is past it too or is step 7 of iteration `i0`; the Tensor Memory
base is kept, and so is `num_iters` except at the load of it. The election events return the
thread's lane. -/
theorem next_past {i0 : Nat} {d0 d : Mma.D} {e : Event}
    (hn : Mma.next L g d0 e = some (some d))
    (hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g) (h1 : 1 ≤ i0)
    (hk0 : d0.site.isSkip = false) (hp : Past i0 d) :
    (Past i0 d0 ∨ (d0.site = .pv 7 ∧ d0.i = i0)) ∧ d.tm = d0.tm ∧
      (d0.site ≠ .ldNum → d.n = d0.n) := by
  have hk0' : d0.site ≠ .pvSkip ∧ d0.site ≠ .qkSkip := by
    constructor <;> intro h <;> simp [h, Mma.Site.isSkip] at hk0
  unfold Past at hp ⊢
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (exfalso; exact hk0'.1 ‹_›)
    | (exfalso; exact hk0'.2 ‹_›)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       refine ⟨?_, rfl, fun _ => rfl⟩
       rcases hp with hp | ⟨hp1, hp2⟩
       · by_cases hlt : i0 < d0.i
         · exact .inl (.inl hlt)
         · have hq : d0.i = i0 := by simp only at hp; omega
           exact .inl (.inr ⟨hq, by simp_all⟩)
       · first
           | (rename_i _ j hj hh
              exact .inr ⟨by rw [hj]; congr 1; exact Fin.ext (by omega), hp1⟩)
           | (simp only at hp2; rcases hp2 with hp2 | hp2 <;> cases hp2))

/-- **The MMA machine's invariant at a state with an event.** -/
theorem mma_inv_at (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {d : Mma.D} {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) : Mma.Inv d := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  exact hinv.2.1

/-- **The state before an MMA state, with adjacency.** Like `mma_state_pred`, with the predecessor
at the previous index. -/
theorem mma_state_pred_le (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Mma.D}
    {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg) :
    ∃ (k0 : Nat) (e : Event) (d0 : Mma.D), k0 + 1 = k ∧ g < L.threads ∧ X.get (g, k0) = some e ∧
      St Q L X g k0 = some (some (.w (.mma d0 P))) ∧ Mma.next L g d0 e = some (some d) := by
  have hk1 : k ≠ 0 := by
    rintro rfl
    have h0 := hσ
    rw [St, Frame.stateAt_zero] at h0
    exact mma_ne_init d P (Option.some.inj (Option.some.inj h0)).symm
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hs' := hσ
  rw [St, Frame.stateAt_succ he] at hs'
  cases hk0 : St Q L X g k0 with
  | none => simp [St] at hk0 hs'; simp [hk0] at hs'
  | some σ =>
    cases σ with
    | none =>
      have : Frame.stateAt (code L Q) X g k0 = some none := hk0
      rw [this] at hs'
      simp [Code.toMachine] at hs'
    | some s0 =>
      have : Frame.stateAt (code L Q) X g k0 = some (some s0) := hk0
      rw [this] at hs'
      have hn : (threadCode L g Q).next s0 e = some (some (.w (.mma d P))) := hs'
      cases s0 with
      | d s =>
        rw [next_d] at hn
        obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
        cases h
      | w s =>
        rw [next_w] at hn
        obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
        cases h
        obtain ⟨d0, rfl, hd0⟩ := wcomp_next_mma ha hs
        have hge : X.get (g, k0) = some e := he
        exact ⟨k0, e, d0, rfl, Frame.lt_of_get hX hge, hge, hk0, hd0⟩

theorem mma_state_pred_adj (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Mma.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg) :
    ∃ (k0 : Nat) (e : Event) (d0 : Mma.D), k0 + 1 = k ∧ g < L.threads ∧ X.get (g, k0) = some e ∧
      St Q L X g k0 = some (some (.w (.mma d0 P))) ∧ Mma.next L g d0 e = some (some d) :=
  mma_state_pred_le hX hk.le hσ hs

/-- **A thread whose broadcasts receive 7 is never at a skip site** (`qkSkip`, `pvSkip`), at an
index up to the trace's length: each MMA state but the entry follows an MMA state by one step
(`mma_state_pred_le`), and a step on a broadcast that receives 7 does not reach a skip site
(`Mma.next_not_skip`). -/
theorem not_skip_le (hX : Consistent L kernel asms mem0 X) (hbc : Mma.BcastRun (X.tr g)) :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k ≤ (X.tr g).length →
      St Q L X g k = some (some (.w (.mma d P))) → d.site.isSkip = false := by
  intro k
  induction k with
  | zero =>
    intro d P hk hσ
    by_cases hs : d.site = .setMaxReg
    · rw [hs]; rfl
    obtain ⟨k0, e, d0, hadj, -, -, -, -⟩ := mma_state_pred_le hX hk hσ hs
    omega
  | succ k ih =>
    intro d P hk hσ
    by_cases hs : d.site = .setMaxReg
    · rw [hs]; rfl
    obtain ⟨k0, e, d0, hadj, -, he, hs0, hn⟩ := mma_state_pred_le hX hk hσ hs
    obtain rfl : k0 = k := by omega
    exact Mma.next_not_skip (hbc e (List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he)))
      (ih (by omega) hs0) hn

/-- **A thread whose broadcasts receive 7 is never at a skip site.** -/
theorem not_skip (hX : Consistent L kernel asms mem0 X) (hbc : Mma.BcastRun (X.tr g)) {k : Nat}
    {d : Mma.D} {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    d.site.isSkip = false := by
  by_cases hk : k ≤ (X.tr g).length
  · exact not_skip_le hX hbc k hk hσ
  · have hσ' : St Q L X g (X.tr g).length = some (some (.w (.mma d P))) := by
      have he := Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by omega)
      rw [St] at hσ ⊢
      rw [← he]
      exact hσ
    exact not_skip_le hX hbc _ le_rfl hσ'

/-- **A thread at an MMA state is a thread of warp 7**, so its broadcasts receive 7 when every
broadcast of warp 7 does. -/
theorem bcast_of_mma (hW : RoleWarps Q L X) (hB : Mma.MmaBcast L X) {k : Nat} {d : Mma.D}
    {P : Loader.Pro} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) : Mma.BcastRun (X.tr g) :=
  hB g hg (by simpa [RoleWarp, Ledger.roleWarp] using roleWarp_inv hW k _ hk hσ)

/-- **An earlier PV step 7.** An MMA-warp state of thread `g` at an event, past step 7 of the PV
half of iteration `i0 ≥ 1`, has an earlier state at step 7 of that iteration, with the same
Tensor Memory base and `num_iters` and an MMA event; every state between it and the state is an
MMA-warp state past step 7 of the iteration with the same `num_iters`. -/
theorem exists_pv7 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hlead : ElectLead L g (X.tr g))
    (hbc : Mma.BcastRun (X.tr g)) {i0 : Nat} (h1 : 1 ≤ i0) :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.mma d P))) → Past i0 d →
      ∃ (k' : Nat) (d' : Mma.D), k' < k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
        d'.site = .pv 7 ∧ d'.i = i0 ∧ d'.tm = d.tm ∧ d'.n = d.n ∧
        (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
        ∀ j, k' < j → j ≤ k → ∃ dj, St Q L X g j = some (some (.w (.mma dj P))) ∧
          Past i0 dj ∧ dj.n = d.n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hp
    have hI := mma_inv_at hX hf hk hσ
    have hsite : d.site ≠ .setMaxReg := by
      intro hs
      have := hI.pre (by rw [hs]; trivial)
      unfold Past at hp
      rw [hs] at hp
      rcases hp with hp | ⟨hp, hp'⟩
      · omega
      · rcases hp' with hp' | hp' <;> cases hp'
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX hk hσ hsite
    have hlt : k0 < k := by omega
    have hmem : e ∈ X.tr g := List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he)
    have hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g :=
      fun mask inst ld h => hlead e hmem mask inst ld h
    obtain ⟨hp0, htm, hnn⟩ := next_past hn hl h1 (not_skip hX hbc hs0) hp
    have hI0 := mma_inv_at hX hf (by omega) hs0
    have hld : d0.site ≠ .ldNum := by
      intro hs
      have := hI0.pre (by rw [hs]; trivial)
      rcases hp0 with hp0 | ⟨hp0, -⟩
      · unfold Past at hp0
        rw [hs] at hp0
        rcases hp0 with hp0 | ⟨hp0, hp'⟩
        · omega
        · rcases hp' with hp' | hp' <;> cases hp'
      · rw [hs] at hp0
        cases hp0
    have hn0 := hnn hld
    rcases hp0 with hp0 | ⟨hs7, hi7⟩
    · obtain ⟨k', d', hk', hs', hd1, hd2, hd3, hd4, hev, hch⟩ := ih k0 hlt (by omega) hs0 hp0
      refine ⟨k', d', by omega, hs', hd1, hd2, hd3.trans htm.symm, hd4.trans hn0.symm, hev, ?_⟩
      intro j hj1 hj2
      by_cases hjk : j = k
      · exact ⟨d, by rw [hjk]; exact hσ, hp, rfl⟩
      · obtain ⟨dj, h1, h2, h3⟩ := hch j hj1 (by omega)
        exact ⟨dj, h1, h2, h3.trans hn0.symm⟩
    · refine ⟨k0, d0, hlt, hs0, hs7, hi7, htm.symm, hn0.symm, ?_, ?_⟩
      · obtain ⟨pc, dst, sp, acc, mask, h⟩ := mma_issue_event hpre hX hf hg0 he hs0
          (.inr ⟨7, hs7⟩)
        exact ⟨pc, dst, sp, acc, mask, by rw [he, h]⟩
      · intro j hj1 hj2
        have : j = k := by omega
        exact ⟨d, by rw [this]; exact hσ, hp, rfl⟩

/-- **In a complete execution the thread's state before an event is not the last state.** A state
of a launched thread at an index past its last event does not exist: the last event is the exit
(`exit_of_complete`), whose successor is none. -/
theorem lt_length_of_complete (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hc : Complete L X) (hg : g < L.threads) {k : Nat} {s : TSt}
    (h : St Q L X g k = some (some s)) : k < (X.tr g).length := by
  by_contra hk
  have h2 : St Q L X g (X.tr g).length = some (some s) :=
    (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by omega)).symm.trans h
  rcases hc.1 g hg with hcan | ⟨pc, hl⟩
  · exact no_canceled hX g hg hcan
  · have hlen : 0 < (X.tr g).length := by
      by_contra h0
      have : (X.tr g) = [] := List.length_eq_zero_iff.mp (by omega)
      rw [this] at hl
      simp at hl
    have he : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .exit⟩ := by
      rw [← List.getLast?_eq_getElem?, hl]
    have hge : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := he
    have hlen' : (X.tr g).length = ((X.tr g).length - 1) + 1 := by omega
    rw [hlen', St, Frame.stateAt_succ he] at h2
    rcases exit_event_state hX hf.sound hf.tracked hge with ⟨d, hσ, hd⟩ | ⟨x, hσ, hx⟩
    · have hσ' : Frame.stateAt (code L Q) X g ((X.tr g).length - 1) = some (some (.d (.epi d))) :=
        hσ
      rw [hσ'] at h2
      simp only [Option.bind_some] at h2
      have := next_epiExit_none (L := L) (Q := Q) (g := g) d hd ⟨pc, .exit⟩
      simp only [Code.toMachine] at h2
      exact absurd (this.symm.trans h2) (by simp)
    · have hσ' : Frame.stateAt (code L Q) X g ((X.tr g).length - 1) = some (some (.w (.exit x))) :=
        hσ
      rw [hσ'] at h2
      simp only [Option.bind_some] at h2
      obtain ⟨xs, P⟩ := x
      have hx' : xs = .ret := hx
      subst hx'
      have := next_ret_none (L := L) (Q := Q) (g := g) P ⟨pc, .exit⟩
      simp only [Code.toMachine] at h2
      exact absurd (this.symm.trans h2) (by simp)

/-- **An MMA-warp state of a complete execution is before an event of a launched thread.** -/
theorem mma_state_lt (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hc : Complete L X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (h : St Q L X g k = some (some (.w (.mma d P)))) :
    g < L.threads ∧ k < (X.tr g).length := by
  by_cases hg : g < L.threads
  · exact ⟨hg, lt_length_of_complete hX hf hc hg h⟩
  · exfalso
    have hnil : X.tr g = [] := by
      by_contra hne
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[0]? = some e :=
        ⟨_, List.getElem?_eq_getElem (List.length_pos_of_ne_nil hne)⟩
      exact hg (Frame.lt_of_get hX (show X.get (g, 0) = some e from he))
    have h2 : St Q L X g k = St Q L X g 0 := by
      show Frame.stateAt (code L Q) X g k = Frame.stateAt (code L Q) X g 0
      rw [Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by simp [hnil])]
      simp [hnil]
    rw [h2, St, Frame.stateAt_zero] at h
    exact mma_ne_init d P (Option.some.inj (Option.some.inj h)).symm

/-! ### The loop's end, backwards -/

/-- The sites after the loop: the end-of-loop barrier, the election, the `o_final` commit and the
return to the dispatch. -/
def FinSite (s : Mma.Site) : Prop :=
  s = .finBar ∨ s = .finElect ∨ s = .finCommit ∨ s = .bar1 ∨ s = .setMaxRegInc

/-- **One step of the machine, backwards, at the loop's end.** A successor state at the loop's
end, with `1 ≤ num_iters ≤ 2147483646`, comes from a state at the loop's end in the same iteration,
or from the second commit of the last iteration. -/
theorem next_fin {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (hd : FinSite d.site) (h1 : 1 ≤ d.n) (h2 : d.n ≤ 2147483646) :
    d0.site ≠ .ldNum ∧ d.n = d0.n ∧
      ((FinSite d0.site ∧ d0.i = d.i) ∨
        ((d0.site = .pvCommit2 ∨ d0.site = .pvSkip) ∧ d0.i = d0.n ∧ d.i = d0.n + 1)) := by
  unfold FinSite at hd ⊢
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp only at h1 h2; exfalso; omega)

/-- **The loop's end is at iteration `num_iters + 1`.** An MMA-warp state at the end of the loop
(the barrier, the election, the `o_final` commit or after it), with `1 ≤ n ≤ 2147483646`, is at
iteration `n + 1`. -/
theorem fin_iter (hX : Consistent L kernel asms mem0 X)
    (hlead : ElectLead L g (X.tr g)) :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.mma d P))) → FinSite d.site → 1 ≤ d.n →
      d.n ≤ 2147483646 → d.i = d.n + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hfs h1 h2
    have hsite : d.site ≠ .setMaxReg := by
      intro hs
      unfold FinSite at hfs
      rw [hs] at hfs
      rcases hfs with h | h | h | h | h <;> cases h
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX hk hσ hsite
    have hmem : e ∈ X.tr g := List.mem_of_getElem? (show (X.tr g)[k0]? = some e from he)
    have hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g :=
      fun mask inst ld h => hlead e hmem mask inst ld h
    obtain ⟨hld, hnn, hc⟩ := next_fin hn hl hfs h1 h2
    rcases hc with ⟨hf0, hi0⟩ | ⟨hs2, hi2, hi3⟩
    · have := ih k0 (by omega) (by omega) hs0 hf0 (by omega) (by omega)
      omega
    · omega

/-! ### Before the first PV step of an iteration, backwards -/

/-- The state is before the first PV step of iteration `i`: in an earlier iteration, or in the
iteration at a site before the PV half's MMAs. -/
def Bef (i : Nat) (d : Mma.D) : Prop :=
  d.i < i ∨ (d.i = i ∧ d.site ≠ .pvCommit1 ∧ d.site ≠ .pvCommit2 ∧ (∀ y, d.site ≠ .pv y) ∧
    ¬ FinSite d.site)

/-- **One step of the machine, backwards, before the first PV step.** A state before the first PV
step of iteration `i`, or that step, has a predecessor before it. -/
theorem next_bef {i : Nat} {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hb : Bef i d ∨ (d.site = .pv 0 ∧ d.i = i)) : Bef i d0 := by
  unfold Bef FinSite at hb ⊢
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; omega)

/-- **The states between the last PV step of iteration `b` and PV step 0 of iteration `b + 1`**
are before the first PV step of iteration `b + 1`: they issue no PV MMA. -/
theorem between_bef (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {b k k' : Nat} {d : Mma.D} {P : Loader.Pro} (hb : 1 ≤ b) (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv 0) (hi : d.i = b + 1)
    (hch : ∀ j, k' < j → j ≤ k → ∃ dj, St Q L X g j = some (some (.w (.mma dj P))) ∧
      Past b dj) :
    ∀ m j, j + m + 1 = k → k' < j → ∃ dj, St Q L X g j = some (some (.w (.mma dj P))) ∧
      Bef (b + 1) dj := by
  intro m
  induction m with
  | zero =>
    intro j hj hjk
    have hsite : d.site ≠ .setMaxReg := by rw [hs]; nofun
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX hk hσ hsite
    have hj0 : k0 = j := by omega
    subst hj0
    exact ⟨d0, hs0, next_bef (i := b + 1) hn (Or.inr ⟨hs, hi⟩)⟩
  | succ m ih =>
    intro j hj hjk
    obtain ⟨dj1, hσ1, hb1⟩ := ih (j + 1) (by omega) (by omega)
    obtain ⟨dq, hσq, hpq⟩ := hch (j + 1) (by omega) (by omega)
    have hdd : dq = dj1 := by
      have := Option.some.inj (Option.some.inj (hσq.symm.trans hσ1))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    have hI := mma_inv_at hX hf (by omega) hσ1
    have hsite : dq.site ≠ .setMaxReg := by
      intro h0
      have := hI.pre (by rw [h0]; trivial)
      unfold Past at hpq
      rw [h0] at hpq
      rcases hpq with hp | ⟨-, hp⟩
      · omega
      · rcases hp with hp | hp <;> cases hp
    obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX (by omega) hσ1 hsite
    have hj0 : k0 = j := by omega
    subst hj0
    exact ⟨d0, hs0, next_bef (i := b + 1) hn (Or.inl hb1)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
