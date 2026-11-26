-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowFeed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Recv

@[expose] public section

/-! # A lane of warp 4 or 5 before its election

For the pre-election exports (`Common/Export/PreElect.lean`, which imports this file privately).
The lane of warp 4 (5) whose sub-role is the MMA (TMA) code, `r` with `ElWarp r`, is past its
election (`PostE r`: its role's code past the election site, or the idle code) only after an event
at the election's pc `elPc r` (`pre_hist`). Its states are classified by `pre_cls`: a startup
state before the hand-over, a head state of warpgroup 1, a state past the election, or its role's
first state at the election site (time `idleBase` for the MMA code, `idleBase + 29` for the TMA
code), whose event is the election.

Going forward along the thread machine (`pre_step`): a startup step enters a startup state, a
head or another warpgroup; a head step enters the head's shuffle, or at the shuffle the sub-role
the dispatch selects on the received word, which is the launch's warp word (`head_recv`): the
role `r` at its first state, at the election site. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The warp of an electing sub-role's lanes. -/
def ElWarp (L : Launch) (g : Nat) : SubEntry → Prop
  | .mma => warpOf L g = 4
  | .tma => warpOf L g = 5
  | _ => False

/-- The pc of an electing sub-role's election. -/
def elPc : SubEntry → Nat
  | .mma => 1853
  | .tma => 2165
  | _ => 0

/-- The glued time of an electing sub-role's first state. -/
def elTime : SubEntry → Nat
  | .mma => idleBase
  | .tma => idleBase + 29
  | _ => 0

/-- A sub-role's state at its election site. -/
def AtEl : (i : SubEntry) → (subFrag P L g i).D → Prop
  | .mma, d => d.site = .elect
  | .tma, d => d.site = .elect
  | _, _ => True

/-- **The states after the election** of sub-role `r`: its code past the election site, or the
idle code. -/
def PostE (r : SubEntry) : (thread P L g).D → Prop
  | (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, _⟩⟩, _) => True
  | (.inr ⟨.inl .wg1, .inr ⟨.inl i, d⟩⟩, _) => i = r ∧ ¬ AtEl i d
  | _ => False

/-- **The dispatch on the launch's warp word** of warp 4 (5) selects the MMA (TMA) exit. -/
theorem el_disp (hp : Pre P L m) {r : SubEntry} (hw : ElWarp L g r) {pc : Nat} {a : Value}
    {ok : Bool} {s' : Wg1.Site}
    (hs : Wg1.succ .hsh ⟨pc, .shfl .idx a 0 31 (w32 (warpW L g)) ok⟩ = some (some s')) :
    wg1Enter P L g s' = some r := by
  have hlt : warpOf L g < 2 ^ 32 := by have := warpOf_lt (g := g) hp; omega
  have e7 : scmpi .eq .b (warpW L g) 7 = decide (warpOf L g = 7) :=
    scmpi_eq_b_W hlt (by decide) (by decide)
  have e5 : scmpi .eq .b (warpW L g) 5 = decide (warpOf L g = 5) :=
    scmpi_eq_b_W hlt (by decide) (by decide)
  have e4 : scmpi .ne .b (warpW L g) 4 = decide (warpOf L g ≠ 4) :=
    scmpi_ne_b_W hlt (by decide) (by decide)
  simp only [Wg1.succ, Wg1.dispatch, e7, e5, e4] at hs
  cases r <;> simp only [ElWarp] at hw <;> simp [hw] at hs <;> subst hs <;>
    simp [wg1Enter, Wg1.exitOf]

/-- **No startup step enters a state after the election.** -/
theorem start_post {r : SubEntry} {d : Startup.D} {n : Cls → Nat} {f : Event}
    {σ' : (thread P L g).D} (hn : (thread P L g).next (.inl d, n) f = some (some σ')) :
    ¬ PostE r σ' := by
  rw [next_startup] at hn
  rcases h : Startup.succ L g d f with _ | _ | d'
  · rw [h] at hn; cases hn
  · rw [h] at hn; cases hn
  rw [h] at hn
  simp only [Option.map_some, Option.some.injEq] at hn
  subst hn
  unfold Code.enter
  split
  · next i _ =>
    rcases i with i | i
    · cases i <;> simp [PostE, Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, wg1HeadCode,
        Wg1.code]
    · simp [PostE]
  · simp [PostE]

/-- **No head step of the electing warp enters a state after the election**: the dispatch
enters the role at its election site. -/
theorem head_post (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {r : SubEntry} (hw : ElWarp L g r) {k : Nat} {s : Wg1.Site}
    {n : Cls → Nat} {f : Event}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg1, .inl s⟩, n)))
    (he : X.get (g, k) = some f) (hu : ∀ fl, f.kind ≠ .ub fl)
    {σ' : (thread P L g).D}
    (hn : (thread P L g).next (.inr ⟨.inl .wg1, .inl s⟩, n) f = some (some σ')) :
    ¬ PostE r σ' := by
  have hg := Frame.lt_of_get hX he
  have hJ := (follow_iff.mp hFw g hg k).2 _ hσ
  rw [next_head] at hn
  rcases hs : Wg1.succ s f with _ | _ | s'
  · rw [hs] at hn; cases hn
  · rw [hs] at hn; cases hn
  rw [hs] at hn
  simp only [Option.map_some, Option.some.injEq] at hn
  subst hn
  have hev : Wg1.Ev L g s f := ev_of_state hp hX he hσ hJ hu
  cases s with
  | smr =>
    simp only [Wg1.succ, Option.some.injEq] at hs
    subst hs
    rw [Code.enter_none (by simp [Code.gatedExit, wg1Enter, Wg1.exitOf])]
    simp [PostE]
  | hsh =>
    obtain ⟨-, hR, -, hwg⟩ := hJ
    change Wg1.HRef L g .hsh (n .shfl) at hR
    obtain ⟨hsh, -⟩ := hR
    obtain ⟨rv, ok, hk⟩ := hev
    obtain ⟨pc, kd⟩ := f
    simp only at hk
    subst hk
    have hc : Frame.cnt X Execution.isShfl g k = 2 := by
      rw [← hsh]
      exact (state_count hσ .shfl).symm
    have hF := follow_iff.mp hFw
    have hrv := head_recv hp hX he hc hwg fun h j hw _ => hF h hw.1 j
    subst hrv
    have hx := el_disp hp hw hs
    have hsel : subSel P L g r s' = some r := by
      cases r <;> simp only [ElWarp] at hw <;> simp [subSel, subOk, hw]
    rw [Code.enter_some (i := .inl r) (by simp [Code.gatedExit, hx, hsel])]
    cases r <;> simp only [ElWarp] at hw <;>
      simp [PostE, AtEl, Mma.init, Tma.init]
  | _ => simp [Wg1.succ] at hs

/-- A lane of warpgroup 0 or 2 is no lane of an electing warp. -/
private theorem wg_ne {r : SubEntry} (hw : ElWarp L g r) {w : Nat} (hwg : wgOf L g = w)
    (h1 : w ≠ 1) : False := by
  simp only [wgOf] at hwg
  cases r <;> simp only [ElWarp, warpOf] at hw <;> omega

/-- **The states of a lane of an electing warp**: a startup state before its hand-over, a head
state, a state after the election, or the role's first state at the election site, at time
`elTime r`, whose event (no undefined behaviour) is at the election's pc. -/
theorem pre_cls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) {r : SubEntry} (hw : ElWarp L g r) {i : Nat}
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ startupEnter P L g d = none) ∨
      (∃ s n, σ = (.inr ⟨.inl .wg1, .inl s⟩, n)) ∨ PostE r σ ∨
      (time P L g σ = elTime r ∧ ∀ f, (X.tr g)[i]? = some f → (∀ fl, f.kind ≠ .ub fl) →
        f.pc = elPc r) := by
  have hJ := (follow_iff.mp hFw g hg i).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | e, d⟩
  · exact .inl ⟨d, n, rfl, glue_gate hσ⟩
  · cases e with
    | wg0 => obtain ⟨-, -, -, h⟩ := hJ; exact (wg_ne hw h (by decide)).elim
    | dequant => obtain ⟨-, -, -, h⟩ := hJ; exact (wg_ne hw h (by decide)).elim
    | wg1 =>
      rcases d with s | ⟨j | j, d⟩
      · exact .inr (.inl ⟨s, n, rfl⟩)
      · obtain ⟨-, hW, -, -⟩ := hJ
        have hev : ∀ f, (X.tr g)[i]? = some f → (∀ fl, f.kind ≠ .ub fl) →
            (table P L).Ev g (.inr ⟨.inl .wg1, .inr ⟨.inl j, d⟩⟩, n) f := fun f hf hu =>
          ev_of_state hp hX hf hσ ((follow_iff.mp hFw g hg i).2 _ hσ) hu
        cases j with
        | idle => exact .inr (.inr (.inl trivial))
        | index =>
          obtain ⟨-, hsub, -⟩ := hW
          simp only [subOk, beq_iff_eq] at hsub
          cases r <;> simp only [ElWarp] at hw <;> omega
        | mma =>
          obtain ⟨-, hsub, -⟩ := hW
          simp only [subOk, beq_iff_eq] at hsub
          cases r <;> simp only [ElWarp] at hw <;> try omega
          by_cases hA : d.site = .elect
          · refine .inr (.inr (.inr ⟨?_, fun f hf hu => ?_⟩))
            · simp [time, fragTime, wg1Time, mmaTime, Mma.time, Mma.place, hA, Mma.Site.inLoop,
                Mma.Site.ord, elTime]
            · have h1 := (hev f hf hu).1
              simp only [hA, Mma.Site.pc] at h1
              exact h1
          · exact .inr (.inr (.inl ⟨rfl, hA⟩))
        | tma =>
          obtain ⟨-, hsub, -⟩ := hW
          simp only [subOk, beq_iff_eq] at hsub
          cases r <;> simp only [ElWarp] at hw <;> try omega
          by_cases hA : d.site = .elect
          · refine .inr (.inr (.inr ⟨?_, fun f hf hu => ?_⟩))
            · simp [time, fragTime, wg1Time, tmaTime, Tma.time, Tma.place, hA, Tma.Site.inLoop,
                Tma.Site.ord, elTime]
            · have h1 := (hev f hf hu).1
              simp only [hA, Tma.Site.pc] at h1
              exact h1
          · exact .inr (.inr (.inl ⟨rfl, hA⟩))
      · exact hJ.2.1.elim
  · exact hJ.elim

/-- **A step into a state after the election** is from one, or is the election. -/
theorem pre_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) {r : SubEntry}
    (hw : ElWarp L g r) {i : Nat} {σ σ' : (thread P L g).D} {f : Event}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) (hf : (X.tr g)[i]? = some f)
    (hn : (thread P L g).next σ f = some (some σ')) (hP : PostE r σ') :
    PostE r σ ∨ f.pc = elPc r := by
  have he : X.get (g, i) = some f := hf
  have hu : ∀ fl, f.kind ≠ .ub fl := fun fl h => hnu ⟨(g, i), f.pc, fl, by rw [he, ← h]⟩
  rcases pre_cls hp hX hFw hg hw hσ with ⟨d, n, rfl, -⟩ | ⟨s, n, rfl⟩ | h | ⟨-, h⟩
  · exact absurd hP (start_post hn)
  · exact absurd hP (head_post hp hX hFw hw hσ he hu hn)
  · exact .inl h
  · exact .inr (h f hf hu)

/-- **A state after the election follows an event at the election's pc.** -/
theorem pre_hist (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) {r : SubEntry}
    (hw : ElWarp L g r) :
    ∀ i (σ : (thread P L g).D), Frame.stateAt (thread P L) X g i = some (some σ) →
      PostE r σ → ∃ j < i, ∃ e, X.get (g, j) = some e ∧ e.pc = elPc r := by
  intro i
  induction i with
  | zero =>
    intro σ hσ hP
    rw [Frame.stateAt_zero, thread_init] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    simp [PostE] at hP
  | succ k ih =>
    intro σ hσ hP
    rcases hk : (X.tr g)[k]? with _ | e
    · have hlen : (X.tr g).length ≤ k := List.getElem?_eq_none_iff.mp hk
      have h' : Frame.stateAt (thread P L) X g (k + 1) = Frame.stateAt (thread P L) X g k := by
        unfold Frame.stateAt
        rw [List.take_of_length_le hlen, List.take_of_length_le (by omega)]
      obtain ⟨j, hj, hw'⟩ := ih σ (h' ▸ hσ) hP
      exact ⟨j, by omega, hw'⟩
    · rw [Frame.stateAt_succ hk] at hσ
      obtain ⟨τ, hτ, hn⟩ := Option.bind_eq_some_iff.mp hσ
      rcases τ with _ | σ0
      · cases hn
      rcases pre_step hp hX hFw hnu hg hw hτ hk hn hP with h | h
      · obtain ⟨j, hj, hw'⟩ := ih σ0 hτ h
        exact ⟨j, by omega, hw'⟩
      · exact ⟨k, by omega, e, hk, h⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
