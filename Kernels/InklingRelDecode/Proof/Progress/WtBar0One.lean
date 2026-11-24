-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Progress.WfBarAll

@[expose] public section

/-!
# `Bar0Facts.one`: a thread has at most one last-generation arrival

A last-generation arrival (`FinalArr X 0 2`) is a `bar.sync 0` without a count that follows at least
two barrier-0 events of its thread. The instruction of its state is `bar.sync 0`, which is not at
the common start (those states have fewer than two earlier barrier-0 events, `ordinal_inv`), so it
is the default partition's last `bar.sync 0` (the epilogue's `bar3`) or the exit role's (`.exit`
at `bar`): a state of `FinalSite`. Both lead to states of `PostSite` (the epilogue's `dealloc` and
`exit`, the exit role's `ret`), which lead to `PostSite` states or stop, and no `PostSite` state is
a `FinalSite`. So a thread's second last-generation arrival would be fired from a `PostSite` state.

`ordinal_inv` has a lower bound only; the upper bound this needs is the straight-line shape of the
end of each machine, not a count.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The states whose instruction is the last `bar.sync 0` of a machine: the epilogue's `bar3`, the
exit role's `bar` (and the dispatch's entry of the exit role, which no machine state reaches). -/
def FinalSite : TSt → Prop
  | .d (.epi d) => d.site = .bar3
  | .w (.exit x) => x.site = .bar
  | .w (.worker w) => w.site = .toExit
  | _ => False

/-- The states after the last `bar.sync 0`. -/
def PostSite : TSt → Prop
  | .d (.epi d) => d.site = .dealloc ∨ d.site = .exit
  | .w (.exit x) => x.site = .ret
  | _ => False

theorem not_final_of_post {s : TSt} (hp : PostSite s) : ¬ FinalSite s := by
  cases s with
  | d s =>
    cases s <;> simp only [PostSite, FinalSite] at hp ⊢
    rcases hp with h | h <;> simp [h]
  | w s =>
    cases s <;> simp only [PostSite, FinalSite] at hp ⊢
    simp [hp]

/-- **An event on `bar.sync 0` without a count after two barrier-0 events is fired at a final
site.** -/
theorem final_site (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k pc : Nat} {m : BarMode} (he : X.get (g, k) = some ⟨pc, .bar 0 none m⟩)
    (hk : 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) :
    ∃ s, St Q L X g k = some (some s) ∧ FinalSite s := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (fun pc' f h => by cases h)
  have hkl : k ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  obtain ⟨hlb, hex⟩ := ordinal_inv hX hS k s hkl hσ
  have hl2 : ¬ tLb s < 2 := fun hl => by have := hex hl; omega
  refine ⟨s, hσ, ?_⟩
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) ⟨pc, .bar 0 none m⟩ o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  rcases bar_kind_op hb hmem hf' (show (⟨pc, .bar 0 none m⟩ : Event).kind = .bar 0 none m from rfl)
    with ⟨al, hop⟩ | ⟨-, al, hop⟩
  · have hb0 : b0At (TSt.pc s) = 1 := by simp [b0At, hc', hop]
    cases s with
    | d s0 =>
      cases s0 with
      | dstart d =>
        have h1 := dstart_b0 d.site
        have h2 : b0At d.site.pc = 1 := hb0
        rw [h2] at h1
        obtain ⟨st, tm⟩ := d
        exfalso
        cases st <;> simp at h1 <;> exact hl2 (by simp [tLb, BarOrd.dLb])
      | pro d => exact absurd (hb0 : b0At d.site.pc = 1) (pro_b0 d.site)
      | sm d => exact absurd (hb0 : b0At d.site.pc = 1) (sm_b0 d.site)
      | epi d =>
        have h1 := epi_b0 d.site
        have h2 : b0At d.site.pc = 1 := hb0
        rw [h2] at h1
        obtain ⟨st, pr, o', sk⟩ := d
        cases st <;> first | (simp at h1; done) | simp [FinalSite]
    | w s0 =>
      cases s0 with
      | worker w =>
        have h1 := worker_b0 w.site
        have h2 : b0At w.site.pc = 1 := hb0
        rw [h2] at h1
        obtain ⟨st, P⟩ := w
        cases st <;> simp at h1 <;>
          first | (simp [FinalSite]; done) | exact absurd (by simp [tLb, BarOrd.wLb]) hl2
      | idle d =>
        have h1 := idle_b0 d.site
        have h2 : b0At d.site.pc = 1 := hb0
        omega
      | loader d P =>
        have h1 := loader_b0 d.site
        have h2 : b0At d.site.pc = 1 := hb0
        omega
      | mma d P =>
        have h1 := mma_b0 d.site
        have h2 : b0At d.site.pc = 1 := hb0
        omega
      | exit x =>
        have h1 := exit_b0 x.site
        have h2 : b0At x.site.pc = 1 := hb0
        rw [h2] at h1
        obtain ⟨st, P⟩ := x
        cases st <;> first | (simp at h1; done) | simp [FinalSite]
  · rw [hop] at hf'
    have := EvD.fires_barSyncN_128 hb hf'
    simp only [Event.mk.injEq, Kind.bar.injEq] at this
    obtain ⟨-, -, hcnt, -⟩ := this
    cases hcnt

/-- A final site's successor is a post site, or the machine stops following. -/
theorem final_next {g : Nat} {s : TSt} (hs : FinalSite s) (e : Event) :
    (threadCode L g Q).next s e = some none ∨
      ∃ s', (threadCode L g Q).next s e = some (some s') ∧ PostSite s' := by
  cases s with
  | d s0 =>
    cases s0 with
    | epi d =>
      obtain ⟨st, pr, o, sk⟩ := d
      simp only [FinalSite] at hs
      subst hs
      refine .inr ⟨_, rfl, ?_⟩
      show PostSite (.d (.epi ⟨if pr.p3 then .dealloc else .exit, pr, o, sk⟩))
      split <;> simp [PostSite]
    | _ => exact absurd hs (by simp [FinalSite])
  | w s0 =>
    cases s0 with
    | worker w =>
      obtain ⟨st, P⟩ := w
      simp only [FinalSite] at hs
      subst hs
      exact .inl rfl
    | exit x =>
      obtain ⟨st, P⟩ := x
      simp only [FinalSite] at hs
      subst hs
      exact .inr ⟨_, rfl, rfl⟩
    | _ => exact absurd hs (by simp [FinalSite])

/-- A post site's successor is a post site, or the machine stops. -/
theorem post_next {g : Nat} {s : TSt} (hs : PostSite s) (e : Event) :
    (threadCode L g Q).next s e = none ∨
      ∃ s', (threadCode L g Q).next s e = some (some s') ∧ PostSite s' := by
  cases s with
  | d s0 =>
    cases s0 with
    | epi d =>
      obtain ⟨st, pr, o, sk⟩ := d
      simp only [PostSite] at hs
      rcases hs with rfl | rfl
      · exact .inr ⟨_, rfl, by simp [PostSite]⟩
      · exact .inl rfl
    | _ => exact absurd hs (by simp [PostSite])
  | w s0 =>
    cases s0 with
    | exit x =>
      obtain ⟨st, P⟩ := x
      simp only [PostSite] at hs
      subst hs
      exact .inl rfl
    | _ => exact absurd hs (by simp [PostSite])

/-- **After a final site the thread's states are post sites** or the machine has stopped. -/
theorem post_all {g j : Nat} {e : Event}
    {s : TSt} (he : X.get (g, j) = some e) (hσ : St Q L X g j = some (some s))
    (hs : FinalSite s) : ∀ m, j + 1 ≤ m → St Q L X g m = none ∨ St Q L X g m = some none ∨
      ∃ s', St Q L X g m = some (some s') ∧ PostSite s' := by
  have he' : (X.tr g)[j]? = some e := he
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have h1 : St Q L X g (j + 1) = (threadCode L g Q).next s e := by
      show Frame.stateAt (code L Q) X g (j + 1) = _
      rw [Frame.stateAt_succ he']
      have : Frame.stateAt (code L Q) X g j = some (some s) := hσ
      rw [this]
      rfl
    rcases final_next (g := g) (Q := Q) (L := L) hs e with h | ⟨s', h, hp⟩
    · exact .inr (.inl (h1.trans h))
    · exact .inr (.inr ⟨s', h1.trans h, hp⟩)
  | succ m hm ih =>
    by_cases hl : m < (X.tr g).length
    · obtain ⟨e', he''⟩ : ∃ e', (X.tr g)[m]? = some e' := ⟨_, List.getElem?_eq_getElem hl⟩
      have h1 : St Q L X g (m + 1) =
          (Frame.stateAt (code L Q) X g m).bind
            fun σ => (threadCode L g Q).toMachine.next σ e' := by
        show Frame.stateAt (code L Q) X g (m + 1) = _
        rw [Frame.stateAt_succ he'']
      rcases ih with h | h | ⟨s', h, hp⟩
      · have h' : Frame.stateAt (code L Q) X g m = none := h
        rw [h'] at h1
        exact .inl h1
      · have h' : Frame.stateAt (code L Q) X g m = some none := h
        rw [h'] at h1
        exact .inr (.inl h1)
      · have h' : Frame.stateAt (code L Q) X g m = some (some s') := h
        rw [h'] at h1
        rcases post_next (g := g) (Q := Q) (L := L) hp e' with hn | ⟨s'', hn, hp'⟩
        · exact .inl (h1.trans hn)
        · exact .inr (.inr ⟨s'', h1.trans hn, hp'⟩)
    · have h1 : St Q L X g (m + 1) = St Q L X g m := by
        show Frame.stateAt (code L Q) X g (m + 1) = Frame.stateAt (code L Q) X g m
        rw [Frame.stateAt_of_le (k := m + 1) (by omega), Frame.stateAt_of_le (k := m) (by omega)]
      rw [h1]
      exact ih

/-- **`Bar0Facts.one`**: a thread has at most one last-generation arrival. -/
theorem bar0_one (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g j j' : Nat} (_ : g < L.threads) (h1 : FinalArr X 0 2 g j) (h2 : FinalArr X 0 2 g j') :
    j = j' := by
  have key : ∀ {a b : Nat}, FinalArr X 0 2 g a → FinalArr X 0 2 g b → a < b → False := by
    intro a b ha hb hab
    obtain ⟨pca, ma, hea, hka⟩ := ha
    obtain ⟨pcb, mb, heb, hkb⟩ := hb
    obtain ⟨s, hσ, hfs⟩ := final_site hpre hX hS ht hea hka
    obtain ⟨s', hσ', hfs'⟩ := final_site hpre hX hS ht heb hkb
    rcases post_all hea hσ hfs b hab with h | h | ⟨s'', h, hp⟩
    · rw [h] at hσ'; cases hσ'
    · rw [h] at hσ'; cases hσ'
    · rw [h] at hσ'
      obtain rfl := Option.some.inj (Option.some.inj hσ')
      exact not_final_of_post hp hfs'
  rcases Nat.lt_trichotomy j j' with h | h | h
  · exact (key h1 h2 h).elim
  · exact h
  · exact (key h2 h1 h).elim

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
