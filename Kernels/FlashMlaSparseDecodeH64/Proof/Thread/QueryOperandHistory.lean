-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
public import Lemmas.Flow.TraceInduction
import Lemmas.Flow.Final

@[expose] public section

/-! # The query-copy acquire and fence before QK -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryOperandHistory

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

private def stage : Wg1Mma.Site → Nat
  | .qCopyFence => 1
  | .kvWait | .kvFence | .qkMma _ | .qkCommit | .soWait | .soFence | .pvMma _ | .pvCommit
  | .outBar => 2
  | _ => 0

private def captured (k : Nat) (d : Wg1Mma.D) (e : Event) : Prop :=
  (k = 1 ∧ d.site = .qCopyFence) ∨
    (k = 0 ∧ d.site = .qCopyWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc)

set_option maxHeartbeats 1200000 in
private theorem advance {k : Nat} {d d' : Wg1Mma.D} {e : Event}
    (hn : Wg1Mma.next P L g d e = some (some d')) (hk : k < stage d'.site) :
    k < stage d.site ∨ captured k d e := by
  cases hd : d.site <;> simp only [Wg1Mma.next, hd, Wg1Mma.nextSite] at hn
  case qCopyWait =>
    cases he : e.kind <;> simp [he] at hn
    rename_i m p ok acq sc
    cases ok <;> simp at hn <;> cases hn
    · exact .inl (by simpa [hd] using hk)
    · have hk0 : k < 1 := hk
      exact .inr (.inr ⟨by omega, hd, m, p, acq, sc, he⟩)
  case qCopyFence =>
    by_cases hp : Wg1Mma.total P L g < 64 <;>
      simp only [hp, ↓reduceIte, Option.some.injEq] at hn
    all_goals subst d'
    all_goals
      have hk' : k < 2 := hk
      by_cases h1 : k = 1
      · exact .inr (.inl ⟨h1, hd⟩)
      · exact .inl (by change k < 1; omega)
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    try simp only [Wg1Mma.startSite, Wg1Mma.afterTopk] at hk
    repeat' split_ifs at hk
    all_goals simp_all [stage]

private def needs (k : Nat) : Option Machine.ThreadD → Prop
  | some (.mma d) => k < stage d.site
  | _ => False

private def source (P : Params) (L : Launch) (g k : Nat) (pre : List Event) : Prop :=
  ∃ j d e o, pre[j]? = some e ∧
    (Machine.machine P L g).after (some (.prologue .shfl0)) (pre.take j) =
      some (some (.mma d)) ∧
    captured k d e ∧ (Machine.machine P L g).Fired (some (.mma d)) e o

private def history (P : Params) (L : Launch) (g k : Nat)
    (s : Option Machine.ThreadD) (pre : List Event) : Prop :=
  (Machine.machine P L g).after (some (.prologue .shfl0)) pre = some s ∧
    (needs k s → source P L g k pre)

private theorem source_append {k : Nat} {pre : List Event} {e : Event}
    (h : source P L g k pre) : source P L g k (pre ++ [e]) := by
  obtain ⟨j, d, f, o, hf, ha, hcap, hfire⟩ := h
  have hj := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨j, d, f, o, ?_, ?_, hcap, hfire⟩
  · rwa [List.getElem?_append_left hj]
  · rwa [List.take_append_of_le_length hj.le]

private theorem history_step {k : Nat} {s s' : Option Machine.ThreadD}
    {pre : List Event} {e : Event} {o : Option TState}
    (h : history P L g k s pre) (hf : (Machine.machine P L g).Fired s e o)
    (hn : (Machine.machine P L g).next s e = some s') :
    history P L g k s' (pre ++ [e]) := by
  refine ⟨?_, ?_⟩
  · rw [Machine.after_snoc (M := Machine.machine P L g) (some (.prologue .shfl0)) pre e, h.1]
    exact hn
  intro hw
  cases s with
  | none =>
    change some none = some s' at hn
    cases hn
    exact hw.elim
  | some s =>
    change Machine.next P L g s e = some s' at hn
    cases s
    case mma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hnext
        cases hn
        rcases advance hnext hw with hprev | hcap
        · exact source_append (h.2 hprev)
        · refine ⟨pre.length, d, e, o, by simp, ?_, hcap, hf⟩
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          exact h.1
      · split_ifs at hn <;> cases hn <;> exact hw.elim
      · split_ifs at hn
        cases hn
        exact hw.elim
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact hw.elim
      · split at hn
        · rename_i w _
          split_ifs at hn <;> fin_cases w <;> cases hn <;> exact hw.elim
        · cases hn
          exact hw.elim
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> first
        | exact hw.elim
        | exact ((Nat.not_lt_zero k) hw).elim
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals exact hw.elim

variable {mem0 : Mem0} {X : Execution}

private theorem source_before {k i : Nat} {d : Wg1Mma.D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hk : k < stage d.site) :
    ∃ j < i, ∃ q f u, X.get (g, j) = some f ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ captured k q f ∧
      (Machine.machine P L g).Fired (some (.mma q)) f (some u) := by
  have hg := Frame.lt_of_get hX he
  have hr := (hs.produces (hX.thr g hg)).prefix_induction (history P L g k)
    ⟨rfl, False.elim⟩ (fun _ _ _ _ _ => history_step) i (some (.mma d)) hd
  obtain ⟨j, q, f, o, hf, hstate, hcap, hfire⟩ := hr.2 hk
  have hj := (List.getElem?_eq_some_iff.mp hf).1
  have hji : j < i := hj.trans_le (List.length_take_le _ _)
  have hget : X.get (g, j) = some f := List.getElem?_eq_some_iff.mpr
    ⟨hj.trans_le (List.length_take_le' _ _), by simpa using (List.getElem?_eq_some_iff.mp hf).2⟩
  rw [List.take_take, Nat.min_eq_left hji.le] at hstate
  cases o with
  | none =>
    obtain ⟨t, _, hf⟩ := hfire
    obtain ⟨_, hrun⟩ := hX.thr g hg
    have hlen := PTX.Flow.Run.end_last hrun hget (fires_none_ends hf)
    have hi : i < (X.tr g).length := PTX.len_of_get he
    omega
  | some u => exact ⟨j, hji, q, f, u, hget, hstate, hcap, hfire⟩


/-- The actual QK issue follows the successful local query-copy acquire and its fence. -/
theorem wait_and_fence_before_qk {i : Nat} {d : Wg1Mma.D} {k : Fin 16} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qkMma k) :
    ∃ w f tag ft, w < f ∧ f < i ∧
      X.get (g, w) = some
        ⟨tag, .wait ⟨.shared, ctaOf L g, L.sharedBase + 222784⟩ 0 true true .cta⟩ ∧
      X.get (g, f) = some ⟨ft, .tc .fenceAfter⟩ := by
  obtain ⟨f, hfi, q, ev, u, hget, hst, hcap, hfire⟩ :=
    source_before (k := 1) hX hs he hd (by rw [hsite]; change 1 < 2; decide)
  have hfs : q.site = .qCopyFence := by
    rcases hcap with h | h
    · exact h.2
    · have := h.1
      omega
  have hcode : kernel.code[q.site.pc]? = some ⟨none, .tcFenceAfter⟩ := by
    rw [hfs]
    exact Flow.code_1986
  obtain ⟨t, _, hf⟩ := RingGateEvents.fired_at_code hfire hcode
  change ev = ⟨q.site.pc, .tc .fenceAfter⟩ ∧ some u = some (PTX.next t) at hf
  obtain ⟨w, hwf, p, we, v, hgetw, hp, hwait, hF⟩ :=
    source_before (k := 0) hX hs hget hst (by rw [hfs]; decide)
  rcases hwait with h | ⟨_, hws, _, _, _, _, hok⟩
  · have := h.1
    omega
  · obtain ⟨ok, hw⟩ := RingEvents.mma_wait_exact hpre (.inr (.inl hws)) hF
    have hw' : we.kind = .wait ⟨.shared, ctaOf L g, L.sharedBase + 222784⟩
        0 ok true .cta := by simpa [hws, ctaOf] using hw
    have hv := (Kind.wait.inj (hw'.symm.trans hok)).2.2.1
    obtain ⟨tag, kind⟩ := we
    change kind = _ at hw'
    rw [hv] at hw'
    exact ⟨w, f, tag, _, hwf, hfi, by rw [hgetw, hw'], hget.trans (congrArg some hf.1)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryOperandHistory
