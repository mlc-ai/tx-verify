-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CtaBarArrive
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # Appending one warp's arrival on a named barrier

A proof tool for the progress layer of a kernel with named barriers whose participants may exit
or use `bar.arrive`. In a maximal execution with no CTA barrier fault, a warp whose lanes all
have their arrival on named barrier `id` as their last event, unrecorded, has its arrival record
appended (`append_warp`): the resource accepts it, since an arrival of a live warp with a valid
operand that the resource refused would be a fault (`CtaBarFault`). The extension is maximal,
with the same traces.

The lanes of a warp are recorded together (`recorded_of_lane`): a record of the warp holds every
lane that has not exited, with its arrival of the same ordinal. So a thread whose last event is
an unrecorded arrival, every lane of whose warp has made its arrival of that ordinal, is
recorded in an extension with the same traces (`arrive_release`). -/

/-- The well-formedness assumptions survive appending to one CTA's barrier history. -/
def PTX.Assumption.WfCtaHistory {L : PTX.Launch} {K : PTX.Kernel} {mem0 : PTX.Mem0}
    (A : List PTX.Assumption) : Prop :=
  ∀ (X : PTX.Execution) c suffix, PTX.Consistent L K A mem0 X →
    ∀ a ∈ A, a.wf L mem0 (X.withCtaHistory c (X.barriers c ++ suffix))

theorem PTX.Assumption.WfStep.ctaHistory {L : PTX.Launch} {K : PTX.Kernel}
    {mem0 : PTX.Mem0} {A : List PTX.Assumption} {sel : Nat → Bool}
    (hA : PTX.Assumption.WfStep sel L K mem0 A) :
    PTX.Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A := by
  intro X c suffix hX
  exact hA X _ hX (X.le_withCtaHistory c ⟨suffix, rfl⟩)
    (PTX.Execution.notifiedInOrder_of_eq rfl) (PTX.Execution.noNewRead_of_tr rfl)

theorem PTX.Assumption.WfInOrder.ctaHistory {L : PTX.Launch} {K : PTX.Kernel}
    {mem0 : PTX.Mem0} {A : List PTX.Assumption} {sel : Nat → Bool}
    (hA : PTX.Assumption.WfInOrder sel L K mem0 A) :
    PTX.Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A :=
  hA.step.ctaHistory

namespace PTX.NamedBar
open PTX CtaBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The arrival record of warp `w` of CTA `c` on named barrier `id` with operand `cnt`, holding
the last event of each of its lanes. -/
def warpRecord (L : Launch) (X : Execution) (c w id : Nat) (cnt : Option Nat) :
    Record EvId :=
  .arrival id w cnt (fullLanes L.block w fun lt =>
    (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1))

/-- An arrival of a live warp with a valid identifier and operand that the resource refuses is a
fault: a duplicate arrival or a count mismatch. -/
theorem arrive_fault_of_error {block id w n : Nat} {cnt : Option Nat} {s : State} {err : Error}
    (hid : id < 16) (hw : w < warps block ∧ warpLive block s.exited w)
    (hn : target block cnt = .ok n) (h : arrive block s id w cnt = .error err) :
    err.isFault = true := by
  simp only [arrive, hid, hw, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, and_self, ↓reduceIte] at h
  split_ifs at h
  · cases h; rfl
  · split at h
    · split_ifs at h
      cases h; rfl
    · cases h

/-- A lane with no exit event is not exited in a state of its CTA's history. -/
theorem not_exited_of_noExit (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {k lt : Nat} {s : State} (hs : CtaBarrier.run L.block {} ((X.barriers c).take k) = .ok s)
    (hno : ∀ j pc, X.get (c * L.block + lt, j) ≠ some ⟨pc, .exit⟩) : lt ∉ s.exited := by
  intro hm
  obtain ⟨a, ha⟩ := run_exited_mem hs hm
  obtain ⟨-, ha1, pc, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_mem_take ha)
  exact hno a.2 pc (by rw [← ha1]; exact hget)

/-- A refused append of the full incoming arrival of one specified warp. -/
def WarpAppendFault (L : Launch) (X : Execution) (c w id : Nat) (cnt : Option Nat) : Prop :=
  ∃ s err, CtaBarrier.run L.block {} (X.barriers c) = .ok s ∧
    CtaBarSources L X c (warpRecord L X c w id cnt) ∧
    (∀ e ∈ (warpRecord L X c w id cnt).refs, e ∉ (X.barriers c).flatMap Record.refs) ∧
    (warpRecord L X c w id cnt).perform L.block s = .error err ∧ err.isFault

theorem WarpAppendFault.ctaBarFault {c w id : Nat} {cnt : Option Nat} (hc : c < L.grid)
    (h : WarpAppendFault L X c w id cnt) : CtaBarFault L X := by
  obtain ⟨s, err, hr, hsrc, hfresh, hperf, hFault⟩ := h
  exact ⟨c, hc, s, hr, id, w, cnt, _, err, hsrc,
    fun q hq => hfresh q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩), hperf, hFault⟩

/-- Appending the warp record changes only its CTA barrier history, when this particular append
cannot fault. -/
theorem append_warp_in_history (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A) {c w id n : Nat}
    {cnt : Option Nat} (hf : ¬ WarpAppendFault L X c w id cnt)
    (hc : c < L.grid) (hw : w * 32 < L.block) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlane : ∀ lt, lt < L.block → lt / 32 = w →
      (∃ pc m, X.get (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1) =
        some ⟨pc, .bar id cnt m⟩) ∧
      (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1) ∉
        (X.barriers c).flatMap Record.refs) :
    Maximal L K A mem0
      (X.withCtaHistory c (X.barriers c ++ [warpRecord L X c w id cnt])) := by
  have hX := hmax.1
  let event : Nat → EvId := fun lt => (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1)
  obtain ⟨s, hs⟩ := (hX.ctaBar.2 c hc).2.2
  have hnoexit : ∀ lt, lt < L.block → lt / 32 = w → ∀ j pc,
      X.get (c * L.block + lt, j) ≠ some ⟨pc, .exit⟩ := by
    intro lt hlt hlw j pc hj
    obtain ⟨⟨pc', m, hb⟩, -⟩ := hlane lt hlt hlw
    have hl := Execution.exit_last hX (cta_thread_lt hc hlt) hj
    have hj' : j = (X.tr (c * L.block + lt)).length - 1 := by omega
    rw [hj', hb] at hj
    cases hj
  have hlive : ∀ lt < L.block, lt / 32 = w → lt ∉ s.exited := by
    intro lt hlt hlw
    refine not_exited_of_noExit hX hc (k := (X.barriers c).length) ?_ (hnoexit lt hlt hlw)
    rw [List.take_length]
    exact hs
  have hperf := fullLanes_perform_of (block := L.block) (warp := w) (id := id) (cnt := cnt)
    (s := s) hlive event
  have hsrc : CtaBarSources L X c (warpRecord L X c w id cnt) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := mem_fullLanes.mp hq
    obtain ⟨⟨pc, m, hb⟩, -⟩ := hlane q.1 h1 h2
    exact ⟨h1, by rw [h3], pc, m, by rw [h3]; exact hb⟩
  have hfresh : ∀ e ∈ (warpRecord L X c w id cnt).refs,
      e ∉ (X.barriers c).flatMap Record.refs := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    obtain ⟨h1, h2, h3⟩ := mem_fullLanes.mp hq
    rw [h3]
    exact (hlane q.1 h1 h2).2
  obtain ⟨t, ht⟩ : ∃ t, (warpRecord L X c w id cnt).perform L.block s = .ok t := by
    change ∃ t, Record.perform L.block s (.arrival id w cnt (fullLanes L.block w event)) = _
    rw [hperf]
    cases ha : arrive L.block s id w cnt with
    | ok t => exact ⟨t, rfl⟩
    | error err =>
      exfalso
      have hwl : warpLive L.block s.exited w :=
        ⟨0, by simp, by omega, hlive _ (by omega) (by omega)⟩
      have hwb : w < warps L.block := by unfold warps; omega
      refine hf ⟨s, err, hs, hsrc, hfresh, ?_, arrive_fault_of_error hid ⟨hwb, hwl⟩ hn ha⟩
      change Record.perform L.block s (.arrival id w cnt (fullLanes L.block w event)) = _
      rwa [hperf]
  have hhist : CtaBarHistoryOk L
      (X.withCtaHistory c (X.barriers c ++ [warpRecord L X c w id cnt])) := by
    constructor
    · intro d hd
      rw [withCtaHistory_barriers_ne X _ (by omega)]
      exact hX.ctaBar.1 d hd
    · intro d hd
      by_cases hdc : d = c
      · subst hdc
        rw [withCtaHistory_barriers_self]
        refine ⟨?_, ?_, t, ?_⟩
        · rw [List.flatMap_append]
          refine List.nodup_append.mpr ⟨(hX.ctaBar.2 d hc).1, ?_, ?_⟩
          · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, warpRecord,
              Record.refs, fullLanes, List.map_map]
            refine (List.nodup_range.filter _).map ?_
            intro a b hab
            have := congrArg Prod.fst hab
            simp only [Function.comp_apply] at this
            omega
          · intro e he f hf' hef
            subst hef
            exact hfresh e (by simpa using hf') he
        · intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact (hX.ctaBar.2 d hc).2.1 r hr
          · rw [List.mem_singleton] at hr
            subst hr
            exact hsrc
        · rw [run_append, hs]
          simp [CtaBarrier.run, ht, Except.bind]
      · rw [withCtaHistory_barriers_ne X _ hdc]
        exact hX.ctaBar.2 d hd
  have hterm : ∀ e ∈ [warpRecord L X c w id cnt].flatMap Record.refs,
      e.2 + 1 = (X.tr e.1).length := by
    intro e he
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    obtain ⟨h1, h2, h3⟩ := mem_fullLanes.mp hq
    obtain ⟨⟨pc, m, hb⟩, -⟩ := hlane q.1 h1 h2
    have hl := len_of_get hb
    rw [h3]
    simp only at hl ⊢
    omega
  obtain ⟨-, -, -, hmaxY⟩ := Step.CtaBar.release_append_arrive hmax hc
    (fun r hr => by rw [List.mem_singleton] at hr; exact ⟨_, _, _, _, hr⟩) hhist
    (hA X c _ hX) hterm
  exact hmaxY

/-- **Appending a warp's arrival.** In a maximal execution with no CTA barrier fault, let every
lane of warp `w` of CTA `c` have as its last event an arrival on named barrier `id < 16` with
the valid operand `cnt`, unrecorded. Then appending the warp's arrival record to the CTA's
history gives a maximal execution with the same traces. -/
theorem append_warp_of_wf (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    (hf : ¬ CtaBarFault L X) {c w id n : Nat}
    {cnt : Option Nat} (hc : c < L.grid) (hw : w * 32 < L.block) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlane : ∀ lt, lt < L.block → lt / 32 = w →
      (∃ pc m, X.get (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1) =
        some ⟨pc, .bar id cnt m⟩) ∧
      (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1) ∉
        (X.barriers c).flatMap Record.refs) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
      Y.barriers c = X.barriers c ++ [warpRecord L X c w id cnt] ∧
      ∀ d, d ≠ c → Y.barriers d = X.barriers d :=
  ⟨_, append_warp_in_history hmax hA (fun h => hf (h.ctaBarFault hc)) hc hw hid hn hlane, rfl,
    withCtaHistory_barriers_self _ _ _, fun _ hd => withCtaHistory_barriers_ne X _ hd⟩

/-- The step well-formedness rule suffices for appending one warp's arrival. -/
theorem append_warp (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfStep sel L K mem0 A) (hf : ¬ CtaBarFault L X) {c w id n : Nat}
    {cnt : Option Nat} (hc : c < L.grid) (hw : w * 32 < L.block) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlane : ∀ lt, lt < L.block → lt / 32 = w →
      (∃ pc m, X.get (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1) =
        some ⟨pc, .bar id cnt m⟩) ∧
      (c * L.block + lt, (X.tr (c * L.block + lt)).length - 1) ∉
        (X.barriers c).flatMap Record.refs) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
      Y.barriers c = X.barriers c ++ [warpRecord L X c w id cnt] ∧
      ∀ d, d ≠ c → Y.barriers d = X.barriers d := by
  exact append_warp_of_wf hmax hA.ctaHistory hf hc hw hid hn hlane

/-- **The lanes of a warp are recorded together.** If lane `ly` of a warp of CTA `c` has its
arrival on named barrier `id` recorded, a lane `lz` of the same warp with no exit event has its
arrival of the same ordinal recorded too. -/
theorem recorded_of_lane (hX : Consistent L K A mem0 X) {c id ly lz i j pc pc' : Nat}
    {cnt cnt' : Option Nat} {m m' : BarMode} (hc : c < L.grid) (hly : ly < L.block)
    (hlz : lz < L.block) (hw : ly / 32 = lz / 32)
    (he : X.get (c * L.block + ly, i) = some ⟨pc, .bar id cnt m⟩)
    (hf : X.get (c * L.block + lz, j) = some ⟨pc', .bar id cnt' m'⟩)
    (hord : ((X.tr (c * L.block + ly)).take i).countP (Execution.isBarId id) =
      ((X.tr (c * L.block + lz)).take j).countP (Execution.isBarId id))
    (hrec : (c * L.block + ly, i) ∈ (X.barriers c).flatMap Record.refs)
    (hno : ∀ k pc, X.get (c * L.block + lz, k) ≠ some ⟨pc, .exit⟩) :
    (c * L.block + lz, j) ∈ (X.barriers c).flatMap Record.refs := by
  obtain ⟨r, hr, href⟩ := List.mem_flatMap.mp hrec
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
  obtain ⟨s, t, hs, ht⟩ := run_at_record hlast hk
  have hsrc := (hX.ctaBar.2 c hc).2.1 r hr
  cases r with
  | exit x y =>
    obtain ⟨-, -, pcx, hget⟩ := hsrc
    have hy : y = (c * L.block + ly, i) := (List.mem_singleton.mp href).symm
    rw [hy, he] at hget
    cases hget
  | arrival id' w' cnt'' lanes =>
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp href
    obtain ⟨-, hq2, pcq, mq, hqb⟩ := hsrc q hq
    rw [hqe, he] at hqb
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hqb
    obtain ⟨-, rfl, -, -⟩ := hqb
    have hq1 : q.1 = ly := by
      rw [hqe] at hq2
      simp only at hq2
      omega
    have hlanes := perform_arrival_lanes ht
    have hyl := hlanes.2.1 q hq
    have hzx : lz ∉ s.exited := not_exited_of_noExit hX hc hs hno
    obtain ⟨q', hq', hq'z⟩ := List.mem_map.mp
      (hlanes.2.2 lz hlz (by rw [← hw, ← hq1]; exact hyl.2.1) hzx)
    obtain ⟨-, hq'2, pcz, mz, hzb⟩ := hsrc q' hq'
    have hcz := cta_prefix_id_arrival_count (id := id) hX hc hk
      (List.mem_map.mpr ⟨q', hq', rfl⟩) hs hlz (by rw [hq'2, hq'z]) hzx rfl
    have hcy := cta_prefix_id_arrival_count (id := id) hX hc hk href hs hly rfl
      (hq1 ▸ hyl.2.2) rfl
    have hq'e : q'.2 = (c * L.block + lz, q'.2.2) := by
      rw [← hq'z, ← hq'2]
    rw [hq'e] at hzb hcz
    simp only at hcz hcy
    rw [hw] at hcy
    have hf' : (X.tr (c * L.block + lz))[j]? = some ⟨pc', .bar id cnt' m'⟩ := hf
    have hzb' : (X.tr (c * L.block + lz))[q'.2.2]? = some ⟨pcz, .bar id cnt'' mz⟩ := hzb
    have hidx := ordinal_unique (X := X) (g := c * L.block + lz) (id := id) hf' hzb'
      (by simp [Execution.isBarId]) (by simp [Execution.isBarId]) (by omega)
    refine List.mem_flatMap.mpr ⟨_, hr, List.mem_map.mpr ⟨q', hq', ?_⟩⟩
    rw [hq'e, hidx]

/-- **A thread at an unrecorded arrival whose warp has arrived is recorded in an extension.** In a
maximal execution with no CTA barrier fault, let thread `g`'s last event be an unrecorded arrival
on named barrier `id < 16` with the valid operand `cnt`, and let every lane of its warp have made
its arrival on `id` of the same ordinal with operand `cnt`. Then a maximal execution with the
same traces records `g`'s arrival. -/
theorem arrive_release_preserving_objects (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfStep sel L K mem0 A) (hf : ¬ CtaBarFault L X) {g pc id n : Nat}
    {cnt : Option Nat} {m : BarMode} (hg : g < L.threads) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt m⟩)
    (hnr : (g, (X.tr g).length - 1) ∉ (X.barriers (g / L.block)).flatMap Record.refs)
    (hlane : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 → ∃ j pc' m',
      X.get (g / L.block * L.block + lt, j) = some ⟨pc', .bar id cnt m'⟩ ∧
      ((X.tr (g / L.block * L.block + lt)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      (g, (X.tr g).length - 1) ∈ (Y.barriers (g / L.block)).flatMap Record.refs := by
  have hX := hmax.1
  have hb := block_pos_of_thread_lt hg
  have hc := cta_lt hg
  have hgl : g % L.block < L.block := Nat.mod_lt _ hb
  have hgeq : g / L.block * L.block + g % L.block = g := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod g L.block
  have hgno : ∀ k pc', X.get (g / L.block * L.block + g % L.block, k) ≠ some ⟨pc', .exit⟩ := by
    intro k pc' hk
    rw [hgeq] at hk
    have hl := Execution.exit_last hX hg hk
    have hk' : k = (X.tr g).length - 1 := by omega
    rw [hk', hlast] at hk
    cases hk
  have hlast' : X.get (g / L.block * L.block + g % L.block,
      (X.tr (g / L.block * L.block + g % L.block)).length - 1) = some ⟨pc, .bar id cnt m⟩ := by
    rw [hgeq]; exact hlast
  have hlane' : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 →
      (∃ pc m, X.get (g / L.block * L.block + lt,
        (X.tr (g / L.block * L.block + lt)).length - 1) = some ⟨pc, .bar id cnt m⟩) ∧
      (g / L.block * L.block + lt, (X.tr (g / L.block * L.block + lt)).length - 1) ∉
        (X.barriers (g / L.block)).flatMap Record.refs := by
    intro lt hlt hlw
    obtain ⟨j, pc', m', hget, hord⟩ := hlane lt hlt hlw
    have hnrj : (g / L.block * L.block + lt, j) ∉
        (X.barriers (g / L.block)).flatMap Record.refs := by
      intro hrec
      apply hnr
      have := recorded_of_lane hX hc hlt hgl hlw hget hlast'
        (by rw [hord, hgeq]) hrec hgno
      rwa [hgeq] at this
    have hdiv := (lane_cta (c := g / L.block) hb hlt).1
    rcases recorded_or_last hX hget with hrec | hl
    · rw [hdiv] at hrec
      exact absurd hrec hnrj
    · simp only at hl
      have hj : (X.tr (g / L.block * L.block + lt)).length - 1 = j := by omega
      rw [hj]
      exact ⟨⟨pc', m', hget⟩, hnrj⟩
  have hmaxY := append_warp_in_history hmax hA.ctaHistory
    (fun h => hf (h.ctaBarFault hc)) hc (w := g % L.block / 32) (by omega) hid hn hlane'
  refine ⟨_, hmaxY, rfl, rfl, ?_⟩
  rw [withCtaHistory_barriers_self, List.flatMap_append]
  refine List.mem_append_right _ ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, warpRecord, Record.refs]
  refine List.mem_map.mpr ⟨(g % L.block, (g / L.block * L.block + g % L.block,
    (X.tr (g / L.block * L.block + g % L.block)).length - 1)),
    mem_fullLanes.mpr ⟨hgl, rfl, rfl⟩, ?_⟩
  simp only [hgeq]

/-- **A thread at an unrecorded arrival whose warp has arrived is recorded in an extension.** In a
maximal execution with no CTA barrier fault, let thread `g`'s last event be an unrecorded arrival
on named barrier `id < 16` with the valid operand `cnt`, and let every lane of its warp have made
its arrival on `id` of the same ordinal with operand `cnt`. Then a maximal execution with the
same traces records `g`'s arrival. -/
theorem arrive_release (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfStep sel L K mem0 A) (hf : ¬ CtaBarFault L X) {g pc id n : Nat}
    {cnt : Option Nat} {m : BarMode} (hg : g < L.threads) (hid : id < 16)
    (hn : target L.block cnt = .ok n)
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt m⟩)
    (hnr : (g, (X.tr g).length - 1) ∉ (X.barriers (g / L.block)).flatMap Record.refs)
    (hlane : ∀ lt, lt < L.block → lt / 32 = g % L.block / 32 → ∃ j pc' m',
      X.get (g / L.block * L.block + lt, j) = some ⟨pc', .bar id cnt m'⟩ ∧
      ((X.tr (g / L.block * L.block + lt)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
      (g, (X.tr g).length - 1) ∈ (Y.barriers (g / L.block)).flatMap Record.refs := by
  obtain ⟨Y, hY, hTrace, _, hRecord⟩ :=
    arrive_release_preserving_objects hmax hA hf hg hid hn hlast hnr hlane
  exact ⟨Y, hY, hTrace, hRecord⟩

end

end PTX.NamedBar
