-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.Execution.NoTma
public import Lemmas.Async.AsyncExecution
public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Order.OrderWaits

@[expose] public section

/-!
# Appending thread instructions

Appending a thread instruction preserves all independent asynchronous effects and object
histories. It does not synthesize a copy completion or a barrier observation. Instructions
which operate on an mbarrier need a corresponding history extension before consistency
can be established.
-/
namespace PTX
noncomputable section

/-- Append one source-thread event. Async effects and object records are unchanged. -/
def Execution.snoc (X : Execution) (g : Nat) (e : Event)
    (r : Nat → Option AsyncCopy.Ref) : Execution :=
  { X with
    tr := fun h => if h = g then X.tr g ++ [e] else X.tr h
    rf := fun v k => if v = .thread (g, (X.tr g).length) then r k else X.rf v k }

/-- The events of the launch. -/
def Execution.events (X : Execution) (L : Launch) : List EvId :=
  (List.range L.threads).flatMap fun g => (List.range (X.tr g).length).map fun i => (g, i)

theorem Execution.ShflK.lt {X : Execution} {e : EvId} {n : Nat} (h : X.ShflK e n) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨⟨pc, m, a, b, c, r, o, hs⟩, -⟩ := h
  unfold Execution.get at hs; exact (List.getElem?_eq_some_iff.mp hs).1

theorem Execution.TcK.lt {X : Execution} {v : EvId} {k : Nat} (h : X.TcK v k) :
    v.2 < (X.tr v.1).length := by
  obtain ⟨⟨ev, hv, -⟩, -⟩ := h; exact len_of_get hv

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}

theorem snoc_tr (h : Nat) :
    (X.snoc g e r).tr h = if h = g then X.tr g ++ [e] else X.tr h := rfl

theorem snoc_len (h : Nat) :
    ((X.snoc g e r).tr h).length = if h = g then (X.tr g).length + 1 else (X.tr h).length := by
  rw [snoc_tr]; split_ifs <;> simp

theorem snoc_get (v : EvId) :
    (X.snoc g e r).get v = if v = (g, (X.tr g).length) then some e else X.get v := by
  obtain ⟨h, i⟩ := v
  unfold Execution.get
  simp only [snoc_tr, Prod.mk.injEq]
  by_cases hh : h = g
  · subst hh
    simp only [↓reduceIte, true_and]
    rcases Nat.lt_trichotomy i (X.tr h).length with hi | hi | hi
    · rw [List.getElem?_append_left hi, ite_eq_right (by omega)]
    · subst hi; simp
    · rw [ite_eq_right (by omega), List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]
  · simp [hh]

theorem snoc_get_old {v : EvId} (hv : v.2 < (X.tr v.1).length) :
    (X.snoc g e r).get v = X.get v := by
  rw [snoc_get, ite_eq_right]; rintro rfl; simp at hv

theorem snoc_take {v : EvId} (hv : v.2 ≤ (X.tr v.1).length) :
    ((X.snoc g e r).tr v.1).take v.2 = (X.tr v.1).take v.2 := by
  rw [snoc_tr]; split_ifs with h
  · subst h; rw [List.take_append_of_le_length hv]
  · rfl

theorem snoc_tcK_of_old {v : EvId} {k : Nat} (hv : v.2 < (X.tr v.1).length) :
    (X.snoc g e r).TcK v k ↔ X.TcK v k := by
  unfold Execution.TcK; rw [snoc_get_old hv, snoc_take hv.le]

/-- Resource histories are unchanged by a pure thread-trace extension. -/
theorem snoc_ctaBarK_old {v : EvId} {key : Nat} (hv : v.2 < (X.tr v.1).length) :
    CtaBarK L (X.snoc g e r) v key ↔ CtaBarK L X v key := by
  unfold CtaBarK Execution.IsBarrier
  rw [snoc_get_old hv]
  rfl

theorem snoc_ctaBarK (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) {v : EvId} {key : Nat} :
    CtaBarK L (X.snoc g e r) v key ↔ CtaBarK L X v key := by
  constructor
  · intro hk
    have hv : v.2 < (X.tr v.1).length := by
      obtain ⟨count, pc, hp⟩ := hk.2.1
      unfold Execution.IsBarrier at hp
      rw [snoc_get] at hp
      split_ifs at hp with hn
      · have he : e.kind = .bar (key % 16) count := congrArg Event.kind (Option.some.inj hp)
        exact (hnb _ _ _ he).elim
      · exact len_of_get hp
    exact (snoc_ctaBarK_old hv).mp hk
  · intro hk
    exact (snoc_ctaBarK_old hk.lt).mpr hk

theorem snoc_ctaBarArrivalK_old {v : EvId} {key : Nat} (hv : v.2 < (X.tr v.1).length) :
    CtaBarArrivalK L (X.snoc g e r) v key ↔ CtaBarArrivalK L X v key := by
  unfold CtaBarArrivalK Execution.IsBarArrival
  rw [snoc_get_old hv]
  rfl

theorem snoc_ctaBarArrivalK (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) {v : EvId}
    {key : Nat} : CtaBarArrivalK L (X.snoc g e r) v key ↔ CtaBarArrivalK L X v key := by
  constructor
  · intro hk
    have hv : v.2 < (X.tr v.1).length := by
      obtain ⟨count, pc, mode, hp⟩ := hk.2.1
      rw [snoc_get] at hp
      split_ifs at hp with hn
      · have he : e.kind = .bar (key % 16) count mode := congrArg Event.kind (Option.some.inj hp)
        exact (hnb _ _ _ he).elim
      · exact len_of_get hp
    exact (snoc_ctaBarArrivalK_old hv).mp hk
  · intro hk
    exact (snoc_ctaBarArrivalK_old hk.lt).mpr hk

theorem snoc_shflK (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) {v : EvId}
    {n : Nat} : (X.snoc g e r).ShflK v n ↔ v.2 < (X.tr v.1).length ∧ X.ShflK v n := by
  constructor
  · intro hk
    obtain ⟨⟨pc, m, a, b, c, rv, ok, hs⟩, hcnt⟩ := hk
    rw [snoc_get] at hs
    split_ifs at hs with hv
    · cases e; cases hs; exact absurd rfl (hns m a b c rv ok)
    · have hlt : v.2 < (X.tr v.1).length := by
        unfold Execution.get at hs; exact (List.getElem?_eq_some_iff.mp hs).1
      exact ⟨hlt, ⟨pc, m, a, b, c, rv, ok, hs⟩, by rwa [snoc_take hlt.le] at hcnt⟩
  · rintro ⟨hv, ⟨pc, m, a, b, c, rv, ok, hs⟩, hcnt⟩
    exact ⟨⟨pc, m, a, b, c, rv, ok, by rw [snoc_get_old hv]; exact hs⟩, by rwa [snoc_take hv.le]⟩

theorem snoc_writes_old {w : EvId} {a : Acc} {bs : List Byte} (h : X.Writes w a bs) :
    (X.snoc g e r).Writes w a bs := by
  obtain ⟨pc, hp⟩ := h; exact ⟨pc, by rw [snoc_get_old (len_of_get hp)]; exact hp⟩

theorem snoc_get_new : (X.snoc g e r).get (g, (X.tr g).length) = some e := by
  rw [snoc_get, ite_eq_left rfl]

/-- Appending a thread event that is no linear copy changes no reduction element or reduction
read source. -/
theorem TensorStore.ReduceOk.snoc {A : List Assumption} {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (h : TensorStore.ReduceOk A X)
    (hc : ∀ s, e.kind ≠ .copy s) : TensorStore.ReduceOk A (X.snoc g e r) := by
  refine h.of_tensorStores rfl fun i s red j hY hw hperf => ⟨?_, rfl⟩
  obtain ⟨pc, hp⟩ := hY
  by_cases hi : i = (g, (X.tr g).length)
  · subst hi
    rw [snoc_get_new] at hp
    exact absurd (congrArg Event.kind (Option.some.inj hp)) (hc s)
  · rw [snoc_get, ite_eq_right hi] at hp
    exact ⟨pc, hp⟩

/-! ### `tcgen05` events of an extension -/

theorem le_snoc : X.le (X.snoc g e r) := by
  refine ⟨fun h => ?_, ?_, AsyncCopy.Extends.refl _,
    (fun _ => List.prefix_refl _), (Execution.le_refl X).2.2.2.2⟩
  · rw [snoc_tr]; split_ifs with hh
    · subst hh; exact List.prefix_append _ _
    · exact List.prefix_refl _
  · rintro v k ⟨a, bs, hv⟩
    change (if v = .thread (g, (X.tr g).length) then r k else X.rf v k) = _
    rw [ite_eq_right]
    rintro rfl
    rcases hv with ⟨pc, hp⟩ | ⟨new, pc, hp⟩
    · exact absurd (len_of_get hp) (by simp)
    · exact absurd (len_of_get hp) (by simp)

/-- Appending a thread event keeps the checked CTA barrier histories: no recorded reference and no
source check of a record changes. A new unrecorded `bar.arrive` may stay outside the history. -/
theorem CtaBarHistoryOk.snoc (hh : CtaBarHistoryOk L X) : CtaBarHistoryOk L (X.snoc g e r) :=
  hh.preserving le_snoc rfl

/-- A non-shuffle event leaves every shuffle source unchanged (DEP-WARP-SHUFFLE). -/
theorem snoc_shflOk (hs : ShflOk L X) (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) :
    ShflOk L (X.snoc g e r) := by
  intro h i n pc m a b c recv ok hget hk
  have hv := ((snoc_shflK hns).mp hk).1
  rw [snoc_get_old hv] at hget
  obtain ⟨h2, hsrc⟩ := hs h i n pc m a b c recv ok hget ((snoc_shflK hns).mp hk).2
  refine ⟨h2, ?_⟩
  rcases hsrc with ⟨j, pc', b', c', r', o', h3, h4⟩ | hx
  · exact .inl ⟨j, pc', b', c', r', o', (snoc_shflK hns).mpr ⟨len_of_get h4, h3⟩,
      by rw [snoc_get_old (len_of_get h4)]; exact h4⟩
  · exact .inr (Execution.shflExited_mono le_snoc hx)

/-- Appending an event whose kind carries no lane value keeps the ballot instances. -/
theorem snoc_voteOk (hX : VoteOk L X) (hn : e.kind.laneValue = false) (he : e.kind ≠ .exit) :
    VoteOk L (X.snoc g e r) := by
  refine Execution.voteOk_mono hX le_snoc (fun v pc k h hk => ?_) (fun v pc h => ?_)
  · rw [snoc_get] at h
    split_ifs at h
    · have hk' : e.kind = k := congrArg Event.kind (Option.some.inj h)
      rw [hk'] at hn
      rw [hn] at hk
      cases hk
    · exact h
  · rw [snoc_get] at h
    split_ifs at h
    · exact absurd (congrArg Event.kind (Option.some.inj h)) he
    · exact h

/-- Appending an event whose kind carries no lane value and is no exit keeps the constraints on
mode votes, reductions, matches and `activemask`. -/
theorem snoc_warpValueOk (hX : WarpValueOk L X) (hn : e.kind.laneValue = false)
    (he : e.kind ≠ .exit) : WarpValueOk L (X.snoc g e r) := by
  refine Execution.warpValueOk_mono hX le_snoc (fun v pc k h hk => ?_) (fun v pc h => ?_)
  · rw [snoc_get] at h
    split_ifs at h
    · have hk' : e.kind = k := congrArg Event.kind (Option.some.inj h)
      rw [hk'] at hn
      rw [hn] at hk
      cases hk
    · exact h
  · rw [snoc_get] at h
    split_ifs at h
    · exact absurd (congrArg Event.kind (Option.some.inj h)) he
    · exact h

theorem snoc_async : (X.snoc g e r).async = X.async := rfl

theorem snoc_objects : (X.snoc g e r).objects = X.objects := rfl

theorem Execution.NoTc.snoc (h : X.NoTc) (he : ∀ k, e.kind ≠ .tc k) : (X.snoc g e r).NoTc := by
  intro v pc k hv
  rw [snoc_get] at hv
  split_ifs at hv
  · exact he k (congrArg Event.kind (Option.some.inj hv))
  · exact h v pc k hv

theorem Execution.NoTma.snoc (h : X.NoTma) (he : e.kind.isTma = false) :
    (X.snoc g e r).NoTma := by
  intro v pc k hv
  rw [snoc_get] at hv
  split_ifs at hv
  · cases e; cases hv; exact he
  · exact h v pc k hv

theorem snoc_emptyAsync (h : Execution.NoTma.EmptyAsync X) :
    Execution.NoTma.EmptyAsync (X.snoc g e r) := h

theorem lsum_append (a b : List Nat) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, List.sum_cons, ih]; omega

theorem sum_range_bump (f : Nat → Nat) (g : Nat) : ∀ n,
    ((List.range n).map fun h => if h = g then f h + 1 else f h).sum =
      ((List.range n).map f).sum + if g < n then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, lsum_append, lsum_append,
      sum_range_bump f g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h : n = g
    · subst h; simp; omega
    · simp only [h, ↓reduceIte]
      by_cases hg : g < n
      · simp [hg, show g < n + 1 by omega]; omega
      · simp [hg, show ¬ g < n + 1 by omega]

/-- An old event of an appended execution keeps its asynchronous stages: `Execution.elemSize`
reads `X.get`, which `snoc` changes only at the appended index. -/
theorem asyncSize_snoc_of_lt {h i : Nat} (hi : i < (X.tr h).length) :
    (X.snoc g e r).asyncSize (h, i) = X.asyncSize (h, i) := by
  unfold Execution.asyncSize Execution.elemSize
  rw [snoc_get_old hi, snoc_async]
  rfl

/-- The appended event contributes no asynchronous stage of its own: no recorded copy stage and, by
consistency of the prefix, no recorded element stage. -/
theorem asyncSize_snoc_new (hz : X.asyncSize (g, (X.tr g).length) = 0)
    (helem : ∀ j, (X.async.copies (g, (X.tr g).length)).elemWrites j = none ∧
      (X.async.copies (g, (X.tr g).length)).elemOld j = none) :
    (X.snoc g e r).asyncSize (g, (X.tr g).length) = 0 := by
  have hw := fun j => (helem j).1
  have ho := fun j => (helem j).2
  have hel : (X.snoc g e r).elemSize (g, (X.tr g).length) = 0 := by
    unfold Execution.elemSize
    rw [snoc_async, snoc_get_new]
    split <;> simp [hw, ho]
  have hxel : X.elemSize (g, (X.tr g).length) = 0 := by
    have hi : X.get (g, (X.tr g).length) = none := List.getElem?_eq_none (Nat.le_refl _)
    unfold Execution.elemSize
    rw [hi]
  have hz' : X.asyncSize (g, (X.tr g).length) = 0 := hz
  unfold Execution.asyncSize at hz' ⊢
  rw [hxel, Nat.add_zero] at hz'
  rw [snoc_async, hel, Nat.add_zero]
  exact hz'

/-- Counting an appended instruction also exposes its independent stages, if any.
Consistency of the prefix rules those stages out before the instruction exists. -/
theorem size_snoc_of_no_effects (hg : g < L.threads) (hc : e.counts = true)
    (hz : X.asyncSize (g, (X.tr g).length) = 0)
    (helem : ∀ j, (X.async.copies (g, (X.tr g).length)).elemWrites j = none ∧
      (X.async.copies (g, (X.tr g).length)).elemOld j = none) :
    (X.snoc g e r).size L = X.size L + 1 := by
  unfold Execution.size Execution.threadSize
  have hmap : ∀ h, ((List.range (X.tr h).length).map
      fun i => (X.snoc g e r).asyncSize (h, i)) =
      ((List.range (X.tr h).length).map fun i => X.asyncSize (h, i)) := by
    intro h
    refine List.map_congr_left fun i hi => ?_
    exact asyncSize_snoc_of_lt (List.mem_range.mp hi)
  have hnew : (X.snoc g e r).asyncSize (g, (X.tr g).length) = 0 :=
    asyncSize_snoc_new hz helem
  have hf : (fun h => ((X.snoc g e r).tr h).countP Event.counts +
      ((List.range ((X.snoc g e r).tr h).length).map
        fun i => (X.snoc g e r).asyncSize (h, i)).sum) =
      fun h => if h = g then (X.tr h).countP Event.counts +
        ((List.range (X.tr h).length).map fun i => X.asyncSize (h, i)).sum + 1
      else (X.tr h).countP Event.counts +
        ((List.range (X.tr h).length).map fun i => X.asyncSize (h, i)).sum := by
    funext h
    by_cases hh : h = g
    · subst hh
      rw [snoc_tr]
      simp only [↓reduceIte, List.countP_append, List.countP_cons, hc, List.countP_nil,
        List.length_append, List.length_singleton, List.range_succ, List.map_append, hmap,
        List.map_cons, List.map_nil, lsum_append, List.sum_cons, List.sum_nil, hnew]
      omega
    · rw [ite_eq_right hh, snoc_tr, ite_eq_right hh, hmap]
  rw [hf, sum_range_bump, ite_eq_left hg]
  change _ + X.pairSize L = _
  omega

/-- A consistent execution records no element stage at an instruction it has not issued. -/
theorem Consistent.elem_empty_of_get_none {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {i : EvId} (hi : X.get i = none) :
    ∀ j, (X.async.copies i).elemWrites j = none ∧ (X.async.copies i).elemOld j = none := by
  have hn : ¬ AsyncCopy.nonempty (X.async.copies i) := by
    intro hp
    obtain ⟨s, hs, -⟩ := hX.tma.1 i hp
    unfold AsyncCopy.issuedBy at hs
    rw [hi] at hs
    cases hs
  intro j
  constructor
  · cases hw : (X.async.copies i).elemWrites j with
    | none => rfl
    | some bs => exact absurd ⟨.write (.elem j), by simp [AsyncCopy.present, hw]⟩ hn
  · cases ho : (X.async.copies i).elemOld j with
    | none => rfl
    | some bs => exact absurd ⟨.old (.elem j), by simp [AsyncCopy.present, ho]⟩ hn

/-- A consistent prefix has no effects belonging to its not-yet-issued next event. -/
theorem size_snoc {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) (hc : e.counts = true) :
    (X.snoc g e r).size L = X.size L + 1 := by
  have hi : X.get (g, (X.tr g).length) = none := List.getElem?_eq_none (Nat.le_refl _)
  exact size_snoc_of_no_effects hg hc (hX.absent_no_effects hi) (hX.elem_empty_of_get_none hi)


/-- Appending an event leaves program order into an old event unchanged. -/
theorem po_snoc_old {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    po (X.snoc g e r) a b ↔ po X a b := by
  unfold po
  rw [snoc_len]
  by_cases hs : a.1 = b.1
  · by_cases hlt : a.2 < b.2
    · have hsame := SameAccess.congr (X := X) (Y := X.snoc g e r) hs.symm hlt.le
        (fun x h1 _ hx => snoc_get_old (by rw [h1, hs]; omega))
      have : b.2 < (if b.1 = g then (X.tr g).length + 1 else (X.tr b.1).length) := by
        split_ifs with hh
        · rw [hh] at hbo; omega
        · exact hbo
      simp only [hs, hlt, true_and, hsame, this, hbo]
    · simp [hlt]
  · simp [hs]

/-- An event of the extension that is not the appended kind is an old event. -/
private theorem snoc_old_of_ne {v : EvId} {ev : Event} (h : (X.snoc g e r).get v = some ev)
    (hk : e ≠ ev) : v.2 < (X.tr v.1).length ∧ X.get v = some ev := by
  rw [snoc_get] at h
  split_ifs at h
  · exact (hk (Option.some.inj h)).elim
  · exact ⟨len_of_get h, h⟩

/-- Appending an event that is no `fence.sc` keeps the Fence-SC obligation, when causality into an
old event is causality of `X` (MEM-FENCE-SC): every morally strong pair of the extension is an old
pair, and the Fence-SC order is unchanged. -/
theorem FenceScOk.snoc (h : FenceScOk L X (baseCausality L X)) (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (hold : ∀ a b, b.2 < (X.tr b.1).length → baseCausality L (X.snoc g e r) a b →
      baseCausality L X a b) :
    FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)) := by
  have hfence : ∀ {v s}, (X.snoc g e r).ThreadFence v .sc s →
      v.2 < (X.tr v.1).length ∧ X.ThreadFence v .sc s := by
    rintro v s ⟨pc, hv⟩
    obtain ⟨hlt, hx⟩ := snoc_old_of_ne hv (fun he => hsc s (by rw [he]))
    exact ⟨hlt, pc, hx⟩
  have hstrong : ∀ {a b}, ScStrong L (X.snoc g e r) a b →
      b.2 < (X.tr b.1).length ∧ ScStrong L X a b := by
    rintro a b ⟨s, s', ha, hb, hscope⟩
    exact ⟨(hfence hb).1, s, s', (hfence ha).2, (hfence hb).2, hscope⟩
  refine ⟨fun a b hs hne => h.total a b (hstrong hs).2 hne, fun a ha => h.acyclic a ?_,
    fun a b hs hc => h.causal a b (hstrong hs).2 (hold a b (hstrong hs).1 hc)⟩
  exact Relation.TransGen.mono (fun x y hxy => ⟨(hstrong hxy.1).2, hxy.2⟩) _ _ ha

/-- Appending an event that is no warp-level matrix instruction keeps DEP-WARP-MATRIX: every matrix
event and every instance of the extension is one of `X`. -/
theorem MatrixOk.snoc {A : List Assumption} (h : MatrixOk L A X) (hm : isMatrix e = false) :
    MatrixOk L A (X.snoc g e r) := by
  have hold : ∀ {v ev}, (X.snoc g e r).get v = some ev → isMatrix ev = true →
      v.2 < (X.tr v.1).length ∧ X.get v = some ev := fun hv hev =>
    snoc_old_of_ne hv (by rintro rfl; rw [hm] at hev; cases hev)
  have hk : ∀ {v n}, (X.snoc g e r).MatrixK v n → X.MatrixK v n := by
    rintro v n ⟨⟨ev, hv, hev⟩, hc⟩
    obtain ⟨hlt, hx⟩ := hold hv hev
    exact ⟨⟨ev, hx, hev⟩, by rw [← snoc_take (g := g) (e := e) (r := r) hlt.le]; exact hc⟩
  intro g' i pc op own recv n hget hK parts hinst
  obtain ⟨-, hx⟩ := hold hget rfl
  refine h g' i pc op own recv n hx (hk hK) parts fun lane hl => ?_
  obtain ⟨j, rv, hj, hjk⟩ := hinst lane hl
  exact ⟨j, rv, (hold hj rfl).2, hk hjk⟩

/-- The instruction that issues an atomic operation. -/
def RmwId.issue : RmwId → EvId
  | .thread e | .tensor e _ _ | .copy e _ => e

/-- Moral strength of two atomic operations reads only the events that issue them. -/
theorem rmwStrong_congr {Y : Execution} {p q : RmwId} (hp : Y.get p.issue = X.get p.issue)
    (hq : Y.get q.issue = X.get q.issue) : RmwStrong L Y p q ↔ RmwStrong L X p q := by
  cases p <;> cases q <;>
    simp only [RmwId.issue] at hp hq <;>
    simp only [RmwStrong, RmwId.newRef, MorallyStrong, StrongScoped, AsyncCopy.Ref.Generic,
      GenericCopy, OpFootprint, Execution.Intent, Execution.Access, Execution.Reads,
      Execution.Writes, Execution.Rmw, Execution.AsyncFootprint, Execution.TensorStoreIssue,
      Execution.Copy, AsyncCopy.Ref.issuer, hp, hq]

/-- Appending an event that is no atomic read-modify-write keeps MEM-ATOMICITY: every atomic
operation of the extension is an operation of `X` issued by an old event, with the same old-value
sources and the same moral strength. -/
theorem AtomicOk.snoc (h : AtomicOk L X) (hS : TensorStoreOk L X)
    (hw : AsyncCopy.WellFormed (AsyncCopy.issuedBy X) X.async)
    (hn : ∀ a old new, e.kind ≠ .rmw a old new) : AtomicOk L (X.snoc g e r) := by
  have hat : ∀ {p l n}, (X.snoc g e r).RmwAt p l n →
      p.issue.2 < (X.tr p.issue.1).length ∧ X.RmwAt p l n := by
    intro p l n hp
    cases p with
    | thread v =>
      obtain ⟨a, old, new, ⟨pc, hv⟩, hl, hs⟩ := hp
      obtain ⟨hlt, hx⟩ := snoc_old_of_ne hv (fun he => hn a old new (by rw [he]))
      exact ⟨hlt, a, old, new, ⟨pc, hx⟩, hl, hs⟩
    | tensor i x y =>
      obtain ⟨fp, hred, hl, hs⟩ := hp
      obtain ⟨o, -, -, ho, -⟩ := id hred
      obtain ⟨⟨addr, pc, hi⟩, -⟩ := hS i o ho
      exact ⟨len_of_get hi, fp, hred, hl, hs⟩
    | copy i j =>
      obtain ⟨s, rd, a, ⟨pc, hc⟩, hwr, hel, hsome, hl, hs⟩ := hp
      obtain ⟨s', hs', -⟩ := hw i ⟨.write (.elem j), hsome⟩
      have hlt : i.2 < (X.tr i.1).length := by
        unfold AsyncCopy.issuedBy at hs'
        split at hs'
        · exact len_of_get (by assumption)
        · cases hs'
      exact ⟨hlt, s, rd, a, ⟨pc, by rwa [snoc_get_old hlt] at hc⟩, hwr, hel, hsome, hl, hs⟩
  have hrf : ∀ {p l n}, (X.snoc g e r).RmwAt p l n → ∀ k,
      (X.snoc g e r).oldRf p k = X.oldRf p k := by
    intro p l n hp k
    have hlt := (hat hp).1
    cases p with
    | thread v =>
      simp only [Execution.oldRf, Execution.snoc, RmwId.issue] at hlt ⊢
      refine ite_eq_right_iff.mpr fun hv => ?_
      cases hv
      simp at hlt
    | tensor i x y => simp [Execution.oldRf, Execution.snoc]
    | copy i j => simp [Execution.oldRf, Execution.snoc]
  have hst : ∀ {p q l n l' n'}, (X.snoc g e r).RmwAt p l n → (X.snoc g e r).RmwAt q l' n' →
      (RmwStrong L (X.snoc g e r) p q ↔ RmwStrong L X p q) := fun hp hq =>
    rmwStrong_congr (snoc_get_old (hat hp).1) (snoc_get_old (hat hq).1)
  refine ⟨fun p q l n k hp hq hne hs hk => ?_, fun p hc => h.acyclic p ?_⟩
  · rw [hrf hp, hrf hq]
    exact h.unique p q l n k (hat hp).2 (hat hq).2 hne ((hst hp hq).mp hs) hk
  · refine Relation.TransGen.mono (fun a b hab => ?_) _ _ hc
    obtain ⟨l, n, ha, hb, hs, k, k', hk, hr⟩ := hab
    exact ⟨l, n, (hat ha).2, (hat hb).2, (hst ha hb).mp hs, k, k', hk, by rwa [← hrf hb]⟩

end
end
end PTX
