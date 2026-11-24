-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Order.Order
public import Core.Assembly.Correctness
public import Lemmas.Async.AsyncOrder
public import Lemmas.Order.ByteCausalityAcyclic
public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

/-!
# Extending executions with collective events

A barrier arrival or a completed shuffle adds no ordinary memory access. Once the conflicts at the
bytes that are read are ordered in the existing execution (`ReadsOrdered`, implied by its safety),
its memory constraints survive an extension that preserves existing causality, adds none
between two writes of the same value (`SameValueWrites`), which `ReadsOrdered` leaves
unordered, and has acyclic waiting dependencies. The caller proves the new thread traces, waiting
rules, collective values and assumption conditions. -/

namespace PTX

/-- The obligations of `Consistent` other than the traces, the reads-from well-formedness, the read
axioms, the order obligations (`OrderOk`), the readiness of DEP-ORDER, the shuffles, `TmaOk` and the
assumptions, which the transport lemmas take separately. -/
structure ExtensionObligations (L : Launch) (A : List Assumption) (Y : Execution) : Prop where
  ctaBar : CtaBarHistoryOk L Y
  cluster : ClusterHistoryOk L Y
  elect : ElectOk L Y
  vote : VoteOk L Y
  warpValue : VoteModeOk L Y ∧ ReduxOk L Y ∧ MatchOk L Y ∧ ActiveMaskOk L Y
  warpBar : WarpBarOk L Y
  matrix : MatrixOk L A Y
  clc : ClcOk L Y
  tensor : TensorOk L Y
  store : TensorStoreOk L Y
  atomic : AtomicOk L Y
  fenceSc : FenceScOk L Y (baseCausality L Y)
  tmemPair : Tmem.Pair.HistoriesOk L Y
  tmemPairResult : Tmem.Pair.ResultOk L Y
  tmemPairCompletion : Tmem.Pair.CompletionClosed L Y
  tcCommit : AsyncCopy.CommitOk Y
  mmaCompletion : TcMma.CompletionClosed L Y
  tcRead : TcMma.ReadOk L A Y
  reduce : TensorStore.ReduceOk A Y

theorem ExtensionObligations.effectValidity {L : Launch} {A : List Assumption} {Y : Execution}
    (h : ExtensionObligations L A Y) (ht : TmaOk Y) : EffectValidity L Y :=
  ⟨ht, h.tensor, h.store, h.clc, h.tmemPair, h.tcCommit⟩

/-- The guard obligations of an extension: the readiness of DEP-ORDER and the barrier facts of its
obligations. -/
theorem ExtensionObligations.guardOk {L : Launch} {A : List Assumption} {Y : Execution}
    (h : ExtensionObligations L A Y) (hready : ∀ e, Returned Y e → Ready L Y e) : GuardOk L Y :=
  ⟨hready, h.ctaBar, h.cluster, h.warpBar⟩

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X Y : Execution}

/-- When a non-memory extension preserves visibility between its old present nodes,
all memory axioms transport directly. This does not need an already-proved safety theorem. -/
theorem consistent_preserving_present_extension
    (hX : Consistent L K A mem0 X) (hle : X.le Y)
    (hthr : ∀ g < L.threads, Produces K A L g (Y.tr g))
    (houtside : ∀ g, L.threads ≤ g → Y.tr g = [])
    (hread : ∀ e a bs, Y.MemReads e a bs → X.MemReads e a bs)
    (hwrite : ∀ e a bs, Y.MemWrites e a bs → X.MemWrites e a bs)
    (hlift : ∀ e a bs, X.MemWrites e a bs → Y.MemWrites e a bs)
    (hrf : ∀ e a bs, Y.MemReads e a bs → ∀ k, Y.rf e k = X.rf e k)
    (hvis : ∀ l e f, X.RefPresent e → X.RefPresent f →
      (modelCausality L Y l e f ↔ modelCausality L X l e f))
    (hready : ∀ e, Returned Y e → Ready L Y e) (hshfl : ShflOk L Y)
    (horder : OrderOk L K A Y)
    (hasm : ∀ a ∈ A, a.wf L mem0 Y) (htma : TmaOk Y)
    (hinit : Y.initial = X.initial) (hextra : ExtensionObligations L A Y) :
    Consistent L K A mem0 Y := by
  have reflect {l e f} (he : X.RefPresent e) (hf : X.RefPresent f) (h : ByteCausality L Y l e f) :
      ByteCausality L X l e f :=
    ByteCausality.le_reflect_from_present hle hX.effectValidity
      (fun {l f} h => (hvis l e f he h).mp)
      (observesMma_of_prefix hle hX.effectValidity htma.2.2.1) hf h
  refine {
    thr := hthr, outside := houtside, rf := ?_, ctaBar := hextra.ctaBar,
    cluster := hextra.cluster, dependency := ⟨hready, horder.depAcyclic⟩, shfl := hshfl,
    vote := hextra.vote, warpValue := hextra.warpValue, matrix := hextra.matrix,
    elect := hextra.elect, warpBar := hextra.warpBar, observation := horder.observation,
    object := horder.object, asyncObject := horder.asyncObject, initFence := horder.initFence,
    noFuture := ?_, hidden := ?_, tma := htma, clc := hextra.clc,
    tensor := hextra.tensor, store := hextra.store, reduce := hextra.reduce,
    atomic := hextra.atomic, fenceSc := hextra.fenceSc,
    tmemPair := hextra.tmemPair, tmemPairCompletion := hextra.tmemPairCompletion,
    tmemPairResult := hextra.tmemPairResult, tcCommit := hextra.tcCommit,
    mmaCompletion := hextra.mmaCompletion, tcRead := hextra.tcRead, asm := hasm }
  · intro e a bs he
    obtain ⟨hlen, hs⟩ := hX.rf e a bs (hread _ _ _ he)
    refine ⟨hlen, fun k hk => ?_⟩
    rw [hrf _ _ _ he k]
    have hh := hs k hk
    cases h : X.rf e k with
    | none => simpa [h, Execution.initialByte, hinit] using hh
    | some w =>
      rw [h] at hh
      obtain ⟨a', bs', hw, hc, hv⟩ := hh
      exact ⟨a', bs', hlift _ _ _ hw, hc, hv⟩
  · intro e a bs k w he hk hs hew
    have heX := hread _ _ _ he
    rw [hrf _ _ _ he k] at hs
    have hw := (hX.rf e a bs heX).2 k hk
    rw [hs] at hw
    obtain ⟨dst, bytes, hw, _⟩ := hw
    exact hX.noFuture e a bs k w heX hk hs (reflect heX.present hw.present hew)
  · intro e a bs k w a' bs' he hk hw hc hwe
    have heX := hread _ _ _ he
    have hwX := hwrite _ _ _ hw
    have hh := hX.hidden e a bs k w a' bs' heX hk hwX hc
      (reflect hwX.present heX.present hwe)
    rw [hrf _ _ _ he k]
    cases hs : X.rf e k with
    | none => simp [hs] at hh
    | some w' =>
      rw [hs] at hh
      have hSource := (hX.rf e a bs heX).2 k hk
      rw [hs] at hSource
      obtain ⟨_,_,hSrc,_,_⟩ := hSource
      exact fun h => hh (reflect hSrc.present hwX.present h)


/-- When a non-memory extension preserves visibility into every old present node,
all memory axioms transport directly. This does not need an already-proved safety theorem. -/
theorem consistent_preserving_extension
    (hX : Consistent L K A mem0 X) (hle : X.le Y)
    (hthr : ∀ g < L.threads, Produces K A L g (Y.tr g))
    (houtside : ∀ g, L.threads ≤ g → Y.tr g = [])
    (hread : ∀ e a bs, Y.MemReads e a bs → X.MemReads e a bs)
    (hwrite : ∀ e a bs, Y.MemWrites e a bs → X.MemWrites e a bs)
    (hlift : ∀ e a bs, X.MemWrites e a bs → Y.MemWrites e a bs)
    (hrf : ∀ e a bs, Y.MemReads e a bs → ∀ k, Y.rf e k = X.rf e k)
    (hvis : ∀ l e f, X.RefPresent f → (modelCausality L Y l e f ↔ modelCausality L X l e f))
    (hready : ∀ e, Returned Y e → Ready L Y e) (hshfl : ShflOk L Y)
    (horder : OrderOk L K A Y)
    (hasm : ∀ a ∈ A, a.wf L mem0 Y) (htma : TmaOk Y)
    (hinit : Y.initial = X.initial) (hextra : ExtensionObligations L A Y) :
    Consistent L K A mem0 Y :=
  consistent_preserving_present_extension hX hle hthr houtside hread hwrite hlift hrf
    (fun loc e f _ hf => hvis loc e f hf) hready hshfl horder hasm htma hinit hextra

/-- **The memory constraints survive an extension that grows visibility**, when the conflicts at
the bytes that are read are ordered and the extension orders no two old same-value writes that
`X` leaves unordered (`hsame`). -/
theorem consistent_collective_extension_reads
    (hX : Consistent L K A mem0 X) (hle : X.le Y) (hord : ReadsOrdered L X)
    (hthr : ∀ g < L.threads, Produces K A L g (Y.tr g))
    (houtside : ∀ g, L.threads ≤ g → Y.tr g = [])
    (hread : ∀ e a bs, Y.MemReads e a bs → X.MemReads e a bs)
    (hwrite : ∀ e a bs, Y.MemWrites e a bs → X.MemWrites e a bs)
    (hlift : ∀ e a bs, X.MemWrites e a bs → Y.MemWrites e a bs)
    (hrf : ∀ e a bs, Y.MemReads e a bs → ∀ k, Y.rf e k = X.rf e k)
    (hmono : ∀ l e f, modelCausality L X l e f → modelCausality L Y l e f)
    (hsame : ∀ l e f a b, SameValueWrites X e f a b → X.RefPresent e → X.RefPresent f →
      ByteCausality L Y l e f → ByteCausality L X l e f)
    (hready : ∀ e, Returned Y e → Ready L Y e) (hshfl : ShflOk L Y)
    (horder : OrderOk L K A Y) (hg : SyncGuarded L K Y)
    (hasm : ∀ a ∈ A, a.wf L mem0 Y) (htma : TmaOk Y)
    (hinit : Y.initial = X.initial) (hextra : ExtensionObligations L A Y) :
    Consistent L K A mem0 Y := by
  have mono {l e f} (h : ByteCausality L X l e f) : ByteCausality L Y l e f :=
    h.le_mono hle (fun {l e f} => hmono l e f)
  have hvis {l e f} (h : ByteCausality L Y l e f) (h' : ByteCausality L Y l f e) : False :=
    ByteCausality.acyclic (hextra.effectValidity htma) horder.object
      (DepStepAcyclic.of_dependency ⟨hready, horder.depAcyclic⟩) hg (hextra.guardOk hready)
      l e ((Relation.TransGen.single h).tail h')
  -- two conflicting accesses of a byte that is read, ordered in `Y`, are ordered so in `X`
  have back : ∀ e a bs k x y ax ay, X.MemReads e a bs → k < a.size → Conflict X x y ax ay →
      ax.Covers (a.loc.at k) → ay.Covers (a.loc.at k) → X.RefPresent x → X.RefPresent y →
      ByteCausality L Y (a.loc.at k) x y → ByteCausality L X (a.loc.at k) x y := by
    intro e a bs k x y ax ay he hk hc hcx hcy hx hy h
    by_cases hsv : SameValueWrites X x y ax ay
    · exact hsame _ _ _ _ _ hsv hx hy h
    rcases hord e a bs k he hk x y ax ay hc hsv hcx hcy with h' | h'
    · exact h'
    · exact (hvis h (mono h')).elim
  have oldBefore : ∀ e a bs k w a' bs', Y.MemReads e a bs → k < a.size → Y.MemWrites w a' bs' →
      a'.Covers (a.loc.at k) → ByteCausality L Y (a.loc.at k) w e → ByteCausality L X
          (a.loc.at k) w e := by
    intro e a bs k w a' bs' he hk hw hc hwe
    have heX := hread _ _ _ he
    have hwX := hwrite _ _ _ hw
    by_cases hne : w = e
    · subst hne
      exact (hvis hwe hwe).elim
    exact back e a bs k w e a' a heX hk
      ⟨hne, true, false, hwX.intent, heX.intent, .inl rfl, ⟨a.loc.at k, hc, Acc.covers_at hk⟩⟩
      hc (Acc.covers_at hk) hwX.present heX.present hwe
  refine {
    thr := hthr, outside := houtside, rf := ?_, ctaBar := hextra.ctaBar,
    cluster := hextra.cluster, dependency := ⟨hready, horder.depAcyclic⟩, shfl := hshfl,
    vote := hextra.vote, warpValue := hextra.warpValue, matrix := hextra.matrix,
    elect := hextra.elect, warpBar := hextra.warpBar, observation := horder.observation,
    object := horder.object, asyncObject := horder.asyncObject, initFence := horder.initFence,
    noFuture := ?_, hidden := ?_, tma := htma, clc := hextra.clc,
    tensor := hextra.tensor, store := hextra.store, reduce := hextra.reduce,
    atomic := hextra.atomic, fenceSc := hextra.fenceSc,
    tmemPair := hextra.tmemPair, tmemPairCompletion := hextra.tmemPairCompletion,
    tmemPairResult := hextra.tmemPairResult, tcCommit := hextra.tcCommit,
    mmaCompletion := hextra.mmaCompletion, tcRead := hextra.tcRead, asm := hasm }
  · intro e a bs he
    obtain ⟨hlen, hs⟩ := hX.rf e a bs (hread _ _ _ he)
    refine ⟨hlen, fun k hk => ?_⟩
    rw [hrf _ _ _ he k]
    have hh := hs k hk
    cases h : X.rf e k with
    | none => simpa [h, Execution.initialByte, hinit] using hh
    | some w =>
      rw [h] at hh
      obtain ⟨a', bs', hw, hc, hv⟩ := hh
      exact ⟨a', bs', hlift _ _ _ hw, hc, hv⟩
  · intro e a bs k w he hk hs hew
    have heX := hread _ _ _ he
    rw [hrf _ _ _ he k] at hs
    have hw := (hX.rf e a bs heX).2 k hk
    rw [hs] at hw
    obtain ⟨a', bs', hwX, hc, -⟩ := hw
    by_cases hne : e = w
    · subst hne
      exact hvis hew hew
    exact hX.noFuture e a bs k w heX hk hs (back e a bs k e w a a' heX hk
      ⟨hne, false, true, heX.intent, hwX.intent, .inr rfl, ⟨a.loc.at k, Acc.covers_at hk, hc⟩⟩
      (Acc.covers_at hk) hc heX.present hwX.present hew)
  · intro e a bs k w a' bs' he hk hw hc hwe
    have heX := hread _ _ _ he
    have hwX := hwrite _ _ _ hw
    have hweX := oldBefore e a bs k w a' bs' he hk hw hc hwe
    have hh := hX.hidden e a bs k w a' bs' heX hk hwX hc hweX
    rw [hrf _ _ _ he k]
    cases hs : X.rf e k with
    | none => rwa [hs] at hh
    | some w' =>
      rw [hs] at hh
      have hw' := (hX.rf e a bs heX).2 k hk
      rw [hs] at hw'
      obtain ⟨a'', bs'', hw'X, hc', -⟩ := hw'
      intro hback
      by_cases hne : w = w'
      · subst hne
        exact hvis hback hback
      exact hh (back e a bs k w' w a'' a' heX hk
        ⟨fun h => hne h.symm, true, true, hw'X.intent, hwX.intent, .inl rfl,
          ⟨a.loc.at k, hc', hc⟩⟩ hc' hc hw'X.present hwX.present hback)

/-- The memory constraints survive an extension that grows visibility, in a safe execution. -/
theorem consistent_collective_extension
    (hX : Consistent L K A mem0 X) (hle : X.le Y) (hm : ¬ Mixed L X) (hr : ¬ Race L X)
    (hst : StrongOrdered L X)
    (hthr : ∀ g < L.threads, Produces K A L g (Y.tr g))
    (houtside : ∀ g, L.threads ≤ g → Y.tr g = [])
    (hread : ∀ e a bs, Y.MemReads e a bs → X.MemReads e a bs)
    (hwrite : ∀ e a bs, Y.MemWrites e a bs → X.MemWrites e a bs)
    (hlift : ∀ e a bs, X.MemWrites e a bs → Y.MemWrites e a bs)
    (hrf : ∀ e a bs, Y.MemReads e a bs → ∀ k, Y.rf e k = X.rf e k)
    (hmono : ∀ l e f, modelCausality L X l e f → modelCausality L Y l e f)
    (hsame : ∀ l e f a b, SameValueWrites X e f a b → X.RefPresent e → X.RefPresent f →
      ByteCausality L Y l e f → ByteCausality L X l e f)
    (hready : ∀ e, Returned Y e → Ready L Y e) (hshfl : ShflOk L Y)
    (horder : OrderOk L K A Y) (hg : SyncGuarded L K Y)
    (hasm : ∀ a ∈ A, a.wf L mem0 Y) (htma : TmaOk Y)
    (hinit : Y.initial = X.initial) (hextra : ExtensionObligations L A Y) :
    Consistent L K A mem0 Y :=
  consistent_collective_extension_reads hX hle (.of_safe hm hr hst) hthr houtside hread hwrite
    hlift hrf hmono hsame hready hshfl horder hg hasm htma hinit hextra

end
end PTX
