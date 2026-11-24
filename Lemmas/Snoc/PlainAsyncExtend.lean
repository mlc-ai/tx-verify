-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocReady
public import Lemmas.Snoc.SnocPlainWaiting
public import Lemmas.Snoc.SnocMemory
public import Lemmas.Snoc.Collectives
public import Lemmas.Flow.Determinism

@[expose] public section

/-! Appending an ordinary instruction retains all async effects and object histories.
A new read, or the old-value read of a new atomic, reads from ordinary writes, from actual
asynchronous writes or from the launch memory (`NewRead`). -/
namespace PTX
open AsyncCopy
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- Read-source obligations for a read of a newly appended event: a read or the old-value read of
an atomic read-modify-write. -/
structure NewRead (L : Launch) (mem0 : Mem0) (X : Execution) (g : Nat) (e : Event)
    (r : Nat → Option Ref) (a : Acc) (bs : List (Option Byte)) : Prop where
  len : bs.length = a.size
  src : ∀ k < a.size,
    match r k with
    | none => ∀ c, mem0 (a.loc.at k) = some c → bs[k]? = some (X.initialByte c (a.loc.at k))
    | some w => ∃ a' bs', X.MemWrites w a' bs' ∧ a'.Covers (a.loc.at k) ∧
        bs[k]? = some (wbyte a' bs' (a.loc.at k))
  hidden : ∀ k w a' bs', k < a.size → X.MemWrites w a' bs' → a'.Covers (a.loc.at k) →
    ByteCausality L (X.snoc g e r) (a.loc.at k) w (.thread (g, (X.tr g).length)) →
    match r k with
    | none => False
    | some w' => ¬ ByteCausality L X (a.loc.at k) w' w

/-- A new read reads every byte from a write of `X`, hence not from itself. -/
theorem NewRead.self {mem0 : Mem0} {a : Acc} {bs : List (Option Byte)}
    (h : NewRead L mem0 X g e r a bs) {k : Nat} (hk : k < a.size) :
    r k ≠ some (.thread (g, (X.tr g).length)) := by
  intro hr
  have hs := h.src k hk
  rw [hr] at hs
  obtain ⟨a', bs', hw, -⟩ := hs
  have hl := memWrites_thread_lt hw
  simp at hl

/-- The appended event reads from no write of its own when its reads have their sources in `X`. -/
theorem SnocReadsSelf.of_newRead {mem0 : Mem0}
    (hrd : ∀ a bs, (X.snoc g e r).MemReads (.thread (g, (X.tr g).length)) a bs →
      NewRead L mem0 X g e r a bs) : SnocReadsSelf X g e r :=
  fun b cs h hz => (hrd b cs h).self hz

/-- An appended event of the fragment without mbarrier, copy or tensor-core instructions returns
at once: it is no collective, so it has not returned when it is the last event. -/
theorem not_returned_new_of_plain (hk : e.kind.isTma = false)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) :
    ¬ Returned (X.snoc g e r) (X.newId g) := by
  unfold Returned
  rw [snoc_get_new]
  obtain ⟨pc, k⟩ := e
  cases k
  case shfl => exact (hns _ _ _ _ _ _ rfl).elim
  all_goals simp_all [Kind.isTma, Kind.resume]

/-- **Appending an instruction outside the mbarrier, copy and tensor-core fragment**: no barrier
or shuffle, and no releasing atomic; an exit included. The thread's previous last event must be
ready (`LastReady`), every read of the appended event has its sources in `X` (`NewRead`), and
the obligations of the event on the execution metadata are given (`ExtensionObligations`, for an
exit `ExtensionObligations.snoc_exit`). -/
theorem consistent_snoc_plain {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hk : e.kind.isTma = false)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hrel : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    (hlast : LastReady L X g)
    (hrd : ∀ a bs, (X.snoc g e r).MemReads (.thread (g, (X.tr g).length)) a bs →
      NewRead L mem0 X g e r a bs)
    (hextra : ExtensionObligations L A (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) := by
  have hold : SnocReadsOld X g e r := .of_rfWf hX.rf
  have hself : SnocReadsSelf X g e r := .of_newRead hrd
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f) :=
    baseCausality_snoc_old hX.cluster hold hnb hk
  have htma : TmaOk (X.snoc g e r) := tmaOk_snoc_plain hX.tma hk
  have hvo : ∀ {v w : Ref} {l : Loc}, X.RefPresent w →
      (modelCausality L (X.snoc g e r) l v w ↔ modelCausality L X l v w) := by
    intro v w l hw
    exact modelCausality_snoc_old hk hbo (snoc_allocResultBefore_old hX.dependency.ready)
      (refPresent_issuer_lt hX.effectValidity hw)
  have reflect {v w : Ref} {l : Loc} (hw : X.RefPresent w)
      (h : ByteCausality L (X.snoc g e r) l v w) : ByteCausality L X l v w :=
    ByteCausality.le_reflect_present le_snoc hX.effectValidity (fun hk => (hvo hk).mp)
      (observesMma_of_prefix le_snoc hX.effectValidity htma.2.2.1) hw h
  have rfNew : ∀ k, (X.snoc g e r).rf (.thread (g, (X.tr g).length)) k = r k :=
    fun _ => ite_eq_left rfl
  have rfOld : ∀ {v : Ref} {k : Nat}, v ≠ .thread (g, (X.tr g).length) →
      (X.snoc g e r).rf v k = X.rf v k := fun hv => ite_eq_right hv
  have hmat : isMatrix e = false := by
    obtain ⟨pc, k⟩ := e
    cases k <;> simp_all [Kind.isTma, isMatrix]
  have hlv : e.kind.laneValue = false := by
    cases h : e.kind <;> simp only [Kind.laneValue] <;> simp_all [Kind.isTma]
  have horder : OrderOk L K A (X.snoc g e r) := by
    by_cases hx : e.kind = .exit
    · exact snoc_exit_orderOk hX hx (no_exit_of_run hrun)
    · exact snoc_plain_orderOk (g := g) (r := r) hX (.of_plain hk) hns hx hlv hmat
        (fun m tx count sc he' => by rw [he'] at hk; cases hk) hrel
  have hready := ready_snocHistory (records := X.objects) (e := e) (r := r) hX SnocRecords.same
    (fun h => by rw [hmat] at h; cases h) hlast
    (fun h => (not_returned_new_of_plain hk hnb hns h).elim)
  refine {
    thr := ?_, outside := ?_, rf := ?_, ctaBar := hextra.ctaBar, cluster := hextra.cluster,
    dependency := ⟨hready, horder.depAcyclic⟩, shfl := snoc_shflOk hX.shfl hns, vote := hextra.vote,
    warpValue := hextra.warpValue, matrix := hextra.matrix, elect := hextra.elect,
    warpBar := hextra.warpBar, observation := horder.observation, object := horder.object,
    asyncObject := horder.asyncObject, initFence := horder.initFence,
    noFuture := ?_, hidden := ?_, tma := htma, clc := hextra.clc,
    tensor := hextra.tensor, store := hextra.store, reduce := hextra.reduce,
    atomic := hextra.atomic, fenceSc := hextra.fenceSc,
    tmemPair := hextra.tmemPair, tmemPairCompletion := hextra.tmemPairCompletion,
    tmemPairResult := hextra.tmemPairResult, tcCommit := hextra.tcCommit,
    mmaCompletion := hextra.mmaCompletion, tcRead := hextra.tcRead, asm := hasm }
  · intro h hh
    by_cases hhg : h = g
    · subst hhg
      refine ⟨o, ?_⟩
      rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he
    · rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh
  · intro h hh
    rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh
  · intro v a bs hv
    by_cases hn : v = .thread (g, (X.tr g).length)
    · subst v
      have nr := hrd a bs hv
      refine ⟨nr.len, fun k hk' => ?_⟩
      rw [rfNew]
      have hs := nr.src k hk'
      cases hrf : r k with
      | none => simp only [hrf] at hs ⊢; exact hs
      | some w =>
        rw [hrf] at hs
        obtain ⟨a', bytes, hw, hc, hb⟩ := hs
        exact ⟨a', bytes, snoc_memWrites_lift hk hw, hc, hb⟩
    · have hvX := (snoc_memReads_old hk hn).mp hv
      obtain ⟨hlen, hs⟩ := hX.rf v a bs hvX
      refine ⟨hlen, fun k hk' => ?_⟩
      rw [rfOld hn]
      have hsrc := hs k hk'
      cases hrf : X.rf v k with
      | none => simp only [hrf] at hsrc ⊢; exact hsrc
      | some w =>
        rw [hrf] at hsrc
        obtain ⟨a', bytes, hw, hc, hb⟩ := hsrc
        exact ⟨a', bytes, snoc_memWrites_lift hk hw, hc, hb⟩
  · intro v a bs k w hv hk' hrk hvw
    by_cases hn : v = .thread (g, (X.tr g).length)
    · subst v
      obtain ⟨_, first⟩ := hvw.starts
      exact snoc_no_modelCausality_from_new hk hold hself hX.dependency.ready first
    · have hvX := (snoc_memReads_old hk hn).mp hv
      rw [rfOld hn] at hrk
      have hs := (hX.rf v a bs hvX).2 k hk'
      rw [hrk] at hs
      obtain ⟨a', bytes, hw, _⟩ := hs
      exact hX.noFuture v a bs k w hvX hk' hrk (reflect hw.present hvw)
  · intro v a bs k w a' bytes hv hk' hw hc hwv
    have hwn : w ≠ .thread (g, (X.tr g).length) := by
      rintro rfl
      obtain ⟨_, first⟩ := hwv.starts
      exact snoc_no_modelCausality_from_new hk hold hself hX.dependency.ready first
    have hwX := (snoc_memWrites_old hk hwn).mp hw
    by_cases hn : v = .thread (g, (X.tr g).length)
    · subst v
      rw [rfNew]
      have hh := (hrd a bs hv).hidden k w a' bytes hk' hwX hc hwv
      cases hs : r k with
      | none => simp [hs] at hh
      | some w' =>
        rw [hs] at hh
        exact fun h => hh (reflect hwX.present h)
    · have hvX := (snoc_memReads_old hk hn).mp hv
      have hh := hX.hidden v a bs k w a' bytes hvX hk' hwX hc (reflect hvX.present hwv)
      rw [rfOld hn]
      cases hs : X.rf v k with
      | none => simp [hs] at hh
      | some w' =>
        rw [hs] at hh
        exact fun h => hh (reflect hwX.present h)

end
end
end PTX
