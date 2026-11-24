-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Snoc.SnocWaitFrame
public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! # Appending a read

A proof tool. A thread whose last event is released can read memory, possibly with acquire
semantics: given a source for each byte of the read (`NewRead`: an existing write covering the
byte, or the launch content, not hidden behind another write the read sees), the execution with
the read appended is consistent and counts one more event (`read_counted_extension`). The read
issues no asynchronous operation and adds synchronization only into itself, so visibility into
older events and the waiting graph out of them are unchanged; its other obligations are those of
a plain event (`ExtensionObligations.snoc_plain`). -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0} {g : Nat}
  {r : Nat → Option Ref} {a : Acc} {bs : List (Option Byte)}

/-- **A released thread reads memory**, given a source for each byte of the read: a counted
extension. -/
theorem read_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hrel : Released L X g) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {pc : Nat} (he : EStep K A L g t1 ⟨pc, .rd a bs⟩ o)
    (hread : NewRead L mem0 X g ⟨pc, .rd a bs⟩ r a bs)
    (hasm : ∀ a' ∈ A, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let ev : Event := ⟨pc, .rd a bs⟩
  have hs : ev.kind.AsyncSilent := trivial
  have htc : ∀ k, ev.kind ≠ .tc k := fun _ h => Kind.noConfusion h
  have hw : ev.kind.WaitFree := ⟨trivial, htc⟩
  have hnb : ∀ id count mode, ev.kind ≠ .bar id count mode := fun _ _ _ h => Kind.noConfusion h
  have hns : ∀ m a b c recv ok, ev.kind ≠ .shfl m a b c recv ok :=
    fun _ _ _ _ _ _ h => Kind.noConfusion h
  have hnw : ∀ a bs, ev.kind ≠ .wr a bs := fun _ _ h => Kind.noConfusion h
  have hrmw : ∀ a old new, ev.kind ≠ .rmw a old new := fun _ _ _ h => Kind.noConfusion h
  have hrmw' : ∀ a old new, ev.kind = .rmw a old new → a.release = false :=
    fun a old new h => absurd h (hrmw a old new)
  have hna : ∀ m tx count sc, ev.kind ≠ .arrive m tx count true sc :=
    fun _ _ _ _ h => Kind.noConfusion h
  have hsc : ∀ s, ev.kind ≠ .fence .sc s := fun _ h => Kind.noConfusion h
  have hmat : isMatrix ev = false := rfl
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ev r) x f ↔ baseCausality L X x f) :=
    baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf)
      (fun _ _ h => Kind.noConfusion h) hnb hna hsc
  have htma : TmaOk (X.snoc g ev r) :=
    hX.tmaOk_snoc_unobserved htc fun _ => by simp [objectAction, snoc_get_new, ev]
  have hvo : ∀ {v w : Ref} {l : Loc}, X.RefPresent w →
      (modelCausality L (X.snoc g ev r) l v w ↔ modelCausality L X l v w) := fun hw =>
    hs.modelCausality_snoc_old hbo (snoc_allocResultBefore_old_of_not_write hnw)
      (refPresent_issuer_lt hX.effectValidity hw)
  have hwrite {v : Ref} {a' : Acc} {bs' : List Byte} :
      (X.snoc g ev r).MemWrites v a' bs' ↔ X.MemWrites v a' bs' :=
    snoc_memWrites_control hX.effectValidity hnw hrmw
  have oldRead {v : Ref} (hn : v ≠ .thread (g, (X.tr g).length)) {a' : Acc}
      {bs' : List (Option Byte)} : (X.snoc g ev r).MemReads v a' bs' ↔ X.MemReads v a' bs' := by
    cases v with
    | thread i =>
      simp only [Execution.MemReads, Execution.Reads, Execution.Rmw, snoc_get,
        ite_eq_right (fun h => hn (congrArg Ref.thread h))]
    | async i p => exact hs.snoc_memReads_async
  have noBase {f : EvId} : ¬ baseCausality L (X.snoc g ev r) (g, (X.tr g).length) f :=
    snoc_no_baseCausality_from_new_of_not_arrive hna (fun _ _ h => absurd h (hnw _ _)) hrmw' hsc
  have noFromNew {f : Ref} {l : Loc} :
      ¬ modelCausality L (X.snoc g ev r) l (.thread (g, (X.tr g).length)) f := by
    intro hv
    cases f with
    | thread i =>
      rcases hv with hb | ha
      · exact noBase hb
      · obtain ⟨_, _, _, _, hresult, _, _, _, _⟩ := ha
        obtain ⟨_, _, hstore⟩ := hresult.writes
        rw [snoc_get_new] at hstore
        exact hnw _ _ (congrArg Event.kind (Option.some.inj hstore))
    | async i p =>
      rcases hv.2 with ⟨_, _, -, -, -, -, -, hb, -⟩ | ⟨-, hb⟩ <;> exact noBase hb
  have hextra : ExtensionObligations L A (X.snoc g ev r) :=
    ExtensionObligations.snoc_plain hX trivial (.inl hne) (fun h => Kind.noConfusion h) hrmw hmat
      (fun _ h => Kind.noConfusion h)
      (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => hnw _ _ (congrArg Event.kind h))
  have horder : OrderOk L K A (X.snoc g ev r) :=
    snoc_plain_orderOk hX hw hns (fun h => Kind.noConfusion h) rfl hmat hna hrmw'
  have hready := ready_snocHistory (records := X.objects) (e := ev) (r := r) hX SnocRecords.same
    (fun h => by rw [hmat] at h; cases h) hrel.ready
    (fun h => by
      have hget : (X.snocHistory g ev r X.objects).get (X.newId g) = some ev := snoc_get_new
      unfold Returned at h; rw [hget] at h; exact h.elim)
  have reflect {v w : Ref} {l : Loc} (hw : X.RefPresent w)
      (h : ByteCausality L (X.snoc g ev r) l v w) : ByteCausality L X l v w :=
    ByteCausality.le_reflect_present le_snoc hX.effectValidity (fun hk => (hvo hk).mp)
      (observesMma_of_prefix le_snoc hX.effectValidity htma.2.2.1) hw h
  have rfNew : ∀ k, (X.snoc g ev r).rf (.thread (g, (X.tr g).length)) k = r k :=
    fun _ => ite_eq_left rfl
  have rfOld : ∀ {v : Ref} {k : Nat}, v ≠ .thread (g, (X.tr g).length) →
      (X.snoc g ev r).rf v k = X.rf v k := fun hv => ite_eq_right hv
  have newRead {a' : Acc} {bs' : List (Option Byte)}
      (hv : (X.snoc g ev r).MemReads (.thread (g, (X.tr g).length)) a' bs') :
      a' = a ∧ bs' = bs := by
    rcases hv with ⟨pc', hp⟩ | ⟨nw, pc', hp⟩ <;> rw [snoc_get_new] at hp <;>
      have hkd := congrArg Event.kind (Option.some.inj hp)
    · simp only [ev, Kind.rd.injEq] at hkd
      exact ⟨hkd.1.symm, hkd.2.symm⟩
    · cases hkd
  have hY : Consistent L K A mem0 (X.snoc g ev r) := by
    refine {
      thr := ?_, outside := ?_, rf := ?_, ctaBar := hextra.ctaBar, cluster := hextra.cluster,
      dependency := ⟨hready, horder.depAcyclic⟩, shfl := snoc_shflOk hX.shfl hns,
      vote := hextra.vote, warpValue := hextra.warpValue, matrix := hextra.matrix,
      elect := hextra.elect, warpBar := hextra.warpBar, observation := horder.observation,
      object := horder.object, asyncObject := horder.asyncObject, initFence := horder.initFence,
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
    · intro v a' bs' hv
      by_cases hn : v = .thread (g, (X.tr g).length)
      · subst v
        obtain ⟨rfl, rfl⟩ := newRead hv
        refine ⟨hread.len, fun k hk' => ?_⟩
        rw [rfNew]
        have hsrc := hread.src k hk'
        cases hrf : r k with
        | none => simp only [hrf] at hsrc ⊢; exact hsrc
        | some w =>
          rw [hrf] at hsrc
          obtain ⟨a'', bytes, hw, hc, hb'⟩ := hsrc
          exact ⟨a'', bytes, hwrite.mpr hw, hc, hb'⟩
      · obtain ⟨hlen, hsrc⟩ := hX.rf v a' bs' ((oldRead hn).mp hv)
        refine ⟨hlen, fun k hk' => ?_⟩
        rw [rfOld hn]
        have hsk := hsrc k hk'
        cases hrf : X.rf v k with
        | none => simp only [hrf] at hsk ⊢; exact hsk
        | some w =>
          rw [hrf] at hsk
          obtain ⟨a'', bytes, hw, hc, hb'⟩ := hsk
          exact ⟨a'', bytes, hwrite.mpr hw, hc, hb'⟩
    · intro v a' bs' k w hv hk' hrk hvw
      by_cases hn : v = .thread (g, (X.tr g).length)
      · subst v
        obtain ⟨_, first⟩ := hvw.starts
        exact noFromNew first
      · have hvX := (oldRead hn).mp hv
        rw [rfOld hn] at hrk
        have hsk := (hX.rf v a' bs' hvX).2 k hk'
        rw [hrk] at hsk
        obtain ⟨a'', bytes, hw, _⟩ := hsk
        exact hX.noFuture v a' bs' k w hvX hk' hrk (reflect hw.present hvw)
    · intro v a' bs' k w a'' otherBytes hv hk' hw hc hwv
      have hwX := hwrite.mp hw
      by_cases hn : v = .thread (g, (X.tr g).length)
      · subst v
        obtain ⟨rfl, rfl⟩ := newRead hv
        rw [rfNew]
        have hh := hread.hidden k w a'' otherBytes hk' hwX hc hwv
        cases hsr : r k with
        | none => simp [hsr] at hh
        | some w' =>
          rw [hsr] at hh
          exact fun h => hh (reflect hwX.present h)
      · have hvX := (oldRead hn).mp hv
        have hh := hX.hidden v a' bs' k w a'' otherBytes hvX hk' hwX hc (reflect hvX.present hwv)
        rw [rfOld hn]
        cases hsr : X.rf v k with
        | none => simp [hsr] at hh
        | some w' =>
          rw [hsr] at hh
          exact fun h => hh (reflect hwX.present h)
  refine ⟨_, hY, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

end
end PTX.Step
