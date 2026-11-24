-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame

public import Lemmas.Snoc.SnocObjectVisibility
public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Tcgen05.TcMmaReadMono
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! Memory and Tensor Memory constraints survive a memory-free, non-release object
instruction. Its own transition and local/control obligations are checked separately. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}

private theorem intent_index {v : Ref} {a : Acc} {w : Bool} (h : X.Intent v a w) :
    v.issuer.2 < (X.tr v.issuer.1).length := by
  obtain ⟨ev, he⟩ := intent_issuer h
  exact len_of_get he

theorem snocObject_noFuture {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hk : ∀ k, e.kind ≠ .tc k) (hrd : ∀ a bs, e.kind ≠ .rd a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc) :
    NoFuture L (X.snocObject g e r mb rec) := by
  intro v a bs k w hr hk' hrf hv
  have hr' := (snoc_memReads_control (g := g) (e := e) (r := r) hX.effectValidity hk hrd
    hrmw).mp hr
  have hle : X.le (X.snocObject g e r mb rec) :=
    Execution.le_trans (le_snoc (X := X) (g := g) (e := e) (r := r))
      (Execution.le_appendObject _ _ _)
  rw [hle.2.1 v k ⟨a, bs, hr'⟩] at hrf
  have hsrc := (hX.rf v a bs hr').2 k hk'
  rw [hrf] at hsrc
  obtain ⟨target, bytes, hw, _⟩ := hsrc
  exact hX.noFuture v a bs k w hr' hk' hrf
    (ByteCausality.le_reflect hle hX.tma.2.1 hX.tcCommit
      (fun old edge => snocObject_modelCausality_old hX.effectValidity hX.cluster
        (.of_rfWf hX.rf) hk hfree hid hnb hna (intent_index hr'.intent) old edge)
      (fun hw' => (PTX.snocObject_observedMma_iff hX.tcCommit hid hw').mp)
      (intent_index hw.intent) hv)

theorem snocObject_hidden {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g, (X.tr g).length))
    (hk : ∀ k, e.kind ≠ .tc k) (hrd : ∀ a bs, e.kind ≠ .rd a bs)
    (hwr : ∀ a bs, e.kind ≠ .wr a bs) (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hna : ∀ m tx count sc, e.kind ≠
      .arrive m tx count true sc) :
    Hidden L (X.snocObject g e r mb rec) := by
  intro v a bs k w target bytes hr hk' hw hc hv
  have hr' := (snoc_memReads_control (g := g) (e := e) (r := r) hX.effectValidity hk hrd
    hrmw).mp hr
  have hw' := (snoc_memWrites_control (g := g) (e := e) (r := r) hX.effectValidity hwr
    hrmw).mp hw
  have hle : X.le (X.snocObject g e r mb rec) :=
    Execution.le_trans (le_snoc (X := X) (g := g) (e := e) (r := r))
      (Execution.le_appendObject _ _ _)
  rw [hle.2.1 v k ⟨a, bs, hr'⟩]
  have reflect {src dst : Ref} {loc : Loc}
      (hsrc : src.issuer.2 < (X.tr src.issuer.1).length)
      (hdst : dst.issuer.2 < (X.tr dst.issuer.1).length)
      (he : ByteCausality L (X.snocObject g e r mb rec) loc src dst) :
      ByteCausality L X loc src dst :=
    ByteCausality.le_reflect hle hX.tma.2.1 hX.tcCommit
      (fun old edge => snocObject_modelCausality_old hX.effectValidity hX.cluster
        (.of_rfWf hX.rf) hk hfree hid hnb hna hsrc old edge)
      (fun hw' => (PTX.snocObject_observedMma_iff hX.tcCommit hid hw').mp) hdst he
  have hv' := reflect (intent_index hw'.intent) (intent_index hr'.intent) hv
  have hh := hX.hidden v a bs k w target bytes hr' hk' hw' hc hv'
  cases hs : X.rf v k with
  | none => simp only [hs] at hh
  | some src =>
    rw [hs] at hh
    have hsrc := (hX.rf v a bs hr').2 k hk'
    rw [hs] at hsrc
    obtain ⟨target', bytes', hsrc, _⟩ := hsrc
    exact fun hv => hh (reflect (intent_index hsrc.intent) (intent_index hw'.intent) hv)

/-- An object-recording plain event adds no Tensor Memory evidence about old loads. -/
theorem snocObject_readOk {A : List Assumption} (hv : EffectValidity L X)
    (hr : TcMma.ReadOk L A X) (hcl : ClusterHistoryOk L X) (hold : SnocReadsOld X g e r)
    (hfree : e.kind.Legacy)
    (hid : rec.id = .thread (g, (X.tr g).length)) (hk : ∀ k, e.kind ≠ .tc k)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc) :
    TcMma.ReadOk L A (X.snocObject g e r mb rec) := by
  have hlog : ∀ l, List.IsPrefix (X.objects l)
      ((fun l => if l = mb then X.objects mb ++ [rec] else X.objects l) l) := by
    intro l
    by_cases hl : l = mb
    · subst l; exact ⟨[rec], by simp⟩
    · simp [hl]
  refine (TcMma.ReadPreserved.readOk ⟨Execution.le_trans (le_snoc (X := X) (g := g) (e := e)
      (r := r)) (Execution.le_appendObject _ _ _), fun hf =>
        ⟨snocObject_baseCausality_old hcl hold hfree hid hnb hna hf,
      fun h => baseCausality_snoc_history (records := fun l => if l = mb then X.objects mb ++ [rec]
        else X.objects l) hlog h⟩, fun hw => snocObject_observedMma_iff hv.tcCommit hid hw,
      fun _ _ h => h, fun _ _ hr => .inl hr, fun hw => snocObject_mbarExec_old hv.tma.2.2.1 hid hw,
      fun _ hq => .inl hq⟩
      hr hv.tma.2.1) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _ _
  change (X.snoc g e r).get load = _ at hl
  rcases snoc_get_cases hl with ⟨rfl, he⟩ | ⟨hold, _⟩
  · exact (hk _ (by rw [← he])).elim
  · omega

theorem snocObject_tma (hv : EffectValidity L X) (hk : ∀ k, e.kind ≠ .tc k)
    (ho : ObjectsOk (X.snocObject g e r mb rec)) : TmaOk (X.snocObject g e r mb rec) := by
  have ht := hv.tma
  refine ⟨snoc_copy_wellFormed (r := r) ht, ?_, ho, snoc_arriveOk (r := r) ht.2.2.2⟩
  have hc : TcEffectsOk (X.snoc g e r) := by
    simpa only [TcEffectsOk, snoc_async, snoc_commit hk,
      snoc_tracksMma_of_not_tc hk,snoc_mmaIssue hk,snoc_cpIssue hk,snoc_shiftIssue hk] using ht.2.1
  exact hc

end
end PTX
