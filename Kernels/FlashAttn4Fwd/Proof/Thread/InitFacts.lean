-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueRun
public import Kernels.FlashAttn4Fwd.Proof.Interface.Init
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.NotInit
public import Lemmas.Flow.CommitTarget
public import Lemmas.Flow.NodupIdx

@[expose] public section

/-! # The barrier initializations, from the prologue's run invariant

`InitFacts` from the thread's machine:

* an initialization fires at a prologue state (a role has no `mbarrier.init` site,
  `Role.NoInitSite`), at an initialization site, which an election that returned the thread's
  lane precedes (`Prologue.Run.led`, with the full mask: `Prologue.Run.mask`); the thread's
  initializations are distinct (`Prologue.Run.nodup`) and each is of its table barrier, so it is
  the thread's only one of its barrier (`init_lead`);
* the thread's first cluster-barrier operation fires at the arrival site: a role state follows
  the cluster wait's event (`role_cluster`), and the wait site follows an earlier one. There
  the prologue's run invariant gives every barrier of the warp initialized, unless an election
  returned another lane (`Prologue.Run.done`; `init_done`);
* a commit's specification is resolved over the issuer's cluster (`commit_cluster`), for every
  commit event, whatever state the machine is in.

The first two take the machine's tracking of every thread (`Frame.Tracked`, a field of
`ThreadFacts`) and `Role.NoInitSite`, which each composed role's sites decide. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- No site of a composed role is an `mbarrier.init`. -/
def Role.NoInitSite (L : Launch) : Prop :=
  ∀ g (r : Role) ins, kernel.code[(code L g).pc (.inr r)]? = some ins → initOp ins.op = false

/-- A role state follows a cluster-barrier operation of the thread. -/
def RoleClusterJ : ThreadD → List Event → Prop
  | .inl _, _ => True
  | .inr _, es => ∃ e ∈ es, Prologue.isCluster e.kind = true

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A thread in a role has passed a cluster-barrier operation** (the cluster wait). -/
theorem role_cluster (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j r, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some (.inr r)) →
      ∃ e ∈ es.take j, Prologue.isCluster e.kind = true := by
  have h := Code.run_inv (sound hpre hg) htr RoleClusterJ trivial ?_
  · exact fun j r hr => h j (.inr r) hr
  intro d d' pre e t ins o hJ hat _ hc hf hn
  rcases d' with p' | r'
  · trivial
  rcases d with p | r
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some (.inr r')) at hn
    cases hx : Prologue.next L g p e with
    | none => rw [hx] at hn; cases hn
    | some x =>
      rw [hx] at hn
      cases x with
      | none => cases hn
      | some x =>
        have hat' : At t p.site.pc (Prologue.facts L g p) :=
          ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
        have hev := Prologue.event_ok hpre hat' hc hf hx
        cases x with
        | inl p' => simp [handoff] at hn
        | inr k =>
          have hs : p.site = .clWait := by
            obtain ⟨s⟩ := p
            cases s <;> simp only [Prologue.next] at hx
            all_goals (repeat' split at hx) <;> simp_all
          rw [hs] at hev
          obtain ⟨op, hop⟩ := hev
          exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), by rw [hop]; rfl⟩
  · obtain ⟨x, hx, hcl⟩ := hJ
    exact ⟨x, List.mem_append_left _ hx, hcl⟩

/-- An event of a prefix of the thread's run is an event of the execution before its end. -/
theorem get_of_mem_take {g k : Nat} {x : Event} (hx : x ∈ (X.tr g).take k) :
    ∃ j < k, X.get (g, j) = some x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < k := by simp at hj; omega
  refine ⟨j, hj', ?_⟩
  show (X.tr g)[j]? = some _
  rw [List.getElem_take]
  exact List.getElem?_eq_getElem _

/-- An event with its kind spelled out. -/
theorem get_kind {g j : Nat} {x : Event} {k : Kind} (hx : X.get (g, j) = some x)
    (hk : x.kind = k) : X.get (g, j) = some ⟨x.pc, k⟩ := by
  rw [hx, ← hk]

theorem isCluster_kind (x : Event) : PTX.isCluster x = Prologue.isCluster x.kind := by
  obtain ⟨_, k⟩ := x
  cases k <;> rfl

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- The event of a prologue state is of its site's kind. -/
theorem pro_event {g k : Nat} {p : Prologue.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inl p))) (hub : ∀ f, e.kind ≠ .ub f) :
    Prologue.EvOk L g p.site e.kind := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ
  have hat' : At t p.site.pc (Prologue.facts L g p) :=
    ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
  rcases Prologue.event_cases hpre hat' hc hf with h | ⟨⟨f, hf'⟩, -⟩
  · exact h
  · exact absurd hf' (hub f)

/-- An initialization fires at a prologue initialization site, after which the machine is at a
prologue state. -/
theorem init_state (ht : Frame.Tracked (code L) X) (hr : Role.NoInitSite L) {g k pc n : Nat}
    {m : Loc} (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩) :
    ∃ p, Frame.stateAt (code L) X g k = some (some (.inl p)) ∧ p.site.led = true ∧
      (∃ b : FBar, m = b.loc L (ctaOf L g) ∧ n = b.count) ∧
      ∃ p', Frame.stateAt (code L) X g (k + 1) = some (some (.inl p')) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ _ h => by cases h)
  rcases d with p | r
  · have hev := pro_event hpre hX he hσ (fun _ h => by cases h)
    have hst : Frame.stateAt (code L) X g (k + 1) =
        (Prologue.next L g p ⟨pc, .mbInit m n⟩).map (Option.bind · (handoff L g)) := by
      rw [Frame.stateAt_succ he, hσ]
      rfl
    refine ⟨p, hσ, ?_⟩
    rcases hev.init rfl with ⟨j, hs, hk⟩ | ⟨hs, hk⟩ <;> injection hk with h1 h2 <;>
      obtain ⟨s⟩ := p <;> simp only at hs <;> subst hs
    · exact ⟨rfl, ⟨_, h1, h2⟩, _, by rw [hst]; rfl⟩
    · exact ⟨rfl, ⟨_, h1, h2⟩, _, by rw [hst]; rfl⟩
  · obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (C := code L) hC hX he hσ
    exact absurd rfl (notInit_of_op (hr g r ins hc) hf m n)

/-- **An initialization** follows a full-mask election that returned the thread's lane, and is
the thread's only one of its barrier. -/
theorem init_lead (ht : Frame.Tracked (code L) X) (hr : Role.NoInitSite L) {g k pc n : Nat}
    {m : Loc} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩) :
    LeadAt L X g k ∧ ∀ k' pc' n', X.get (g, k') = some ⟨pc', .mbInit m n'⟩ → k' = k := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace hC hX hg
  obtain ⟨p, hσ, hled, ⟨b, hm, hn⟩, -⟩ := init_state hpre hX ht hr he
  have hR := Prologue.run hpre hg htr k p hσ
  refine ⟨?_, fun k' pc' n' he' => ?_⟩
  · obtain ⟨x, hx, mask, inst, hk⟩ := hR.led hled
    have hmask := hR.mask x hx mask inst _ hk
    subst hmask
    obtain ⟨j, hj, hget⟩ := get_of_mem_take hx
    exact ⟨j, hj, x.pc, inst, get_kind hget hk⟩
  · obtain ⟨-, -, -, ⟨b', hm', hn'⟩, -⟩ := init_state hpre hX ht hr he'
    have hb := (FBar.loc_inj (hm.symm.trans hm')).1
    subst hb
    have hnn : n' = n := hn'.trans hn.symm
    subst hnn
    -- Both events are in the run up to the later one, where the prologue invariant holds.
    have hlen : ∀ {i pc c} {l : Loc}, X.get (g, i) = some ⟨pc, .mbInit l c⟩ →
        i < (X.tr g).length := fun h => (List.getElem?_eq_some_iff.mp h).1
    have hk := hlen he
    have hk' := hlen he'
    obtain ⟨pcK, heK⟩ : ∃ pcK, X.get (g, max k k') = some ⟨pcK, .mbInit m n'⟩ := by
      rcases le_total k k' with h | h
      · rw [max_eq_right h]; exact ⟨_, he'⟩
      · rw [max_eq_left h]; exact ⟨_, he⟩
    obtain ⟨-, -, -, -, q, hq⟩ := init_state hpre hX ht hr heK
    have hR' := Prologue.run hpre hg htr (max k k' + 1) q hq
    have hgk : ∀ {i pc}, X.get (g, i) = some ⟨pc, .mbInit m n'⟩ → (hi : i < max k k' + 1) →
        ((X.tr g).take (max k k' + 1))[i]'(by simp; omega) = ⟨pc, .mbInit m n'⟩ := by
      intro i pc h hi
      have h' : (X.tr g)[i]? = some ⟨pc, .mbInit m n'⟩ := h
      rw [List.getElem_take]
      exact (List.getElem?_eq_some_iff.mp h').2
    have e1 := hgk he (by omega)
    have e2 := hgk he' (by omega)
    exact nodup_filter_map_idx (p := fun e : Event => Prologue.isInit e.kind) (f := Event.kind)
      hR'.nodup (by simp; omega) (by simp; omega) (by rw [e2]; rfl) (by rw [e1]; rfl)
      (by rw [e1, e2])

/-- **The cluster arrival**: a thread that reaches it initialized every barrier of its warp
before it, unless a full-mask election before it returned another lane. -/
theorem init_done (ht : Frame.Tracked (code L) X) {g : Nat} (hg : g < L.threads)
    (hcl : clFirst X g < (X.tr g).length) :
    (∀ b : FBar, b.initWarp = warpOf L g → ∃ k < clFirst X g, ∃ pc n,
      X.get (g, k) = some ⟨pc, .mbInit (b.loc L (ctaOf L g)) n⟩) ∨
    ∃ k < clFirst X g, ∃ pc inst l, X.Elect (g, k) pc 4294967295 inst l ∧ l ≠ laneOf L g := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace hC hX hg
  set c := clFirst X g with hc
  have hfirst : PTX.isCluster (X.tr g)[c] = true := List.findIdx_getElem (w := hcl)
  have hnone : ∀ x ∈ (X.tr g).take c, Prologue.isCluster x.kind = false := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < c := by simp at hj; omega
    rw [List.getElem_take, ← isCluster_kind]
    exact List.not_of_lt_findIdx hj'
  have he : X.get (g, c) = some (X.tr g)[c] := List.getElem?_eq_getElem hcl
  obtain ⟨op, hop⟩ : ∃ op, ((X.tr g)[c]).kind = .cluster op := by
    rw [isCluster_kind] at hfirst
    revert hfirst
    cases ((X.tr g)[c]).kind <;> simp [Prologue.isCluster]
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ f h => by rw [h] at hop; cases hop)
  rcases d with p | r
  · have hev := pro_event hpre hX he hσ (fun f h => by rw [hop] at h; cases h)
    rw [hop] at hev
    have hR := Prologue.run hpre hg htr c p hσ
    have hs : p.site = .clArrive := by
      rcases hev.cluster_site with h | h
      · exact h
      · have h0 := hR.clusters
        rw [List.countP_eq_zero.mpr fun x hx => by simp [hnone x hx], h] at h0
        cases h0
    have hget : ∀ {x}, x ∈ (X.tr g).take c → ∃ j < c, X.get (g, j) = some x :=
      fun hx => get_of_mem_take hx
    by_cases hl : ElectLead L g ((X.tr g).take c)
    · left
      have hd := hR.done hl
      rw [hs] at hd
      intro b hb
      by_cases hbd : b = .dealloc
      · subst hbd
        have hw : warpOf L g = 12 := by simpa [FBar.initWarp] using hb.symm
        obtain ⟨x, hx, hk⟩ := hd.2 hw rfl
        obtain ⟨j, hj, hx'⟩ := hget hx
        exact ⟨j, hj, x.pc, _, get_kind hx' hk⟩
      · have hw : warpOf L g = 0 := by simpa [FBar.initWarp, hbd] using hb.symm
        obtain ⟨j, rfl⟩ := FBar.exists_ofInit b hbd
        obtain ⟨x, hx, hk⟩ := hd.1 hw j j.isLt
        obtain ⟨i, hi, hx'⟩ := hget hx
        exact ⟨i, hi, x.pc, _, get_kind hx' hk⟩
    · right
      simp only [ElectLead, not_forall] at hl
      obtain ⟨x, hx, mask, inst, ld, hk, hne⟩ := hl
      have hmask := hR.mask x hx mask inst ld hk
      subst hmask
      obtain ⟨j, hj, hx'⟩ := hget hx
      exact ⟨j, hj, x.pc, inst, ld, get_kind hx' hk, hne⟩
  · obtain ⟨x, hx, hxc⟩ := role_cluster hpre hg htr c r hσ
    rw [hnone x hx] at hxc
    cases hxc

/-- **The targets of a commit** are barriers of the issuer's cluster. -/
theorem commit_cluster {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc}
    (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) (ht : TcCommit.target sp r = some m) :
    m.cta / 2 = ctaOf L i.1 / 2 := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨g, k⟩ := i
  rcases Frame.fired hC hX he with ⟨σ, o, -, hf⟩ | ⟨-, pc', f, hf⟩
  · rcases Code.fired_op hf with ⟨pc', f, hf'⟩ | ⟨t, ins, -, hfire⟩
    · cases hf'
    · obtain ⟨group, mb, bits, hs⟩ := commit_resolves hfire rfl
      obtain ⟨hr, hcta⟩ := target_cta hs ht
      have hcl := hpre.cluster
      simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1,
        Launch.oneDim_clusterStart hpre.oneDimLaunch.1,
        Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1, hcl] at hr hcta
      show m.cta / 2 = g / L.block / 2
      omega
  · cases hf

/-- **The thread layer's facts for the barrier initializations**, given that the machine
follows every thread and that no composed role has an `mbarrier.init` site. -/
theorem initFacts (ht : Frame.Tracked (code L) X) (hr : Role.NoInitSite L) : InitFacts L X where
  init hg he := init_lead hpre hX ht hr hg he
  init_done hg hcl := init_done hpre hX ht hg hcl
  commit_cluster he ht := commit_cluster hpre hX he ht

end
end PTX.Kernels.FlashAttn4Fwd.Proof
