-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster

@[expose] public section

/-! # The cluster start, from the prologue's run invariant

`ClusterFacts`, `ThreadFacts.init_site`, `ThreadFacts.cluster_ops` and the initialization fields
of `RingFacts` and `TcFacts`, from the thread's machine:

* no role site is a cluster-barrier operation (`Role.noClusterSite`, decided on the sites), so
  every cluster-barrier operation fires at a prologue state, at the arrival or the wait site;
* the thread's first cluster-barrier operation fires at the arrival site (`cl_arrive_state`):
  a role state follows a cluster-barrier operation (`role_cluster`) and the wait site follows
  one (`Prologue.Run.clusters`); the next state is the wait site (`cl_wait_state`), whose event
  is the second and last one;
* an event of a kind the prologue does not fire is a role state's, after the wait;
* an initialization fires at an initialization site of warp 0 or 12 (`Prologue.Inv`), before
  the arrival (the site has passed no cluster-barrier operation), and the fences of the
  initializations before it number fewer than the two at the arrival (`Prologue.Run.fenced`,
  `Prologue.Run.fences`).

Each fact takes the machine's tracking of every thread (`Frame.Tracked`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### No role site is a cluster-barrier operation -/

/-- The positions of the cluster-barrier operations. -/
abbrev clusterPcs : List Nat := [Flow.clusterArrive_0, Flow.clusterWait_0]

theorem kernel_cluster_pcs : OpPcsFast kernel.code clusterOp clusterPcs = true := by
  decide +kernel

theorem Loader.site_not_cluster (s : Loader.Site) : s.pc ∉ clusterPcs := by
  cases s <;> site_decide

theorem Store.site_not_cluster (s : Store.Site) : s.pc ∉ clusterPcs := by
  cases s <;> site_decide

theorem Idle.site_not_cluster (s : Idle.Site) : s.pc ∉ clusterPcs := by
  cases s <;> site_decide

theorem Correction.site_not_cluster (s : Correction.Site) : s.pc ∉ clusterPcs := by
  cases s <;> site_decide

theorem Softmax.site_not_cluster (s : Softmax.Site) : s.pc ∉ clusterPcs := by
  cases s <;> site_decide

theorem Mma.site_not_cluster (s : Mma.Site) : s.pc ∉ clusterPcs := by
  cases s <;> site_decide

/-- No site of a composed role is a cluster-barrier operation. -/
def Role.NoClusterSite (L : Launch) : Prop :=
  ∀ g (r : Role) ins, kernel.code[(code L g).pc (.inr r)]? = some ins → clusterOp ins.op = false

/-- **No role site is a cluster-barrier operation.** -/
theorem Role.noClusterSite (L : Launch) : Role.NoClusterSite L := by
  intro g r ins hc
  by_contra hop
  have hpc := OpPcsFast.mem kernel_cluster_pcs hc (by simpa using hop)
  cases r with
  | idle s => exact Idle.site_not_cluster s.site hpc
  | loader d => exact Loader.site_not_cluster d.site hpc
  | mma d => exact Mma.site_not_cluster d.site hpc
  | store d => exact Store.site_not_cluster d.site hpc
  | softmax d => exact Softmax.site_not_cluster d.site hpc
  | corr d => exact Correction.site_not_cluster d.site hpc

/-! ### Counting along prefixes -/

theorem countP_take_succ {α : Type} (p : α → Bool) {l : List α} {j : Nat} (hj : j < l.length) :
    (l.take (j + 1)).countP p = (l.take j).countP p + if p l[j] then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.countP_append,
    List.countP_singleton]

theorem countP_take_mono {α : Type} (p : α → Bool) {l : List α} {i j : Nat} (h : i ≤ j) :
    (l.take i).countP p ≤ (l.take j).countP p :=
  (List.take_sublist_take_left h).countP_le

/-- A count that grows between two prefixes has an element in between. -/
theorem exists_of_countP_take_lt {α : Type} (p : α → Bool) {l : List α} {a c : Nat}
    (h : (l.take a).countP p < (l.take c).countP p) :
    ∃ f, a ≤ f ∧ f < c ∧ ∃ hf : f < l.length, p l[f] = true := by
  induction c with
  | zero => simp at h
  | succ c ih =>
    by_cases hlt : (l.take a).countP p < (l.take c).countP p
    · obtain ⟨f, h1, h2, hf, hp⟩ := ih hlt
      exact ⟨f, h1, by omega, hf, hp⟩
    · by_cases hc : c < l.length
      · have hac : a ≤ c := by
          by_contra hn
          have := countP_take_mono p (l := l) (show c + 1 ≤ a by omega)
          omega
        rw [countP_take_succ p hc] at h
        split_ifs at h with hp
        · exact ⟨c, hac, by omega, hc, hp⟩
        · omega
      · rw [List.take_of_length_le (by omega : l.length ≤ c + 1)] at h
        rw [List.take_of_length_le (by omega : l.length ≤ c)] at hlt
        omega

/-- At most two elements satisfy `p` when only positions `a` and `a + 1` may. -/
theorem countP_le_two {α : Type} (p : α → Bool) (l : List α) (a : Nat)
    (h : ∀ i (hi : i < l.length), p l[i] = true → i = a ∨ i = a + 1) : l.countP p ≤ 2 := by
  have key : ∀ n,
      (l.take n).countP p ≤ (if a < n then 1 else 0) + (if a + 1 < n then 1 else 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      by_cases hn : n < l.length
      · rw [countP_take_succ p hn]
        by_cases hp : p l[n] = true
        · simp only [hp, ↓reduceIte]
          rcases h n hn hp with rfl | rfl <;> split_ifs at ih ⊢ <;> omega
        · simp only [hp, Bool.false_eq_true, ↓reduceIte]
          split_ifs at ih ⊢ <;> omega
      · rw [List.take_of_length_le (by omega : l.length ≤ n + 1)]
        rw [List.take_of_length_le (by omega : l.length ≤ n)] at ih
        split_ifs at ih ⊢ <;> omega
  have := key l.length
  rw [List.take_length] at this
  split_ifs at this <;> omega

/-! ### The cluster arrival and wait -/

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- No event before the first cluster-barrier operation is one. -/
theorem cl_none {g : Nat} :
    ∀ x ∈ (X.tr g).take (clFirst X g), Prologue.isCluster x.kind = false := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < clFirst X g := by simp at hj; omega
  rw [List.getElem_take, ← isCluster_kind]
  exact List.not_of_lt_findIdx hj'

/-- The first cluster-barrier operation. -/
theorem cl_kind {g : Nat} (hcl : clFirst X g < (X.tr g).length) :
    ∃ op, ((X.tr g)[clFirst X g]).kind = .cluster op := by
  have hfirst : PTX.isCluster (X.tr g)[clFirst X g] = true := List.findIdx_getElem (w := hcl)
  rw [isCluster_kind] at hfirst
  revert hfirst
  cases ((X.tr g)[clFirst X g]).kind <;> simp [Prologue.isCluster]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **The first cluster-barrier operation fires at the arrival site.** -/
theorem cl_arrive_state {g : Nat} (hg : g < L.threads) (hcl : clFirst X g < (X.tr g).length) :
    Frame.stateAt (code L) X g (clFirst X g) = some (some (.inl ⟨.clArrive⟩)) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace hC hX hg
  have he : X.get (g, clFirst X g) = some (X.tr g)[clFirst X g] := List.getElem?_eq_getElem hcl
  obtain ⟨op, hop⟩ := cl_kind hcl
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ f h => by rw [h] at hop; cases hop)
  rcases d with p | r
  · have hev := pro_event hpre hX he hσ (fun f h => by rw [hop] at h; cases h)
    rw [hop] at hev
    have hR := Prologue.run hpre hg htr (clFirst X g) p hσ
    rcases hev.cluster_site with h | h
    · obtain ⟨s⟩ := p
      simp only at h
      subst h
      exact hσ
    · have h0 := hR.clusters
      rw [List.countP_eq_zero.mpr fun x hx => by simp [cl_none x hx], h] at h0
      cases h0
  · obtain ⟨x, hx, hxc⟩ := role_cluster hpre hg htr (clFirst X g) r hσ
    rw [cl_none x hx] at hxc
    cases hxc

/-- The state after the arrival is the wait site. -/
theorem cl_wait_state {g : Nat} (hg : g < L.threads) (hcl : clFirst X g < (X.tr g).length) :
    Frame.stateAt (code L) X g (clFirst X g + 1) = some (some (.inl ⟨.clWait⟩)) := by
  have he : (X.tr g)[clFirst X g]? = some (X.tr g)[clFirst X g] := List.getElem?_eq_getElem hcl
  rw [Frame.stateAt_succ he, cl_arrive_state hpre hX ht hg hcl]
  rfl

/-- **The first cluster-barrier operation is the relaxed, unaligned arrival.** -/
theorem ClusterFacts_arrive :
    ∀ {g : Nat}, g < L.threads → clFirst X g < (X.tr g).length →
      ∃ pc, X.get (g, clFirst X g) = some ⟨pc, .cluster (.arrive false false)⟩ := by
  intro g hg hcl
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have he : X.get (g, clFirst X g) = some (X.tr g)[clFirst X g] := List.getElem?_eq_getElem hcl
  obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
    Frame.fired_site hC hX he (cl_arrive_state hpre hX ht hg hcl)
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0)
  exact ⟨_, by rw [he, hf.1]⟩

/-- **The next event is the unaligned wait.** -/
theorem ClusterFacts_wait :
    ∀ {g : Nat}, g < L.threads → clFirst X g + 1 < (X.tr g).length →
      ∃ pc, X.get (g, clFirst X g + 1) = some ⟨pc, .cluster (.wait false)⟩ := by
  intro g hg hcl
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have he : X.get (g, clFirst X g + 1) = some (X.tr g)[clFirst X g + 1] :=
    List.getElem?_eq_getElem hcl
  obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
    Frame.fired_site hC hX he (cl_wait_state hpre hX ht hg (by omega))
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
  exact ⟨_, by rw [he, hf.1]⟩

/-- **A thread that reaches the arrival shuffled first.** -/
theorem ClusterFacts_shfl0 :
    ∀ {g : Nat}, g < L.threads → clFirst X g < (X.tr g).length →
      0 < clFirst X g ∧ ∃ pc md a b c r o, X.get (g, 0) = some ⟨pc, .shfl md a b c r o⟩ := by
  intro g hg hcl
  have hσc := cl_arrive_state hpre hX ht hg hcl
  have hc0 : 0 < clFirst X g := by
    by_contra h0
    rw [show clFirst X g = 0 by omega, Frame.stateAt_zero] at hσc
    cases hσc
  refine ⟨hc0, ?_⟩
  have he0 : (X.tr g)[0]? = some (X.tr g)[0] := List.getElem?_eq_getElem (by omega)
  obtain ⟨d1, hσ1⟩ := Frame.stateAt_live ht hg hσc (show 1 ≤ clFirst X g by omega)
  rw [Frame.stateAt_succ he0, Frame.stateAt_zero] at hσ1
  change X.get (g, 0) = some (X.tr g)[0] at he0
  generalize (X.tr g)[0] = x at hσ1 he0
  obtain ⟨pc0, k0⟩ := x
  change (Prologue.next L g ⟨.shfl0⟩ ⟨pc0, k0⟩).map (Option.bind · (handoff L g)) =
    some (some d1) at hσ1
  cases k0 with
  | shfl md a b c r o => exact ⟨pc0, md, a, b, c, r, o, he0⟩
  | _ => simp [Prologue.next] at hσ1

/-- A cluster-barrier operation fires at the arrival or the wait site. -/
theorem cluster_state {g k pc : Nat} {op : ClusterOp} (he : X.get (g, k) = some ⟨pc, .cluster op⟩) :
    ∃ p : Prologue.D, Frame.stateAt (code L) X g k = some (some (.inl p)) ∧
      (p.site = .clArrive ∨ p.site = .clWait) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ _ h => by cases h)
  rcases d with p | r
  · exact ⟨p, hσ, (pro_event hpre hX he hσ (fun f h => by cases h)).cluster_site⟩
  · obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
    have h := fires_cluster_op hf rfl
    have hn := Role.noClusterSite L g r ins hc
    rw [h] at hn
    cases hn

/-- **The thread's only cluster-barrier operations are the arrival and the wait.** -/
theorem ClusterFacts_cl_only :
    ∀ {g k pc : Nat} {op : ClusterOp}, g < L.threads →
      X.get (g, k) = some ⟨pc, .cluster op⟩ → k = clFirst X g ∨ k = clFirst X g + 1 := by
  intro g k pc op hg he
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace hC hX hg
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hkc : Prologue.isCluster ((X.tr g)[k]).kind = true := by
    have h : (X.tr g)[k] = ⟨pc, .cluster op⟩ := (List.getElem?_eq_some_iff.mp he).2
    rw [h]
    rfl
  obtain ⟨p, hσ, hs⟩ := cluster_state hpre hX ht he
  have hR := Prologue.run hpre hg htr k p hσ
  -- No cluster-barrier operation before `k` puts the first one at or after `k`.
  have hle : clFirst X g ≤ k := by
    by_contra hlt
    exact absurd (List.not_of_lt_findIdx (show k < clFirst X g by omega))
      (by rw [isCluster_kind]; simp [hkc])
  have hcl : clFirst X g < (X.tr g).length := by omega
  rcases hs with hs | hs
  · -- At the arrival site no operation precedes, so `k` is the first.
    left
    by_contra hne
    have hlt : clFirst X g < k := by omega
    have h0 := hR.clusters
    rw [hs] at h0
    have h1 : 0 < ((X.tr g).take k).countP (fun e => Prologue.isCluster e.kind) := by
      refine List.countP_pos_iff.mpr ⟨(X.tr g)[clFirst X g], ?_, ?_⟩
      · exact List.mem_iff_getElem.mpr ⟨clFirst X g, by simp; omega, by simp⟩
      · obtain ⟨op', hop⟩ := cl_kind hcl
        rw [hop]
        rfl
    simp only [Prologue.Site.clusters] at h0
    omega
  · -- At the wait site one operation precedes; the arrival's state is not the wait site.
    right
    have hne : k ≠ clFirst X g := by
      intro hkc'
      rw [hkc', cl_arrive_state hpre hX ht hg hcl] at hσ
      simp only [Option.some.injEq, Sum.inl.injEq] at hσ
      rw [← hσ] at hs
      cases hs
    by_contra hne'
    have hlt : clFirst X g + 1 < k := by omega
    have hσw := cl_wait_state hpre hX ht hg hcl
    have hew : X.get (g, clFirst X g + 1) = some (X.tr g)[clFirst X g + 1] :=
      List.getElem?_eq_getElem (show clFirst X g + 1 < (X.tr g).length by omega)
    have hevw := pro_event hpre hX hew hσw (fun f h => by
      have := (show Prologue.EvOk L g .clWait ((X.tr g)[clFirst X g + 1]).kind from by
        obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX hew hσw
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
        exact ⟨_, by rw [hf.1]⟩)
      obtain ⟨op', h'⟩ := this
      rw [h] at h'
      cases h')
    obtain ⟨op', hop'⟩ := hevw
    obtain ⟨op0, hop0⟩ := cl_kind hcl
    have h2 : 2 ≤ ((X.tr g).take k).countP (fun e => Prologue.isCluster e.kind) := by
      have m1 := countP_take_mono (fun e : Event => Prologue.isCluster e.kind) (l := X.tr g)
        (show clFirst X g + 2 ≤ k by omega)
      have i1 : Prologue.isCluster ((X.tr g)[clFirst X g]).kind = true := by rw [hop0]; rfl
      have i2 : Prologue.isCluster ((X.tr g)[clFirst X g + 1]).kind = true := by rw [hop']; rfl
      rw [countP_take_succ _ (by omega), countP_take_succ _ hcl] at m1
      simp only [i1, i2, ↓reduceIte] at m1
      omega
    have h0 := hR.clusters
    rw [hs] at h0
    simp only [Prologue.Site.clusters] at h0
    omega

/-- **Every event of a kind the prologue does not fire follows the wait.** -/
theorem ClusterFacts_post :
    ∀ {g j : Nat} {ev : Event}, g < L.threads → X.get (g, j) = some ev →
      ¬ PreKind ev.kind → (∀ f, ev.kind ≠ .ub f) → clFirst X g + 1 < j := by
  intro g j ev hg he hk hub
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace hC hX hg
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun pc f h => hub f (by rw [h]))
  rcases d with p | r
  · have hev := pro_event hpre hX he hσ hub
    exfalso
    apply hk
    have := hev.proKind
    revert this
    cases ev.kind <;> simp [Prologue.ProKind, PreKind]
  · obtain ⟨x, hx, hxc⟩ := role_cluster hpre hg htr j r hσ
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < j := by simp at hi; omega
    have hci : clFirst X g ≤ i := by
      by_contra hlt
      have h1 := List.not_of_lt_findIdx (show i < clFirst X g by omega)
      rw [isCluster_kind] at h1
      rw [List.getElem_take, h1] at hxc
      cases hxc
    have hcl : clFirst X g < (X.tr g).length := by omega
    by_contra hle
    have hj' : j = clFirst X g + 1 := by omega
    rw [hj', cl_wait_state hpre hX ht hg hcl] at hσ
    cases hσ

/-- **An initialization is followed by a fence before the arrival**, in a thread that reaches
the arrival. -/
theorem ClusterFacts_fence_of_arrive :
    ∀ {g a pc c : Nat} {m : Loc}, g < L.threads → clFirst X g < (X.tr g).length →
      X.get (g, a) = some ⟨pc, .mbInit m c⟩ →
      ∃ f pcf, a < f ∧ f < clFirst X g ∧ X.get (g, f) = some ⟨pcf, .fenceMbarInit⟩ := by
  intro g a pc c m hg hcl he
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace hC hX hg
  have ha : a < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hea : (X.tr g)[a] = ⟨pc, .mbInit m c⟩ := (List.getElem?_eq_some_iff.mp he).2
  obtain ⟨p, hσ, hled, -, -⟩ := init_state hpre hX ht (Role.noInitSite L) he
  have hRa := Prologue.run hpre hg htr a p hσ
  -- The initialization site has passed no cluster-barrier operation: `a` is before the arrival.
  have hpcl : p.site.clusters = 0 := by
    obtain ⟨s⟩ := p
    cases s <;> simp_all [Prologue.Site.led, Prologue.Site.clusters]
  have hac : a < clFirst X g := by
    by_contra hge
    have h1 : 0 < ((X.tr g).take a).countP (fun e => Prologue.isCluster e.kind) := by
      by_cases hca : clFirst X g = a
      · exfalso
        obtain ⟨op, hop⟩ := cl_kind hcl
        simp [hca, hea] at hop
      · refine List.countP_pos_iff.mpr ⟨(X.tr g)[clFirst X g], ?_, ?_⟩
        · exact List.mem_iff_getElem.mpr ⟨clFirst X g, by simp; omega, by simp⟩
        · obtain ⟨op, hop⟩ := cl_kind hcl
          rw [hop]
          rfl
    have h0 := hRa.clusters
    omega
  -- The fences: fewer than two before `a`, two before the arrival.
  have hRc := Prologue.run hpre hg htr (clFirst X g) _ (cl_arrive_state hpre hX ht hg hcl)
  have hfa := hRc.fenced a (by simp; omega) (by rw [List.getElem_take, hea]; rfl)
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hac)] at hfa
  have hfc := hRc.fences
  simp only [Prologue.Site.fences] at hfc
  have hlt : ((X.tr g).take a).countP (fun e : Event => Prologue.isFence e.kind) <
      ((X.tr g).take (clFirst X g)).countP (fun e : Event => Prologue.isFence e.kind) := by
    rw [hfc]
    exact hfa
  obtain ⟨f, hf1, hf2, hf, hp⟩ := exists_of_countP_take_lt _ hlt
  have hfa' : f ≠ a := by
    rintro rfl
    rw [hea] at hp
    cases hp
  refine ⟨f, ((X.tr g)[f]).pc, by omega, hf2, ?_⟩
  have hk : ((X.tr g)[f]).kind = .fenceMbarInit := by
    revert hp
    cases ((X.tr g)[f]).kind <;> simp [Prologue.isFence]
  exact get_kind (List.getElem?_eq_getElem hf) hk

/-- `ClusterFacts.fence`: `ClusterFacts_fence_of_arrive`. -/
theorem ClusterFacts_fence :
    ∀ {g a pc c : Nat} {m : Loc}, g < L.threads → clFirst X g < (X.tr g).length →
      X.get (g, a) = some ⟨pc, .mbInit m c⟩ →
      ∃ f pcf, a < f ∧ f < clFirst X g ∧ X.get (g, f) = some ⟨pcf, .fenceMbarInit⟩ :=
  ClusterFacts_fence_of_arrive hpre hX ht

/-- **Every initialization is of a table barrier of the thread's CTA, with its count**: warp
12's of the handshake barrier, warp 0's of the others. -/
theorem ClusterFacts_init_site :
    ∀ {g k pc c : Nat} {m : Loc}, g < L.threads →
      X.get (g, k) = some ⟨pc, .mbInit m c⟩ →
        ∃ b : FBar, m = b.loc L (ctaOf L g) ∧ c = b.count ∧
          (b = .dealloc → warpOf L g = 12) ∧ (b ≠ .dealloc → warpOf L g = 0) := by
  intro g k pc c m hg he
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨p, hσ, -, -, -⟩ := init_state hpre hX ht (Role.noInitSite L) he
  have hev := pro_event hpre hX he hσ (fun f h => by cases h)
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hC hX he hσ
  have hinv : Prologue.Inv L g p := hinv
  rcases hev.init rfl with ⟨j, hs, hk⟩ | ⟨hs, hk⟩
  · injection hk with h1 h2
    exact ⟨FBar.ofInit j, h1, h2, fun h => absurd h (FBar.ofInit_ne_dealloc j),
      fun _ => hinv.warp0 (.inr ⟨j, hs⟩)⟩
  · injection hk with h1 h2
    exact ⟨.dealloc, h1, h2, fun _ => hinv.warp12 (.inr hs), fun h => absurd rfl h⟩

/-- `ThreadFacts.init_site`: `ClusterFacts.init_site`. -/
theorem ThreadFacts_init_site :
    ∀ {g k pc : Nat} {m : Loc} {c : Nat}, g < L.threads →
      X.get (g, k) = some ⟨pc, .mbInit m c⟩ →
        ∃ b : FBar, m = b.loc L (ctaOf L g) ∧ c = b.count ∧
          (b = .dealloc → warpOf L g = 12) ∧ (b ≠ .dealloc → warpOf L g = 0) :=
  fun hg he => ClusterFacts_init_site hpre hX ht hg he

/-- **A thread has at most two cluster-barrier operations.** -/
theorem ThreadFacts_cluster_ops :
    ∀ {g : Nat}, g < L.threads →
      ((X.tr g).filter (fun e => Prologue.isCluster e.kind)).length ≤ 2 := by
  intro g hg
  rw [← List.countP_eq_length_filter]
  refine countP_le_two _ _ (clFirst X g) fun i hi hc => ?_
  have he : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hi
  obtain ⟨op, hop⟩ : ∃ op, ((X.tr g)[i]).kind = .cluster op := by
    revert hc
    cases ((X.tr g)[i]).kind <;> simp [Prologue.isCluster]
  exact ClusterFacts_cl_only hpre hX ht hg (get_kind he hop)

/-! ### The initialization fields of the ring and Tensor Core facts -/

omit hpre hX ht in
theorem FBar.ring_ne_dealloc : ∀ b : FBar, b.ring = true → b ≠ .dealloc := by decide

/-- **An initialization of a ring barrier is an elected lane's, its thread's only one of the
barrier.** -/
theorem RingFacts_init :
    ∀ {g k pc c n : Nat} {b : FBar}, g < L.threads →
      X.get (g, k) = some ⟨pc, .mbInit (b.loc L c) n⟩ → b.ring →
        LeadAt L X g k ∧
          ∀ k' pc' n', X.get (g, k') = some ⟨pc', .mbInit (b.loc L c) n'⟩ → k' = k :=
  fun hg he _ => init_lead hpre hX ht (Role.noInitSite L) hg he

/-- **A thread of warp 0 that reaches its arrival initialized every ring barrier**, unless an
election returned another lane. -/
theorem RingFacts_init_done :
    ∀ {g : Nat}, g < L.threads → warpOf L g = 0 → clFirst X g < (X.tr g).length →
      (∀ b : FBar, b.ring → ∃ k < clFirst X g, ∃ pc n,
        X.get (g, k) = some ⟨pc, .mbInit (b.loc L (ctaOf L g)) n⟩) ∨
      ∃ k < clFirst X g, ∃ pc inst l, X.Elect (g, k) pc 4294967295 inst l ∧ l ≠ laneOf L g := by
  intro g hg hw hcl
  rcases init_done hpre hX ht hg hcl with h | h
  · exact .inl fun b hb => h b (by simp [FBar.initWarp, FBar.ring_ne_dealloc b hb, hw])
  · exact .inr h

/-- **A thread of warp 0 that reaches its arrival initialized every barrier but the handshake
barrier**, unless an election returned another lane. -/
theorem TcFacts_init_done :
    ∀ {g : Nat}, g < L.threads → warpOf L g = 0 → clFirst X g < (X.tr g).length →
      (∀ b : FBar, b ≠ .dealloc → ∃ k < clFirst X g, ∃ pc n,
        X.get (g, k) = some ⟨pc, .mbInit (b.loc L (ctaOf L g)) n⟩) ∨
      ∃ k < clFirst X g, ∃ pc inst l, X.Elect (g, k) pc 4294967295 inst l ∧ l ≠ laneOf L g := by
  intro g hg hw hcl
  rcases init_done hpre hX ht hg hcl with h | h
  · exact .inl fun b hb => h b (by simp [FBar.initWarp, hb, hw])
  · exact .inr h

end
end PTX.Kernels.FlashAttn4Fwd.Proof
