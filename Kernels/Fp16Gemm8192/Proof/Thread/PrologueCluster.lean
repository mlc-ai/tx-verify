-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex
public import Lemmas.Cluster.ClusterFirstPhase
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # The prologue's cluster barrier and the first cluster phase

Thread `g` performs its first cluster event, the cluster arrive, at index `clusterIndex L g`,
two events after its fence. Along the prologue path every event before that index is a
shuffle, an election, a barrier initialization, a Tensor Memory allocation or write, a warp
barrier or a fence: none is a cluster operation or an exit. The arrive and the wait after it
are the thread's first cluster barrier events, so the first-phase facts of
`Lemmas/Cluster/ClusterFirstPhase.lean` apply with `first := clusterIndex L`.

`prologue_state` says that the thread stays in the prologue up to its arrive, and `fired_neither`
says that no prologue event before the arrive is a cluster operation or an exit. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Prologue

/-- The index of thread `g`'s first cluster event, its cluster arrive. -/
def clusterIndex (L : Launch) (g : Nat) : Nat := index L g ⟨.arrive, warpOf L g⟩

theorem clusterIndex_eq (L : Launch) (g : Nat) :
    clusterIndex L g = fenceIdx L g (warpOf L g) + 2 := rfl

theorem clusterIndex_pos (L : Launch) (g : Nat) : 0 < clusterIndex L g := by
  rw [clusterIndex_eq]
  have := fenceIdx_pos L g (warpOf L g)
  omega

theorem clusterIndex_first {L : Launch} {g : Nat} (hf : first L g = true) :
    clusterIndex L g = 25 := by
  have hw := warpOf_of_first hf
  simp [clusterIndex_eq, fenceIdx, hw, hf]

theorem clusterIndex_cases (L : Launch) (g : Nat) :
    (first L g = true ∧ clusterIndex L g = 25) ∨
      (first L g = false ∧ warpOf L g = 0 ∧ clusterIndex L g = 6) ∨
      (warpOf L g ≠ 0 ∧ clusterIndex L g = 3) := by
  by_cases hw : warpOf L g = 0
  · cases hf : first L g
    · exact .inr (.inl ⟨rfl, hw, by simp [clusterIndex_eq, fenceIdx, hw, hf]⟩)
    · exact .inl ⟨rfl, by simp [clusterIndex_eq, fenceIdx, hw, hf]⟩
  · exact .inr (.inr ⟨hw, by simp [clusterIndex_eq, fenceIdx, hw]⟩)

/-- Before the arrive, a prologue state is never a wait, a register request or a role
election. -/
theorem site_ne_of_lt {L : Launch} {g : Nat} {p : D} (hw : p.w = warpOf L g)
    (h : index L g p < clusterIndex L g) :
    p.site ≠ .arrive ∧ p.site ≠ .wait ∧ p.site ≠ .setMaxReg ∧ p.site ≠ .roleElect := by
  obtain ⟨s, w⟩ := p
  simp only at hw h ⊢
  subst hw
  rw [clusterIndex_eq] at h
  cases s <;> simp only [index] at h <;> simp <;> omega

/-- The state at the cluster arrive index is the arrive. -/
theorem site_of_clusterIndex {L : Launch} {g : Nat} {p : D} (hc : Canon L g p)
    (hw : p.w = warpOf L g) (hi : index L g p = clusterIndex L g) : p.site = .arrive := by
  obtain ⟨s, w⟩ := p
  obtain ⟨hA, hB, hC, -, -⟩ := hc
  simp only at hw hi hA hB hC ⊢
  rcases clusterIndex_cases L g with ⟨hf, h25⟩ | ⟨hf, hw0, h6⟩ | ⟨hw0, h3⟩
  · have hw' : w = 0 := hw.trans (warpOf_of_first hf)
    subst hw'
    clear hw
    rw [h25] at hi
    cases s <;> simp_all [index, fenceIdx]
    omega
  · have hw' : w = 0 := hw.trans hw0
    subst hw'
    clear hw hw0
    rw [h6] at hi
    cases s <;> simp_all [index, fenceIdx]
  · have hw' : w ≠ 0 := by rw [hw]; exact hw0
    have hf' : first L g = false := first_false_of_warp hw0
    clear hw hw0
    rw [h3] at hi
    cases s <;> simp_all [index, fenceIdx]

/-- The successor of a prologue state at a site other than the shuffle, the tensor
allocation and the cluster and role sites is a prologue state. -/
theorem next_inl_site (L : Launch) (g : Nat) (p : D) (e : Event)
    (h1 : p.site ≠ .shfl) (h2 : p.site ≠ .alloc) (h3 : p.site ≠ .arrive) (h4 : p.site ≠ .wait)
    (h5 : p.site ≠ .setMaxReg) (h6 : p.site ≠ .roleElect) :
    ∃ p', next L g p e = some (some (.inl p')) := by
  obtain ⟨s, w⟩ := p
  cases s with
  | init i =>
    by_cases hl : i.val + 1 < 18
    · exact ⟨{ site := .init ⟨i.val + 1, hl⟩, w := w }, by simp [next, hl]⟩
    · exact ⟨{ site := afterInits w, w := w }, by simp [next, hl]⟩
  | elect | allocWrite | warpBar | fence | fenceInit => exact ⟨_, rfl⟩
  | shfl => exact absurd rfl h1
  | alloc => exact absurd rfl h2
  | arrive => exact absurd rfl h3
  | wait => exact absurd rfl h4
  | setMaxReg => exact absurd rfl h5
  | roleElect => exact absurd rfl h6

/-- A trace: an event followed by another event fires from the concrete state reached after
the events before it, with a continuing successor. -/
private theorem trace_fired_some {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {M : Machine K A L g} {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    ∀ {j : Nat} {e : Event}, es[j]? = some e → j + 1 < es.length →
      ∃ τ u, M.after σ (es.take j) = some τ ∧ M.Fired τ e (some u) := by
  induction h with
  | nil σ => intro j e hj; simp at hj
  | step hf hn rest ih =>
    intro j e hj hlen
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, _, by simp, hf⟩
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some]
      exact ih (by simpa using hj) (by simp only [List.length_cons] at hlen; omega)
  | last hf =>
    intro j e hj hlen
    simp only [List.length_singleton] at hlen
    omega
  | dead hf hn hlen' hub =>
    intro j e hj hlen
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, _, by simp, hf⟩
    | succ j =>
      simp only [List.length_cons] at hlen
      omega

/-- The Tensor Memory allocation of a prologue state, when the thread continues past it, is
the allocation event (lane 0 of warp 0 writes the column next), and the state continues. -/
theorem next_alloc_inl {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) (hk : k + 1 < (X.tr g).length)
    {p : Prologue.D} (hp : Frame.stateAt (code L) X g k = some (some (.inl p))) (ha : p.site =
      .alloc) :
    ∃ p', next L g p e = some (some (.inl p')) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨τ, u, hτ, hf⟩ := trace_fired_some htr he hk
  have hτ' : Frame.stateAt (code L) X g k = some τ := hτ
  have hτe : τ = some (.inl p) := Option.some.inj (hτ'.symm.trans hp)
  subst hτe
  obtain ⟨t, ins, hat, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
  have hs0 : t.sub = 0 := by
    rw [hat.2.1]
    simp [Prologue.sub, ha]
  have hc' : kernel.code[Flow.tmemAlloc_0]? = some ins := by
    have h : kernel.code[p.site.pc]? = some ins := hc
    rw [ha] at h
    exact h
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨dst, n, rfl, -⟩ := fires_tcAlloc hs0 hfire
  obtain ⟨s, w⟩ := p
  simp only at ha
  subst ha
  by_cases hl : laneOf L g = 0
  · exact ⟨{ site := .allocWrite, w := w }, by simp [Prologue.next, hl]⟩
  · exact ⟨{ site := .warpBar, w := w }, by simp [Prologue.next, hl]⟩

/-- The thread stays in the prologue from its shuffle up to its cluster arrive: every state
before that index is a prologue state. -/
theorem prologue_state {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads) :
    ∀ k, 1 ≤ k → k ≤ clusterIndex L g → k < (X.tr g).length →
      ∃ p, Frame.stateAt (code L) X g k = some (some (.inl p)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _ hlen
    exact ⟨_, stateAt_one hpre hX hg (by omega)⟩
  | succ k hk ih =>
    intro hle hlen
    obtain ⟨p, hp⟩ := ih (by omega) (by omega)
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hidx, hwp, -⟩ := (onPath_all hpre hX hg k (by omega)).1 p hp
    have hw : p.w = warpOf L g := hwp (by omega)
    have hlt : index L g p < clusterIndex L g := by omega
    have hsites := site_ne_of_lt hw hlt
    have hpos : 1 ≤ index L g p := by omega
    have h1 : p.site ≠ .shfl := site_ne_shfl hpos
    obtain ⟨p', hn⟩ : ∃ p', next L g p e = some (some (.inl p')) := by
      by_cases ha : p.site = .alloc
      · exact next_alloc_inl hpre hX hg he hlen hp ha
      · exact next_inl_site L g p e h1 ha hsites.1 hsites.2.1 hsites.2.2.1 hsites.2.2.2
    exact ⟨p', by rw [stateAt_succ_inl he hp]; exact hn⟩

/-- A prologue state whose instruction is neither a cluster operation nor `ret` fires an event
that is neither a cluster operation nor an exit. -/
theorem fired_neither {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) {p : D}
    (hs : Frame.stateAt (code L) X g k = some (some (.inl p))) {ins : Instr}
    (hc : kernel.code[p.site.pc]? = some ins) (hcl : clusterOp ins.op = false)
    (hr : ins.op ≠ .ret) : (∀ op : ClusterOp, e.kind ≠ .cluster op) ∧ e.kind ≠ .exit := by
  obtain ⟨t, ins', o, -, -, hc', hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hs
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  refine ⟨fun cop hk => ?_, fun hk => (fires_exit_op hf hk).elim hr (not_exit hc)⟩
  rw [fires_cluster_op hf hk] at hcl
  simp [clusterOp] at hcl

/-- A cluster instruction fires the event of its cluster operation at its position. -/
theorem fires_cluster_event {L : Launch} {g : Nat} {t : TState} {cop : ClusterOp} {pc : Nat}
    {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl Prod L g t (.cluster cop)) e o) :
    e = ⟨pc, .cluster cop⟩ := by
  simp only [eventTmpl, Fires] at hf
  exact hf.1

set_option maxHeartbeats 4000000 in
/-- **The cluster barrier before the arrive.** Every event of a thread before its cluster
arrive is neither a cluster operation nor an exit. -/
theorem cluster_before {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ g < L.threads, ∀ j < clusterIndex L g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit := by
  intro g hg j hj ev hev
  have hlen : j < (X.tr g).length := len_of_get hev
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have h0 := first_event hpre hX hg hev
    subst h0
    exact ⟨fun op => by simp, by simp⟩
  · obtain ⟨p, hp⟩ := prologue_state hpre hX hg j hj1 hj.le hlen
    obtain ⟨hidx, hwp, hcp⟩ := (onPath_all hpre hX hg j hlen.le).1 p hp
    have hw : p.w = warpOf L g := hwp hj1
    have hsites := site_ne_of_lt hw (by omega)
    obtain ⟨s, w⟩ := p
    obtain ⟨-, hB, -⟩ := hcp
    cases s with
    | shfl => simp [index] at hidx; omega
    | elect => exact fired_neither hpre hX hev hp Flow.code_elect_0 rfl (by intro h; cases h)
    | init i =>
      have hf0 : g % L.block = 0 := (first_iff L g).1 (hB i rfl)
      simp only [index] at hidx
      subst hidx
      rw [init_event hpre hX hg hf0 i hev]
      exact ⟨fun op => by simp, by simp⟩
    | alloc => exact fired_neither hpre hX hev hp Flow.code_tmemAlloc_0 rfl (by intro h; cases h)
    | allocWrite =>
      exact fired_neither hpre hX hev hp Flow.code_tmemAlloc_0 rfl (by intro h; cases h)
    | warpBar =>
      exact fired_neither hpre hX hev hp Flow.code_warpBar_0 rfl (by intro h; cases h)
    | fence =>
      exact fired_neither hpre hX hev hp Flow.code_fenceProxy_0 rfl (by intro h; cases h)
    | fenceInit =>
      exact fired_neither hpre hX hev hp Flow.code_fenceMbarInit_0 rfl (by intro h; cases h)
    | arrive => exact (hsites.1 rfl).elim
    | wait => exact (hsites.2.1 rfl).elim
    | setMaxReg => exact (hsites.2.2.1 rfl).elim
    | roleElect => exact (hsites.2.2.2 rfl).elim

set_option maxHeartbeats 4000000 in
/-- **The cluster arrive.** A thread whose trace reaches its arrive index performs a cluster
arrive there. -/
theorem cluster_arrive {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ g < L.threads, clusterIndex L g < (X.tr g).length →
      ∃ pc, X.get (g, clusterIndex L g) = some ⟨pc, .cluster (.arrive true true)⟩ := by
  intro g hg hlen
  obtain ⟨p, hp⟩ := prologue_state hpre hX hg (clusterIndex L g) (clusterIndex_pos L g)
    le_rfl hlen
  obtain ⟨hidx, hwp, hcp⟩ := (onPath_all hpre hX hg _ hlen.le).1 p hp
  have hw : p.w = warpOf L g := hwp (clusterIndex_pos L g)
  have hsite := site_of_clusterIndex hcp hw hidx.symm
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[clusterIndex L g]? = some e :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨s, w⟩ := p
  simp only at hsite
  subst hsite
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hp
  have hc' : kernel.code[Flow.clusterArrive_0]? = some ins := hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_clusterArrive_0)
  obtain ⟨pc, hpc⟩ : ∃ pc, e = ⟨pc, .cluster (.arrive true true)⟩ := ⟨_, fires_cluster_event hf⟩
  exact ⟨pc, by show (X.tr g)[clusterIndex L g]? = _; rw [he, hpc]⟩

set_option maxHeartbeats 4000000 in
/-- **The cluster wait.** A thread whose trace reaches the index after its arrive performs a
cluster wait there. -/
theorem cluster_wait {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ g < L.threads, clusterIndex L g + 1 < (X.tr g).length →
      ∃ pc, X.get (g, clusterIndex L g + 1) = some ⟨pc, .cluster (.wait true)⟩ := by
  intro g hg hlen
  have hA : clusterIndex L g < (X.tr g).length := by omega
  obtain ⟨p, hp⟩ := prologue_state hpre hX hg (clusterIndex L g) (clusterIndex_pos L g)
    le_rfl hA
  obtain ⟨hidx, hwp, hcp⟩ := (onPath_all hpre hX hg _ hA.le).1 p hp
  have hw : p.w = warpOf L g := hwp (clusterIndex_pos L g)
  have hsite := site_of_clusterIndex hcp hw hidx.symm
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[clusterIndex L g]? = some e :=
    ⟨_, List.getElem?_eq_getElem hA⟩
  obtain ⟨s, w⟩ := p
  simp only at hsite
  subst hsite
  have hs' : Frame.stateAt (code L) X g (clusterIndex L g + 1) = some (some (.inl ⟨.wait, w⟩)) :=
    (stateAt_succ_inl he hp).trans rfl
  obtain ⟨e', he'⟩ : ∃ e, (X.tr g)[clusterIndex L g + 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he' hs'
  have hc' : kernel.code[Flow.clusterWait_0]? = some ins := hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_clusterWait_0)
  obtain ⟨pc, hpc⟩ : ∃ pc, e' = ⟨pc, .cluster (.wait true)⟩ := ⟨_, fires_cluster_event hf⟩
  exact ⟨pc, by show (X.tr g)[clusterIndex L g + 1]? = _; rw [he', hpc]⟩

/-- **The post-cluster bound.** A role state is reached only after the cluster arrive and its
wait: its index is past the wait. -/
theorem post_cluster {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    (hk : k ≤ (X.tr g).length) {r : Role} (h : Frame.stateAt (code L) X g k =
      some (some (.inr r))) :
    clusterIndex L g + 1 < k := by
  by_cases hg : g < L.threads
  · have hlt := cluster_before_role hpre hX hg hk h
    exact hlt
  · have hnil : X.tr g = [] := hX.outside g (by omega)
    rw [hnil, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [stateAt_zero] at h
    simp at h

end Prologue

end
end PTX.Kernels.Fp16Gemm8192.Proof
