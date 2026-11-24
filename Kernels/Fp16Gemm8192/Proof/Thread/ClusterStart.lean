-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers

@[expose] public section

/-! # Cluster members have started

After a role's event, every thread of its cluster has started: the cluster barrier that the
role's thread passed has collected an arrival of each member, and a member's arrival follows its
trace's first event. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxHeartbeats 4000000 in
/-- After a role's event, every thread of the cluster has started: its trace is nonempty. -/
theorem cluster_started_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g j h :
    Nat}
    {ev : Event} {r : Prologue.Role} (hg : g < L.threads) (he : X.get (g, j) = some ev)
    (hσ : Frame.stateAt (code L) X g j = some (some (.inr r))) (hh : h < L.threads)
    (hcl : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block)) : X.tr h ≠ [] := by
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  have hlen : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hj := Prologue.post_cluster hpre hX hlen hσ
  have hcl' : SameCluster L h g := ⟨hh, hg, hcl⟩
  have hsync := clusterSync_of_post_event hX hblock hpre.oneDimLaunch.1
    (Prologue.cluster_before hpre hX)
    (Prologue.cluster_arrive hpre hX) (Prologue.cluster_wait hpre hX) hcl' he hj
    (i := 0) (Prologue.clusterIndex_pos L h)
  obtain ⟨-, a, -, -, ha, -, -, -⟩ := hsync
  intro hnil
  rw [hnil, List.length_nil] at ha
  exact absurd ha (Nat.not_lt_zero a)

set_option maxHeartbeats 4000000 in
/-- **The ring initialization before a warp 8 to 11 role.** A role state of such a thread lies
past its cluster wait, and the state after the wait is the register lowering, a prologue state.
So the event after the wait is in the trace, and the cluster barrier orders thread 0's
initialization of each ring barrier of the CTA before that event. -/
theorem ring_init_exists_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g k : Nat} {r : Prologue.Role} {b : Bar} {cta : Nat}, g < L.threads →
    8 ≤ g % L.block / 32 → k ≤ (X.tr g).length → Frame.stateAt (code L) X g k =
      some (some (.inr r)) →
    b.Valid → cta < L.grid → L.clusterOfCta cta = L.clusterOfCta (g / L.block) →
    ∃ pc, X.get (cta * L.block, b.initIndex) = some ⟨pc, .mbInit (b.loc L cta) b.count⟩ := by
  intro g k r b cta hg h8 hk hσ hb hcta hcl
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  have hpost := Prologue.post_cluster hpre hX hk hσ
  have hA : Prologue.clusterIndex L g < (X.tr g).length := by omega
  obtain ⟨p, hp⟩ := Prologue.prologue_state hpre hX hg (Prologue.clusterIndex L g)
    (Prologue.clusterIndex_pos L g) le_rfl hA
  obtain ⟨hidx, hwp, hcp⟩ := (onPath_all hpre hX hg _ hA.le).1 p hp
  have hw : p.w = Prologue.warpOf L g := hwp (Prologue.clusterIndex_pos L g)
  have hsite := Prologue.site_of_clusterIndex hcp hw hidx.symm
  obtain ⟨s, w⟩ := p
  simp only at hsite
  subst hsite
  have hw' : w = g % L.block / 32 := hw
  have hw12 : g % L.block / 32 < 12 := Prologue.warpOf_lt hpre g
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[Prologue.clusterIndex L g]? = some e :=
    ⟨_, List.getElem?_eq_getElem hA⟩
  have hs1 : Frame.stateAt (code L) X g (Prologue.clusterIndex L g + 1) =
    some (some (.inl ⟨.wait, w⟩)) :=
    (stateAt_succ_inl he hp).trans rfl
  -- the state after the wait is the register lowering, a prologue state, not the role state
  have hne : k ≠ Prologue.clusterIndex L g + 2 := by
    intro hkeq
    rw [hkeq] at hσ
    obtain ⟨e', he'⟩ : ∃ e, (X.tr g)[Prologue.clusterIndex L g + 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs2 : Frame.stateAt (code L) X g (Prologue.clusterIndex L g + 2) =
        Prologue.next L g ⟨.wait, w⟩ e' := stateAt_succ_inl he' hs1
    have hw4 : w / 4 = 2 := by omega
    have hnext : Prologue.next L g ⟨.wait, w⟩ e' =
        some (some (.inl ⟨.setMaxReg, w⟩)) := by
      simp [Prologue.next, hw4]
    rw [hs2, hnext] at hσ
    simp at hσ
  have hj : Prologue.clusterIndex L g + 2 < k := by omega
  have hlt2 : Prologue.clusterIndex L g + 2 < (X.tr g).length := by omega
  obtain ⟨ev, he2⟩ : ∃ ev, X.get (g, Prologue.clusterIndex L g + 2) = some ev :=
    ⟨_, List.getElem?_eq_getElem hlt2⟩
  set g0 := cta * L.block
  have hg0t : g0 < L.threads := by
    unfold Launch.threads
    exact Nat.mul_lt_mul_of_pos_right hcta hblock
  have hf0 : g0 % L.block = 0 := Nat.mul_mod_left _ _
  have hc0 : g0 / L.block = cta := Nat.mul_div_cancel _ hblock
  have hcl' : SameCluster L g0 g := ⟨hg0t, hg, by rw [hc0, hcl]⟩
  set i := b.initSlot
  have hloc : Prologue.initLoc L g0 i = b.loc L cta := by
    simp only [Prologue.initLoc, Bar.loc, hc0, i, Bar.initSlot_off hb]
  have hjs : Prologue.clusterIndex L g + 1 < Prologue.clusterIndex L g + 2 := by omega
  have hsync := clusterSync_of_post_event hX hblock hpre.oneDimLaunch.1
    (Prologue.cluster_before hpre hX)
    (Prologue.cluster_arrive hpre hX) (Prologue.cluster_wait hpre hX) hcl' he2 hjs
    (i := 2 + i.val) (by rw [Prologue.clusterIndex_first ((Prologue.first_iff L g0).2 hf0)]; omega)
  obtain ⟨-, a, -, -, ha, hai, -, -⟩ := hsync
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g0, 2 + i.val) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hkind := init_event hpre hX hg0t hf0 i he0
  rw [hloc] at hkind
  obtain ⟨hinit, hcnt⟩ := init_bar i hb (Bar.initSlot_off hb)
  rw [← hinit]
  refine ⟨e0.pc, ?_⟩
  rw [he0, ← hcnt, ← hkind]

end
end PTX.Kernels.Fp16Gemm8192.Proof
