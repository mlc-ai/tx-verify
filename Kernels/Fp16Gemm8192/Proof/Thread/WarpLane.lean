-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.WarpFacts

@[expose] public section

/-! # A thread at a collective site, and the lanes of its warp

The three facts of the progress layer's warp class, for a thread at a collective site at the end of
its trace: it has made no event of an instance of the site (`coll_none_fact`), its events before
the site (`coll_before_fact`), and where each lane of its warp stands (`coll_lane_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Warp 0's allocation is at its allocation index. -/
theorem w0_alloc_site {p : D} (hw : p.site ≠ .shfl → p.w = 0) (hc : Canon L g p)
    (h : index L g p = index L g ⟨.alloc, 0⟩) : p.site = .alloc := by
  obtain ⟨site, w⟩ := p
  obtain ⟨-, hinit, hwrite, hset, hrole⟩ := hc
  simp only at hw hinit hwrite hset hrole
  cases site with
  | alloc => rfl
  | init i =>
    have hf := hinit i rfl
    have := i.isLt
    simp [Prologue.index, hf] at h
    omega
  | allocWrite =>
    have hf := hwrite rfl
    simp [Prologue.index, hf] at h
  | setMaxReg => have := hset rfl; have := hw (by simp); omega
  | roleElect => have := hrole rfl; have := hw (by simp); omega
  | fence | fenceInit | arrive | wait =>
    have hw0 := hw (by simp)
    subst hw0
    simp [Prologue.index, Prologue.fenceIdx] at h
    split_ifs at h <;> omega
  | shfl | elect | warpBar =>
    simp [Prologue.index] at h
    split_ifs at h <;> omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
include hpre hX

/-- A thread at warp 0's warp barrier is at its index, in warp 0. -/
theorem wb_end (hg : g < L.threads) {w : Nat}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inl ⟨.warpBar, w⟩))) :
    (X.tr g).length = wbIdx L g ∧ warpOf L g = 0 := by
  obtain ⟨h1, h2, hc⟩ := pro_end hpre hX hg le_rfl hσ
  have hl : (X.tr g).length = wbIdx L g := by rw [h1]; simp [Prologue.index, wbIdx]
  refine ⟨hl, ?_⟩
  have hw : w = 0 := hc.1 (.inr (.inr rfl))
  rw [← h2 (by rw [hl]; simp only [wbIdx, Prologue.index]; split_ifs <;> omega)]
  exact hw

/-- A thread at warp 11's role election has made six events, in warp 11. -/
theorem roleElect_end (hg : g < L.threads) {w : Nat}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inl ⟨.roleElect, w⟩))) :
    (X.tr g).length = 6 ∧ warpOf L g = 11 := by
  obtain ⟨h1, h2, hc⟩ := pro_end hpre hX hg le_rfl hσ
  have hw : w = 11 := hc.2.2.2.2 rfl
  subst hw
  have hl : (X.tr g).length = 6 := by rw [h1]; simp [Prologue.index, Prologue.fenceIdx]
  exact ⟨hl, by rw [← h2 (by omega)]⟩

/-- **A thread at a collective site has made no event of an instance of it.** -/
theorem coll_none_fact (hg : g < L.threads) {d : ThreadD} {s : CollSite}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hs : d.coll = some s) :
    ∀ j e, X.get (g, j) = some e → ¬ s.Matches e := by
  intro j e he hm
  have hj := len_of_get he
  simp only at hj
  rcases d with ⟨site, w⟩ | (l | ⟨site, w', q, fp, ap, cp, r, x⟩ | ⟨site, ap, cp, r, x⟩ | c)
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
    · have := (pro_end hpre hX hg le_rfl hσ).1
      simp only [Prologue.index] at this
      omega
    · obtain ⟨inst, leader, rfl⟩ := hm
      have := (pro_end hpre hX hg le_rfl hσ).1
      simp only [Prologue.index] at this
      have hj0 : j = 0 := by omega
      subst hj0
      have h0 := first_event hpre hX hg he
      cases h0
    · obtain ⟨pc, inst, rfl⟩ := hm
      obtain ⟨hl, hw0⟩ := wb_end hpre hX hg hσ
      obtain ⟨d', hd'⟩ := Frame.stateAt_live (tracked hpre hX) hg hσ (k := j) (by omega)
      rcases d' with q | r
      · obtain ⟨h1, h2, hc⟩ := pro_end hpre hX hg (by omega) hd'
        have hq0 : q.site ≠ .shfl → q.w = 0 := fun hq =>
          (h2 (by have := Prologue.index_pos (L := L) (g := g) hq; omega)).trans hw0
        have hne : q.site ≠ .warpBar := by
          intro hq
          have := (w0_site hq0 hc (by omega)).1
          have hi : index L g q = wbIdx L g := by
            obtain ⟨site, w⟩ := q
            simp only at hq
            subst hq
            simp [Prologue.index, wbIdx]
          omega
        obtain ⟨t, ins, o, -, -, hc', hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hd'
        exact fires_notWarpBar_op (Prologue.notWarpBar_site hne hc') hf _ _ rfl
      · have := (onPath_all hpre hX hg j (by omega)).2 r hd'
        have h2 := wbIdx_lt_wait (L := L) (g := g)
        rw [hw0] at this
        omega
    · obtain ⟨inst, leader, rfl⟩ := hm
      obtain ⟨hl, hw11⟩ := roleElect_end hpre hX hg hσ
      have := role_elect_event hpre hX hg (j := j) he (by omega)
      omega
  · simp [ThreadD.coll] at hs
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨inst, leader, rfl⟩ := hm
    obtain ⟨hl, hw, -⟩ := mma_elect_len hpre hX hg hσ rfl
    have := role_elect_event hpre hX hg (j := j) he (by omega)
    omega
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨inst, leader, rfl⟩ := hm
    obtain ⟨hl, hw⟩ := sched_elect_len hpre hX hg hσ rfl
    have := role_elect_event hpre hX hg (j := j) he (by omega)
    omega
  · simp [ThreadD.coll] at hs

/-- **A thread's events before its collective site.** -/
theorem coll_before_fact (hg : g < L.threads) (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩)
    {d : ThreadD} {s : CollSite}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hs : d.coll =
      some s) : s.Before X g := by
  rcases d with ⟨site, w⟩ | (l | ⟨site, w', q, fp, ap, cp, r, x⟩ | ⟨site, ap, cp, r, x⟩ | c)
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
    · have := (pro_end hpre hX hg le_rfl hσ).1
      simp only [Prologue.index] at this
      exact List.eq_nil_of_length_eq_zero this
    · have := (pro_end hpre hX hg le_rfl hσ).1
      simp only [Prologue.index] at this
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp this
      refine ⟨x, hx, ?_⟩
      have h0 := first_event hpre hX hg (e := x) (by change (X.tr g)[0]? = _; rw [hx]; rfl)
      rw [h0]
      rfl
    · obtain ⟨hl, hw0⟩ := wb_end hpre hX hg hσ
      have hja : index L g ⟨.alloc, 0⟩ + 1 ≤ wbIdx L g := by
        simp only [Prologue.index, wbIdx]
        split_ifs <;> omega
      obtain ⟨da, hda⟩ := Frame.stateAt_live (tracked hpre hX) hg hσ (k :=
        index L g ⟨.alloc, 0⟩) (by omega)
      obtain ⟨qa, rfl⟩ : ∃ qa, da = .inl qa := by
        rcases da with qa | r
        · exact ⟨qa, rfl⟩
        · have := (onPath_all hpre hX hg _ (by omega)).2 r hda
          have h2 := wbIdx_lt_wait (L := L) (g := g)
          rw [hw0] at this
          omega
      obtain ⟨h1, h2, hc⟩ := pro_end hpre hX hg (by omega) hda
      have hapos : 0 < index L g ⟨.alloc, 0⟩ := by
        simp only [Prologue.index]
        split_ifs <;> omega
      have hq0 : qa.site ≠ .shfl → qa.w = 0 := fun _ => (h2 hapos).trans hw0
      have hsa := w0_alloc_site hq0 hc h1.symm
      obtain ⟨ea, hea⟩ : ∃ e, (X.tr g)[index L g ⟨.alloc, 0⟩]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨d1, hd1⟩ := Frame.stateAt_live (tracked hpre hX) hg hσ (k := index L g ⟨.alloc, 0⟩ +
        1)
        (by omega)
      have hn := stateAt_succ_inl hea hda
      rw [hd1] at hn
      obtain ⟨site, wa⟩ := qa
      simp only at hsa
      subst hsa
      have hops := (tmem_ops_fact hpre hX hg hnu hda).1
      simp only [ThreadD.tmemOps] at hops
      -- the allocation's event is a resource operation, after which the state is a prologue one
      have hk : ∃ grp dst n, ea.kind = .tc (.resource grp dst (.alloc n)) := by
        simp only [Prologue.next] at hn
        split at hn
        · rename_i grp dst n hk
          exact ⟨grp, dst, n, hk⟩
        · cases hn
      obtain ⟨grp, dst, n, hk⟩ := hk
      obtain ⟨q1, rfl⟩ : ∃ q1, d1 = .inl q1 := by
        simp only [Prologue.next, hk] at hn
        split_ifs at hn <;> exact ⟨_, Option.some.inj (Option.some.inj hn)⟩
      refine ⟨index L g ⟨.alloc, 0⟩, ea.pc, grp, dst, .alloc n, ?_, hops, ?_⟩
      · change (X.tr g)[_]? = _
        rw [hea, ← hk]
      · rcases alloc_cases hn.symm with ⟨hl0, rfl⟩ | ⟨hl0, rfl⟩
        · have hf := first_of_warp_lane hw0 hl0
          right
          refine ⟨by simp [hl, Prologue.index, wbIdx, hf], ?_⟩
          obtain ⟨e1, he1⟩ : ∃ e, (X.tr g)[index L g ⟨.alloc, 0⟩ + 1]? = some e :=
            ⟨_, List.getElem?_eq_getElem (by rw [hl]; simp [Prologue.index, wbIdx, hf])⟩
          obtain ⟨t, ins, o, hat, -, hc1, hf1⟩ := Frame.fired_site (fun _ => sound hpre) hX he1 hd1
          change kernel.code[Prologue.Site.allocWrite.pc]? = some ins at hc1
          obtain rfl := Option.some.inj (hc1.symm.trans Flow.code_tmemAlloc_0)
          have hsub : t.sub = 1 := by rw [hat.2.1]; simp [Prologue.sub]
          obtain ⟨a, bs, he⟩ := fires_tcAlloc_wr hsub hf1
            (fun f h => hnu _ _ f (by change (X.tr g)[_]? = _; rw [he1, h]))
          exact ⟨_, a, bs, by change (X.tr g)[_]? = _; rw [he1, he]⟩
        · have hf : first L g = false := by
            cases h : first L g
            · rfl
            · exact absurd (laneOf_of_first h) hl0
          left
          rw [hl]
          simp [Prologue.index, wbIdx, hf]
    · obtain ⟨hl, hw11⟩ := roleElect_end hpre hX hg hσ
      refine ⟨by omega, ?_⟩
      rw [hl]
      exact role_before hpre hX hg (by omega) (by omega) (by omega)
  · simp [ThreadD.coll] at hs
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨hl, hw, -⟩ := mma_elect_len hpre hX hg hσ rfl
    refine ⟨by omega, ?_⟩
    rw [hl]
    exact role_before hpre hX hg (by omega) (by omega) (by omega)
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨hl, hw⟩ := sched_elect_len hpre hX hg hσ rfl
    refine ⟨by omega, ?_⟩
    rw [hl]
    exact role_before hpre hX hg (by omega) (by omega) (by omega)
  · simp [ThreadD.coll] at hs

end

end
end PTX.Kernels.Fp16Gemm8192.Proof
