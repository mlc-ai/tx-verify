-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Poll
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # Warpgroup 0's barrier lag on the time table

A lane of warps 0–3 with at most `B` role barrier events (`B ≤ 3 R + 6`, the ordinal of barrier
12) has not exited (its `exit` follows all `3 R + 7`) and its time is at most the place of its
`B`-th barrier site (`w0_lagB`: its states are at most at their next barrier's place,
`Wg0.place_barPlace`). A role barrier event of such a lane is at that place of its count, on the
barrier `Wg0.idAt` of its count (`w0_atBar`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g y : Nat}

/-- The time of a warpgroup-0 state is its place from `wg0Org`. -/
theorem w0_time (d : (wg0Code P L y (warpW L y)).D) (n : Cls → Nat) :
    time P L y (.inr ⟨.inl .wg0, d⟩, n) = wg0Org + Wg0.place d := by
  simp only [time, fragTime, wg0Time, Wg0.time, roleBase, wg0Org]

/-- No startup state fires an `exit`. -/
theorem start_noExit {d : Startup.D} {e : Event} (hx : Startup.exitOf d = none)
    (hev : Startup.Ev L g d e) (hk : e.kind = .exit) : False := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | enter r => simp [Startup.exitOf] at hx
  | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hev <;> rw [hk] at h <;> cases h
  | elect j => obtain ⟨i, l, -, h⟩ := hev; rw [hk] at h; cases h
  | ld => rcases hev with ⟨a, bs, h, -⟩ | ⟨f, h⟩ <;> rw [hk] at h <;> cases h
  | allocSt => obtain ⟨c, -, h⟩ := hev; rw [hk] at h; cases h
  | _ => simp only [Startup.Ev] at hev; rw [hk] at hev; cases hev

/-- **A lane of warps 0–3 with at most `B` role barrier events** (`B ≤ 3 R + 6`) has not exited
and is no later than its `B`-th barrier site. -/
theorem w0_lagB (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) (hy : y < L.threads) {B : Nat}
    (hB : B ≤ 3 * blocksOf P L (y / L.block) + 6) (hle : w0BarCnt X y (X.tr y).length ≤ B)
    (hal : LaneUbFree X y (X.tr y).length) :
    (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X y ≤ wg0Org + Wg0.barPlace (blocksOf P L (y / L.block)) B := by
  have hmono : ∀ i, i ≤ (X.tr y).length → w0BarCnt X y i ≤ B := fun i hi => by
    refine Nat.le_trans ?_ hle
    simp only [w0BarCnt, Wg0.barTot]
    have := fun c => count_take_mono (X := X) (g := y) (Wg0.cls c) hi
    have h9 := this (.bar 9)
    have h10 := this (.bar 10)
    have h11 := this (.bar 11)
    have h12 := this (.bar 12)
    omega
  have h26 : blocksOf P L (y / L.block) < 2 ^ 26 :=
    Proof.Wg0.rounds_lt (lenWA P L (y / L.block)) (lenWB P L (y / L.block))
  have hbase : 100 ≤ wg0Org + Wg0.barPlace (blocksOf P L (y / L.block)) B := by
    simp only [wg0Org]; omega
  refine ⟨fun k pc hx => ?_, ?_⟩
  · obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw hx (fun _ h => by cases h)
    rcases w0_bst_pre hFw (hal.mono (List.getElem?_eq_some_iff.mp hx).1.le) hw hy hσ with
      ⟨d, n, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -, ht⟩
    · exact start_noExit hxd hev rfl
    · obtain ⟨-, hK⟩ : Wg0.Ev P L y (warpW L y) d ⟨pc, .exit⟩ := hev
      have hs := Proof.Wg0.evK_exit hK rfl
      have hR := Wg0.rounds_blocks hL (by rw [hs]; decide)
      have ho : Wg0.barOrd d = 3 * blocksOf P L (y / L.block) + 7 := by
        simp only [Wg0.barOrd, hs, Wg0.Site.reg, Wg0.Site.bidx, hR]
      have := hmono k (List.getElem?_eq_some_iff.mp hx).1.le
      simp only [w0BarCnt] at this
      dsimp only at ht
      omega
  refine time_last (Q := fun t => t ≤ wg0Org + Wg0.barPlace (blocksOf P L (y / L.block)) B)
    (by omega) (fun σ hs => ?_) (fun σ f hs hf _ => ?_)
  · rcases w0_bst_pre hFw hal hw hy hs with ⟨d, n, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -, ht⟩
    · have := Startup.time_lt hxd
      simp only [time] at this ⊢
      omega
    · obtain ⟨h1, -, -⟩ := Wg0.place_barPlace hC hL
      have hB' := hmono _ (Nat.le_refl _)
      simp only [w0BarCnt] at hB'
      have := Wg0.barPlace_mono (R := blocksOf P L (y / L.block)) h26
        (show Wg0.barOrd d ≤ B by omega) (by omega)
      rw [w0_time]
      split_ifs at h1 <;> omega
  · have hget : X.get (y, (X.tr y).length - 1) = some f := hf
    have hlen := (List.getElem?_eq_some_iff.mp hf).1
    have hub : ∀ u, f.kind ≠ .ub u := NoUbBefore.ne hal (by omega) hget
    have hpos : 0 < (X.tr y).length := by
      have := (List.getElem?_eq_some_iff.mp hf).1
      omega
    have hub : ∀ u, f.kind ≠ .ub u := NoUbBefore.ne hal (by omega) hget
    obtain ⟨σ', hσ', -, -, hev, -⟩ := ev_at hp hX hFw hget hub
    rw [hs] at hσ'
    cases hσ'
    rcases w0_bst_pre hFw (hal.mono (Nat.sub_le _ _)) hw hy hs with
      ⟨d, n, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -, ht⟩
    · have := Startup.time_lt hxd
      simp only [time] at this ⊢
      omega
    · obtain ⟨h1, h2, -⟩ := Wg0.place_barPlace hC hL
      have hB' := hmono ((X.tr y).length - 1) (by omega)
      simp only [w0BarCnt] at hB'
      rw [w0_time]
      cases hsb : d.site.isBar
      · simp only [hsb, Bool.false_eq_true, ↓reduceIte] at h1
        have := Wg0.barPlace_mono (R := blocksOf P L (y / L.block)) h26
          (show Wg0.barOrd d ≤ B by omega) (by omega)
        omega
      · obtain ⟨h3, h4⟩ := h2 hsb
        obtain ⟨-, hK⟩ := hev
        have hb := Wg0.evK_barSite hsb hub hK
        have hlast := hmono _ (Nat.le_refl _)
        have hstep : w0BarCnt X y (X.tr y).length = w0BarCnt X y ((X.tr y).length - 1) + 1 := by
          obtain ⟨c, hk⟩ := Wg0.bar_kind hub hK hb hC hL
          rw [Wg0.barW_warp hp, Nat.add_sub_cancel_left] at hk
          have hI := Wg0.idAt_range (blocksOf P L (y / L.block)) (Wg0.barOrd d)
            (Nat.mod_lt (warp L y) (show 0 < 2 by omega))
          generalize Wg0.idAt (blocksOf P L (y / L.block)) (warp L y % 2) (Wg0.barOrd d) = I
            at hk hI
          have hr : Wg0.inRole f = true := by
            rcases wg0_barRole hp hX hFw hw hget hb with hlo | hr
            · obtain ⟨-, hk'⟩ := barRow_startup hp hX hFw (Frame.lt_of_get hX hget) hget hlo hb
              have hk'' : f.kind = .bar 0 none .sync := hk'
              rw [hk] at hk''
              simp only [Kind.bar.injEq] at hk''
              omega
            · exact hr
          have hcl : ∀ j, Wg0.cls (.bar j) f = decide (I = j) := fun j => by
            simp [Wg0.cls, Wg0.kindOf, hk, hr]
          have hT : ∀ c : Event → Bool, ((X.tr y).take (X.tr y).length).countP c =
              ((X.tr y).take ((X.tr y).length - 1)).countP c + if c f then 1 else 0 := fun c => by
            conv => lhs; rw [show (X.tr y).length = (X.tr y).length - 1 + 1 by omega]
            rw [List.take_add_one, hf, Option.toList_some, List.countP_append]
            simp [List.countP_singleton]
          simp only [w0BarCnt, Wg0.barTot, hT, hcl, decide_eq_true_eq]
          split_ifs <;> omega
        simp only [w0BarCnt] at hlast hstep
        have := Wg0.barPlace_lt (R := blocksOf P L (y / L.block)) h26
          (show Wg0.barOrd d < B by omega) h4
        omega


/-- **A role barrier event of a lane of warps 0–3** is at the place of its count, which is at most
`3 R + 6`, on the barrier of its count. -/
theorem w0_atBar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j pc id : Nat}
    {cnt : Option Nat} {md : BarMode} {σ : (thread P L g).D}
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) (h103 : 103 ≤ pc)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ)) :
    time P L g σ = wg0Org + Wg0.barPlace (blocksOf P L (g / L.block)) (w0BarCnt X g j) ∧
      w0BarCnt X g j ≤ 3 * blocksOf P L (g / L.block) + 6 ∧
      id = Wg0.idAt (blocksOf P L (g / L.block)) (warp L g % 2) (w0BarCnt X g j) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, Kind.bar id cnt md ≠ .ub f := fun _ h => by cases h
  have hr : 103 ≤ pc ∧ pc < 1842 := by
    rcases wg0_barRole hp hX hFw hw he rfl with h | h
    · simp only at h; omega
    · simp only [Wg0.inRole, decide_eq_true_eq] at h; omega
  obtain ⟨σ', hσ', hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ'
  cases hσ'
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc' hr
  rcases w0_bst_pre hFw (noUbBefore_of_get hX he) hw hg hσ with
      ⟨d', n', h, -⟩ | ⟨d', n', h, hC, hL, -, ht⟩
  · cases h
  cases h
  obtain ⟨-, hK⟩ := hE
  have hsb : d.site.isBar = true := Proof.Wg0.isBar_of_pc ((Proof.Wg0.evK_bar hub hK rfl).imp
    (fun h => h.1) fun h => h.imp (fun h => h.1) fun h => h.1)
  obtain ⟨c, hk⟩ := Wg0.bar_kind hub hK rfl hC hL
  rw [Wg0.barW_warp hp, Nat.add_sub_cancel_left] at hk
  simp only [Kind.bar.injEq] at hk
  obtain ⟨-, h2, -⟩ := Wg0.place_barPlace hC hL
  obtain ⟨h3, h4⟩ := h2 hsb
  have hB : w0BarCnt X g j = Wg0.barOrd d := ht
  rw [w0_time, hB]
  exact ⟨by rw [h3], h4, hk.1⟩

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- Barriers 9 and 12 are at the same ordinals for both parities. -/
theorem w0IdCnt_par {R id B p p' : Nat} (hid : id = 9 ∨ id = 12) (hp : p < 2) (hp' : p' < 2) :
    w0IdCnt R p id B = w0IdCnt R p' id B := by
  unfold w0IdCnt
  congr 1
  refine List.filter_congr fun o _ => ?_
  unfold Wg0.idAt
  split_ifs <;> simp only [decide_eq_decide] <;> omega

/-- **The lag at a role barrier of warpgroup 0**: a lane `y` of warps 0–3 of the CTA with no more
events on the barrier than `g` before its event (barrier 9, 12, or the pair's of the same parity)
has not exited and is no later than `g`'s state. -/
theorem w0_lagId (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hay : LaneUbFree X y (X.tr y).length) (hy : y < L.threads)
    (hc : y / L.block = g / L.block)
    (hwg : warp L g < 4) (hwy : warp L y < 4) {j pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (hid : id = 9 ∨ id = 12 ∨ warp L y % 2 = warp L g % 2) {σ : (thread P L g).D}
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) (h103 : 103 ≤ pc)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ))
    (hle : (X.tr y).countP (Execution.isBarId id) ≤
      ((X.tr g).take j).countP (Execution.isBarId id)) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (timed P L) X y ≤ time P L g σ := by
  obtain ⟨ht, hB, hI⟩ := w0_atBar hp hX hFw hwg he h103 hσ
  have hI' := Wg0.idAt_range (blocksOf P L (g / L.block)) (w0BarCnt X g j)
    (Nat.mod_lt (warp L g) (show 0 < 2 by omega))
  rw [← hI] at hI'
  have hcy := w0_idCnt hp hX hFw hwy hI'.1 hI'.2 (X.tr y).length
    hay
  rw [List.take_length, hc] at hcy
  have hcg := w0_idCnt hp hX hFw hwg hI'.1 hI'.2 j
    (noUbBefore_of_get hX he)
  have hpar : ∀ B, w0IdCnt (blocksOf P L (g / L.block)) (warp L y % 2) id B =
      w0IdCnt (blocksOf P L (g / L.block)) (warp L g % 2) id B := fun B => by
    rcases hid with h | h | h
    · exact w0IdCnt_par (.inl h) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    · exact w0IdCnt_par (.inr h) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    · rw [h]
  rw [hpar] at hcy
  have hBy : w0BarCnt X y (X.tr y).length ≤ w0BarCnt X g j := by
    by_contra hlt
    have h1 := w0IdCnt_mono (R := blocksOf P L (g / L.block)) (p := warp L g % 2) (id := id)
      (show w0BarCnt X g j + 1 ≤ w0BarCnt X y (X.tr y).length by omega)
    rw [w0IdCnt_succ] at h1
    split_ifs at h1 with hh
    · omega
    · exact hh hI.symm
  have hR : blocksOf P L (y / L.block) = blocksOf P L (g / L.block) := by rw [hc]
  obtain ⟨hx, htm⟩ := w0_lagB hp hX hFw hwy hy (B := w0BarCnt X g j) (by rw [hR]; exact hB)
    hBy (hay)
  rw [hR] at htm
  exact ⟨hx, ht ▸ htm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
