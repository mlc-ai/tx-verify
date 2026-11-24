-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Reduce

@[expose] public section

/-! # The machines never stop

A thread's machine stops only where an outcome of its code faults. On the values the threads read
or receive no outcome faults (`next_ne_none`): the input and weight loads read pairs of real
halves (`xOk_fin`), the reloads read the single-precision inputs the threads staged, and their
pairs pack and multiply with the scale factor (`tileOk_fin`); the shuffles receive numbers
(`recv_ok`), so every addition of the butterflies is one of numbers (`addOk_fin`); the reductions'
reads the sums the reductions stored, and the total is a sum of squares, so the scale factor's
operand is positive (`ttOk_fin`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow Finset

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem ssqT_nonneg (P : Params) (g i : Nat) : 0 ≤ ssqT P g i := by
  simp only [ssqT, fmaSum_eq, zero_add]
  exact add_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)

theorem warpW_nonneg (P : Params) (c i w : Nat) : 0 ≤ warpW P c i w :=
  sum_nonneg fun _ _ => ssqT_nonneg P _ i

theorem pos_vbase {g : Nat} {d : D} (h : d.site.vload = true) : d.pos g = d.vbase g + d.sub := by
  rcases hs : d.site <;> simp [hs, Site.vload] at h <;> simp [D.pos, D.vbase, hs]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

omit hpre hX ht in
/-- **The last element of a vector load completes its four values.** -/
theorem acc_full {g j pc : Nat} {d : D} {a : Acc} {bs : List (Option Byte)} {v : Value}
    (he : X.get (g, j) = some ⟨pc, .rd a bs⟩) (hA : At P L X g j d ⟨pc, .rd a bs⟩)
    (hv : d.site.vload = true) (hs : d.sub = 3) (hrb : rebuild 3 bs = .ok v) :
    d.acc ++ [v] = rv4 (X.tr g) (rowBase g d.i + d.vbase g) := by
  have hr : d.site.inRow = true := by
    rcases hsd : d.site <;> simp [hsd, Site.vload] at hv <;> simp [Site.inRow]
  have hj : j = rowBase g d.i + d.vbase g + 3 := by
    rw [hA.index, idx_of_row hr, pos_vbase hv, hs, Nat.add_assoc]
  rw [hA.data.acc hv, hs]
  have h3 : (X.tr g)[rowBase g d.i + d.vbase g + 3]? = some ⟨pc, .rd a bs⟩ := by
    rw [← hj]; exact he
  simp only [rv4, List.getElem?_take, List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  rw [ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'),
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'),
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'), h3]
  simp [rdv, hrb]

omit hpre hX ht in
/-- A vector load whose element's bytes rebuild, and whose continuation accepts its four values,
does not stop. -/
theorem loadNext_ne_none {d : D} {pc : Nat} {a : Acc} {bs : List (Option Byte)} {v : Value}
    {k : List Value → Option D} (hrb : rebuild 3 bs = .ok v) (hsub : d.sub < 4)
    (hk : d.sub = 3 → k (d.acc ++ [v]) ≠ none) : loadNext d ⟨pc, .rd a bs⟩ k ≠ none := by
  unfold loadNext
  simp only [hrb]
  split_ifs with h
  · simp
  · intro hn
    exact hk (by omega) (Option.map_eq_none_iff.mp hn)

/-- The running sum of a lane in round `k` of the warp's butterfly reads as a number. -/
theorem bfa_val {g j : Nat} {d : D} {e : Event} (he : X.get (g, j) = some e)
    (hA : At P L X g j d e) {k : Nat} (hs : d.site = .bfa k) :
    ∃ y, valFloat .f32 (bsumV (ssqV d) d.ra k) = .ok y := by
  have hr : d.site.inRow = true := by simp [hs, Site.inRow]
  have hk5 := hA.inv.bfa k hs
  have hp : d.pos g = 24 + k := by simp [D.pos, hs]
  rw [ssq_eq hpre hX ht he hA hr (by omega)]
  exact ⟨_, bsumV_fin (valFloat_fl _) k fun k' hk' =>
    ra_eq hpre hX ht k' (by omega) he hA hr (by omega)⟩

/-- The running sum of a lane in round `k` of warp 0's butterfly reads as a number. -/
theorem bfb_val {g j : Nat} {d : D} {e : Event} (he : X.get (g, j) = some e)
    (hA : At P L X g j d e) {k : Nat} (hs : d.site = .bfb k) :
    ∃ y, valFloat .f32 (bsumV d.u d.rb k) = .ok y := by
  have hr : d.site.inRow = true := by simp [hs, Site.inRow]
  obtain ⟨hk5, h32⟩ := hA.inv.bfb k hs
  have hp : d.pos g = 30 + l0 g + l8 g + k := by simp [D.pos, hs]
  exact ⟨_, bsumV_fin (u_val hpre hX ht he hA hr h32 (by omega)) k fun k' hk' =>
    rb_eq hpre hX ht k' (by omega) he hA hr h32 (by omega)⟩

/-- The received value of a round of a butterfly reads as single precision. -/
theorem recv_ok {g j pc : Nat} {d : D} {m : ShflMode} {a : Value} {b c : Nat} {recv : Value}
    {ok : Bool} (he : X.get (g, j) = some ⟨pc, .shfl m a b c recv ok⟩)
    (hA : At P L X g j d ⟨pc, .shfl m a b c recv ok⟩) (hs : d.site ≠ .shfl0) :
    ∃ y, valFloat .f32 recv = .ok y := by
  have hsh := isShfl_of_event hA.event
  obtain ⟨ks, ds, pcs, bs, cs, rs, os, hes, hAs, hss, his⟩ := round_source hpre hX ht he hA hsh hs
  rcases shfl_site hAs.event with ⟨h, -⟩ | ⟨k, h, -, h2, -⟩ | ⟨k, h, -, h2, -⟩
  · exact absurd (hss.symm.trans h) hs
  · rw [h2]; exact bfa_val hpre hX ht hes hAs h
  · rw [h2, bfbOp]; exact bfb_val hpre hX ht hes hAs h

/-- A store or barrier site steps. -/
macro "dead_plain" hs:ident : tactic => `(tactic| (
  simp only [next, $hs:ident, storeNext]
  (try split_ifs) <;> simp))

/-- **The machine of a thread does not stop** at an event of its site. -/
theorem next_ne_none {g j : Nat} {d : D} {e : Event} (he : X.get (g, j) = some e)
    (hA : At P L X g j d e) (hx : d.site ≠ .exit) : next P g d e ≠ none := by
  have hsub := hA.inv.sub.1
  have hld : d.site.isLoad = true → ∃ pc a bs, e = ⟨pc, .rd a bs⟩ := rd_event hA.event
  have hsh : d.site.isShfl = true → ∃ pc m a b c recv ok, e = ⟨pc, .shfl m a b c recv ok⟩ :=
    shfl_event hA.event
  rcases hs : d.site with _ | _ | _ | _ | _ | _ | _ | k | _ | _ | _ | k | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ <;>
    simp only [hs, Site.isLoad, Site.isShfl, Site.vec, forall_const, ne_eq, reduceCtorEq,
      not_false_eq_true, Bool.false_eq_true, false_implies] at hld hsh hsub hx <;>
    (try have hr : d.site.inRow = true := by simp [hs, Site.inRow])
  · simp only [next, hs]; split_ifs <;> simp
  · -- the first input load
    obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := ldx_bytes hpre hX ht he hA (.inl ⟨hs, rfl⟩)
    have hrb : rebuild 3 bs =
        .ok (hpair (xin P g d.i 0 (2 * d.sub)) (xin P g d.i 0 (2 * d.sub + 1))) := by
      rw [hb]; exact rebuild_hpair _ _
    simp only [next, hs]
    apply loadNext_ne_none hrb hsub
    intro h3 hk
    rw [acc_full he hA (by simp [hs, Site.vload]) h3 hrb] at hk
    simp only [D.vbase, hs] at hk
    have hp : d.pos g = 3 := by simp [D.pos, hs, h3]
    have hq : 0 + 3 ≤ d.pos g := by omega
    rw [xwords_eq hpre hX ht he hA hr (t := 0) (q := 0) (.inl ⟨rfl, rfl⟩) hq] at hk
    split_ifs at hk with hT
    exact hT (xOk_fin (xin P g d.i 0) valFloat_z0)
  · dead_plain hs
  · dead_plain hs
  · -- the second input load
    obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := ldx_bytes hpre hX ht he hA (.inr ⟨hs, rfl⟩)
    have hrb : rebuild 3 bs =
        .ok (hpair (xin P g d.i 1 (2 * d.sub)) (xin P g d.i 1 (2 * d.sub + 1))) := by
      rw [hb]; exact rebuild_hpair _ _
    simp only [next, hs]
    apply loadNext_ne_none hrb hsub
    intro h3 hk
    rw [acc_full he hA (by simp [hs, Site.vload]) h3 hrb] at hk
    simp only [D.vbase, hs] at hk
    have hp : d.pos g = 15 := by simp [D.pos, hs, h3]
    have hq : 12 + 3 ≤ d.pos g := by omega
    rw [xwords_eq hpre hX ht he hA hr (t := 1) (q := 12) (.inr ⟨rfl, rfl⟩) hq,
      xa_eq hpre hX ht he hA hr (by omega)] at hk
    split_ifs at hk with hT
    exact hT (xOk_fin (xin P g d.i 1)
      (fmaRun_fin (fun m hm => xw_xwords P g d.i 0 hm) valFloat_z0 8 le_rfl))
  · dead_plain hs
  · dead_plain hs
  · -- a round of the warp's butterfly
    obtain ⟨pc, m, a, b, c, recv, ok, rfl⟩ := hsh
    obtain ⟨y, hy⟩ := recv_ok hpre hX ht he hA (by rw [hs]; simp)
    obtain ⟨x, hx⟩ := bfa_val hpre hX ht he hA hs
    simp [next, hs, addOk_fin hx hy]
  · dead_plain hs
  · dead_plain hs
  · -- warp 0's load of a warp sum
    obtain ⟨pc, a, bs, rfl⟩ := hld
    obtain ⟨kx, dx, pcx, hex, hAx, hsx, -, hbs⟩ := ldws_bytes hpre hX ht he hA hs
    rw [warp_sum hpre hX ht hex hAx hsx] at hbs
    simp only [next, hs, hbs, rebuild_fl]
    simp [fl, Value.bytes, FloatFmt.bytes]
  · -- a round of warp 0's butterfly
    obtain ⟨pc, m, a, b, c, recv, ok, rfl⟩ := hsh
    obtain ⟨y, hy⟩ := recv_ok hpre hX ht he hA (by rw [hs]; simp)
    obtain ⟨x, hx⟩ := bfb_val hpre hX ht he hA hs
    simp [next, hs, addOk_fin hx hy]
  · dead_plain hs
  · dead_plain hs
  · -- the load of the total
    obtain ⟨pc, a, bs, rfl⟩ := hld
    obtain ⟨kx, dx, pcx, hex, hAx, hsx, -, hbs⟩ := ldts_bytes hpre hX ht he hA hs
    rw [cta_total hpre hX ht hex hAx hsx, show 256 * (g / 256) / 256 = g / 256 by omega] at hbs
    have hpos : 0 < (∑ w ∈ range 8, warpW P (g / 256) dx.i w) / c4096 + eps := by
      rw [c4096_eq]
      have := sum_nonneg fun w (_ : w ∈ range 8) => warpW_nonneg P (g / 256) dx.i w
      have := eps_pos
      positivity
    simp only [next, hs, hbs, rebuild_fl, ttOk_fin hpos]
    simp
  · obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := ldw_bytes hpre hX ht he hA (.inl ⟨hs, rfl⟩)
    simp only [next, hs]
    exact loadNext_ne_none (by rw [hb]; exact rebuild_hpair _ _) hsub fun _ => by simp
  · obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := lds_bytes hpre hX ht he hA (.inl ⟨hs, rfl, rfl⟩)
    simp only [next, hs]
    exact loadNext_ne_none (by rw [hb]; exact rebuild_fl _) hsub fun _ => by simp
  · -- the second reload of tile 0
    obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := lds_bytes hpre hX ht he hA (.inr (.inl ⟨hs, rfl, rfl⟩))
    have hrb : rebuild 3 bs = .ok (fl (xin P g d.i 0 (4 * 1 + d.sub))) := by
      rw [hb]; exact rebuild_fl _
    simp only [next, hs]
    apply loadNext_ne_none hrb hsub
    intro h3 hk
    have hj : j = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
    have hp : d.pos g = p1 g + 13 := by simp [D.pos, hs, h3]
    rw [acc_full he hA (by simp [hs, Site.vload]) h3 hrb] at hk
    simp only [D.vbase, hs] at hk
    have q1 : p1 g + 6 ≤ d.pos g := by omega
    have q2 : d.pos g < p1 g + 18 := by omega
    have q3 : p1 g + 10 ≤ d.pos g := by omega
    have q4 : d.pos g < p1 g + 26 := by omega
    have q5 : rowBase g d.i + p1 g + 2 + 4 ≤ j := by omega
    have q6 : rowBase g d.i + p1 g + 6 + 4 ≤ j := by omega
    rw [hA.data.rawa hr q1 q2, hA.data.rs0a hr q3 q4, rv4_take _ q5, rv4_take _ q6] at hk
    have q7 : p1 g + 2 + 3 ≤ d.pos g := by omega
    have q8 : p1 g + 6 + 3 ≤ d.pos g := by omega
    have q9 : p1 g + 10 + 3 ≤ d.pos g := by omega
    have h1 := wwords_eq hpre hX ht he hA hr (t := 0) (.inl ⟨rfl, rfl⟩) q7
    have h2 := lds_vals hpre hX ht he hA hr (t := 0) (h := 0) (.inl ⟨rfl, rfl, rfl⟩) q8
    have h3' := lds_vals hpre hX ht he hA hr (t := 0) (h := 1) (.inr (.inl ⟨rfl, rfl, rfl⟩)) q9
    simp only [← Nat.add_assoc, Nat.mul_zero, Nat.zero_add] at h1 h2
    simp only [Nat.mul_one, Nat.reduceAdd] at h3'
    have hpos := tt_pos P (row g d.i)
    rw [h1, h2, h3', tt_eq hpre hX ht he hA hr (by omega), cpair_fin hpos] at hk
    split_ifs at hk with hT
    exact hT (tileOk_fin (win P g 0) (xin P g d.i 0) _)
  · dead_plain hs
  · obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := ldw_bytes hpre hX ht he hA (.inr ⟨hs, rfl⟩)
    simp only [next, hs]
    exact loadNext_ne_none (by rw [hb]; exact rebuild_hpair _ _) hsub fun _ => by simp
  · obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := lds_bytes hpre hX ht he hA (.inr (.inr (.inl ⟨hs, rfl, rfl⟩)))
    simp only [next, hs]
    exact loadNext_ne_none (by rw [hb]; exact rebuild_fl _) hsub fun _ => by simp
  · -- the second reload of tile 1
    obtain ⟨pc, a, bs, rfl⟩ := hld
    have hb := lds_bytes hpre hX ht he hA (.inr (.inr (.inr ⟨hs, rfl, rfl⟩)))
    have hrb : rebuild 3 bs = .ok (fl (xin P g d.i 1 (4 * 1 + d.sub))) := by
      rw [hb]; exact rebuild_fl _
    simp only [next, hs]
    apply loadNext_ne_none hrb hsub
    intro h3 hk
    have hj : j = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
    have hp : d.pos g = p1 g + 29 := by simp [D.pos, hs, h3]
    rw [acc_full he hA (by simp [hs, Site.vload]) h3 hrb] at hk
    simp only [D.vbase, hs] at hk
    have q1 : p1 g + 22 ≤ d.pos g := by omega
    have q3 : p1 g + 26 ≤ d.pos g := by omega
    have q5 : rowBase g d.i + p1 g + 18 + 4 ≤ j := by omega
    have q6 : rowBase g d.i + p1 g + 22 + 4 ≤ j := by omega
    rw [hA.data.rawb hr q1, hA.data.rs0b hr q3, rv4_take _ q5, rv4_take _ q6] at hk
    have q7 : p1 g + 18 + 3 ≤ d.pos g := by omega
    have q8 : p1 g + 22 + 3 ≤ d.pos g := by omega
    have q9 : p1 g + 26 + 3 ≤ d.pos g := by omega
    have h1 := wwords_eq hpre hX ht he hA hr (t := 1) (.inr ⟨rfl, rfl⟩) q7
    have h2 := lds_vals hpre hX ht he hA hr (t := 1) (h := 0)
      (.inr (.inr (.inl ⟨rfl, rfl, rfl⟩))) q8
    have h3' := lds_vals hpre hX ht he hA hr (t := 1) (h := 1) (.inr (.inr (.inr ⟨rfl, rfl, rfl⟩)))
      q9
    simp only [← Nat.add_assoc, Nat.mul_zero, Nat.zero_add] at h1 h2
    simp only [Nat.mul_one, Nat.reduceAdd] at h3'
    have hpos := tt_pos P (row g d.i)
    rw [h1, h2, h3', tt_eq hpre hX ht he hA hr (by omega), cpair_fin hpos] at hk
    split_ifs at hk with hT
    exact hT (tileOk_fin (win P g 1) (xin P g d.i 1) _)
  · dead_plain hs
  · dead_plain hs
  · exact absurd trivial hx

end
end PTX.Kernels.RmsNorm.Proof
