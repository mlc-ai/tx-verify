-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaSegs

@[expose] public section

/-! # The loop's control code as segments between sites

The local code that follows an event of the MMA warp and ends at the next event is a chain of
the straight-line pieces of `MmaSegs` and conditional branches on the predicates of the loop
(`%p6`, `%p7`, `%p12`, `%p17`), whose values the table gives. Three composite segments cover
every continuation:

* `seg_iter`: from the end of an iteration (`pc 2447`) to the top of the next one (`iterNext`);
* `seg_afterQk`: from the end of the QK half (`pc 2500`) to the PV half or the next iteration;
* `seg_start`: from `barrier.sync 1` to the first iteration or the end of the loop. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D}

theorem holds_live' {R : Nat → Option Value} {pc pc' : Nat} {d d' : D}
    (h : Holds R (factsAt L pc d)) (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc)
    (hv : ∀ r ∈ Flow.live pc', valueOf L d r = valueOf L d' r) :
    Holds R (factsAt L pc' d') := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  rw [← hv r hr]
  exact holds_mem h (Flow.mem_factsFrom (hl r hr))

/-- The membership of a register's value in the facts at a pc. -/
theorem fact_mem {pc r : Nat} {d : D} {v : Value} (hv : valueOf L d r = v)
    (hl : r ∈ Flow.live pc) : (r, v) ∈ factsAt L pc d :=
  hv ▸ Flow.mem_factsFrom hl

/-- The registers the prologue set, which this role carries (and `%r2`, `%r3`, `%r73`, which its
table values). -/
def common : List Nat :=
  [3, 462, 463, 464, 465, 466, 528, 529, 530, 531, 532, 534, 1949, 2020]

/-- The common registers have the same value in two states with the same Tensor Memory base
and prologue registers. -/
theorem valueOf_common {d d' : D} (ht : d.tm = d'.tm) (hp : d.pro = d'.pro) {r : Nat}
    (hr : r ∈ common) : valueOf L d r = valueOf L d' r := by
  simp only [common, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none,
    ht, hp]

/-- The facts at a pc whose live registers are common do not depend on the loop state. -/
theorem holds_common {R : Nat → Option Value} {pc pc' : Nat} {d d' : D}
    (h : Holds R (factsAt L pc d)) (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc)
    (hc : ∀ r ∈ Flow.live pc', r ∈ common) (ht : d.tm = d'.tm) (hp : d.pro = d'.pro) :
    Holds R (factsAt L pc' d') :=
  holds_live' h hl fun r hr => valueOf_common ht hp (hc r hr)

/-! ### The end of an iteration -/

theorem env_succ {d : D} (hd : Env L d) (hin : d.i ≤ d.n) : Env L { d with i := d.i + 1 } :=
  ⟨hd.sb, hd.n, by simp only; have := hd.n; omega, hd.tm, hd.wd⟩

theorem iterNext_fin (he : d.i = d.n) : iterNext d = { d with site := .finBar, i := d.i + 1 } := by
  simp [iterNext, he]

theorem iterNext_qk (he : d.i ≠ d.n) (hq : d.i + 1 < d.n) :
    iterNext d = { d with site := .qkBar, i := d.i + 1 } := by
  simp [iterNext, he, hq]

theorem iterNext_pv (he : d.i ≠ d.n) (hq : ¬ d.i + 1 < d.n) :
    iterNext d = { d with site := .pvBar, i := d.i + 1 } := by
  simp [iterNext, he, hq]

/-- **The end of iteration `i`** (`pc 2447`): the increments and the loop test lead to the end of
the loop (`i = n`), the top of the next iteration's QK half (`i + 1 < n`), or its PV half. -/
theorem seg_iter (hd : Env L d) (hin : d.i ≤ d.n) :
    SegE L g 2447 (factsAt L 2447 d) (iterNext d).site.pc (facts L (iterNext d)) := by
  have h1 := s_incr (g := g) hd hin
  have hd1 := env_succ hd hin
  by_cases he : d.i = d.n
  · have hp : (17, Value.pred false) ∈ factsAt L 2454 { d with i := d.i + 1 } :=
      fact_mem (by ink_values; simp [he]) (by table_decide)
    have h2 := seg_nbraT (L := L) (g := g) Flow.code_2454 hp
    rw [iterNext_fin he]
    refine (h1.comp h2).weaken_end fun R hR => ?_
    exact holds_common hR (by table_decide) (by table_decide) rfl rfl
  · have hp : (17, Value.pred true) ∈ factsAt L 2454 { d with i := d.i + 1 } :=
      fact_mem (by ink_values; simp; omega) (by table_decide)
    have h2 := seg_nbraF (L := L) (g := g) Flow.code_2454 hp
    have h3 := (s_p7 (g := g) hd1).live_start (s' := 2454) (d := { d with i := d.i + 1 }) rfl
      (by table_decide)
    have h12 := (h1.comp h2).comp h3
    by_cases hq : d.i + 1 < d.n
    · have hp7 : (7, Value.pred false) ∈ factsAt L 2456 { d with i := d.i + 1 } :=
        fact_mem (by ink_values; simp; omega) (by table_decide)
      have h4 := seg_braF (L := L) (g := g) Flow.code_2456 hp7
      have h5 := (s_top (g := g) hd1).live_start (s' := 2456) (d := { d with i := d.i + 1 }) rfl
        (by table_decide)
      rw [iterNext_qk he hq]
      exact h12.comp (h4.comp h5)
    · have hp7 : (7, Value.pred true) ∈ factsAt L 2456 { d with i := d.i + 1 } :=
        fact_mem (by ink_values; simp; omega) (by table_decide)
      have h4 := seg_braT (L := L) (g := g) Flow.code_2456 hp7
      have h5 := (s_p12 (g := g) hd1).live_start (s' := 2456) (d := { d with i := d.i + 1 }) rfl
        (by table_decide)
      have hp12 : (12, Value.pred false) ∈ factsAt L 2501 { d with i := d.i + 1 } :=
        fact_mem (by ink_values; simp) (by table_decide)
      have h6 := seg_braF (L := L) (g := g) Flow.code_2501 hp12
      have h7 := (s_pvtail (g := g) hd1 (by simp)).live_start (s' := 2501)
        (d := { d with i := d.i + 1 }) rfl (by table_decide)
      rw [iterNext_pv he hq]
      exact h12.comp (h4.comp (h5.comp (h6.comp h7)))

/-! ### The end of the QK half -/

theorem afterQk_zero (h0 : d.i = 0) : afterQk d = iterNext d := by simp [afterQk, h0]

theorem afterQk_pos (h0 : d.i ≠ 0) : afterQk d = { d with site := .pvBar } := by
  simp [afterQk, h0]

/-- **The end of the QK half** (`pc 2500`, iteration `i < n`): the PV half of the same
iteration, or, in iteration 0, the next iteration. -/
theorem seg_afterQk (hd : Env L d) (hlt : d.i < d.n) :
    SegE L g 2500 (factsAt L 2500 d) (afterQk d).site.pc (facts L (afterQk d)) := by
  have h1 := s_p12 (g := g) hd
  by_cases h0 : d.i = 0
  · have hp : (12, Value.pred true) ∈ factsAt L 2501 d :=
      fact_mem (by ink_values; simp [h0]) (by table_decide)
    have h2 := seg_braT (L := L) (g := g) Flow.code_2501 hp
    have h3 := (seg_iter (g := g) hd hlt.le).live_start (s' := 2501) (d := d) rfl
      (by table_decide)
    rw [afterQk_zero h0]
    exact (h1.comp h2).comp h3
  · have hp : (12, Value.pred false) ∈ factsAt L 2501 d :=
      fact_mem (by ink_values; simp [h0]) (by table_decide)
    have h2 := seg_braF (L := L) (g := g) Flow.code_2501 hp
    have h3 := (s_pvtail (g := g) hd (by omega)).live_start (s' := 2501) (d := d) rfl
      (by table_decide)
    rw [afterQk_pos h0]
    exact (h1.comp h2).comp h3

/-! ### The start of the loop -/

/-- **The start** (`pc 2425`, after `barrier.sync 1`): the first iteration's QK half, or the end
of the loop when `num_iters` is zero or not below `2 ^ 31 - 1`. -/
theorem seg_start (hsb : L.sharedBase + 213340 ≤ 2 ^ 18) (hw : Raw.word32Of (d.pro 471) = some d.n)
    (hi : d.i = 0) (htm : d.tm + 512 < 2 ^ 32) :
    SegE L g 2425 (factsAt L 2425 d) (start d).site.pc (facts L (start d)) := by
  have h1 := s_p6 (L := L) (g := g) (d := d) hw
  by_cases h6 : 2147483646 < d.n
  · have hp : (6, Value.pred true) ∈ factsAt L 2426 d :=
      fact_mem (by ink_values; simp [h6]) (by table_decide)
    have h2 := seg_braT (L := L) (g := g) Flow.code_2426 hp
    have hs : start d = { d with site := .finBar } := by simp [start, h6]
    rw [hs]
    exact (h1.comp h2).weaken_end fun R hR =>
      holds_site (pc' := Site.finBar.pc) hR (by table_decide)
  · have hd : Env L d := ⟨hsb, by omega, by omega, htm, hw⟩
    have hp : (6, Value.pred false) ∈ factsAt L 2426 d :=
      fact_mem (by ink_values; simp [h6]) (by table_decide)
    have h2 := seg_braF (L := L) (g := g) Flow.code_2426 hp
    have h3 := (s_init (g := g) hd hi).live_start (s' := 2426) (d := d) rfl (by table_decide)
    have h4 := (s_p7 (g := g) hd).live_start (s' := 2455) (d := d) rfl (by table_decide)
    have h5 := ((h1.comp h2).comp h3).comp h4
    by_cases h0 : d.n = 0
    · have hp7 : (7, Value.pred true) ∈ factsAt L 2456 d :=
        fact_mem (by ink_values; simp; omega) (by table_decide)
      have h6' := seg_braT (L := L) (g := g) Flow.code_2456 hp7
      have h7 := (s_p12 (g := g) hd).live_start (s' := 2456) (d := d) rfl (by table_decide)
      have hp12 : (12, Value.pred true) ∈ factsAt L 2501 d :=
        fact_mem (by ink_values; simp [hi]) (by table_decide)
      have h8 := seg_braT (L := L) (g := g) Flow.code_2501 hp12
      have h9 := (seg_iter (g := g) hd (by omega)).live_start (s' := 2501) (d := d) rfl
        (by table_decide)
      have hs : start d = { d with site := .finBar } := by simp [start, h0]
      have he : d.i = d.n := by omega
      rw [hs]
      have h10 := h5.comp (h6'.comp (h7.comp (h8.comp h9)))
      rw [iterNext_fin he] at h10
      refine h10.weaken_end fun R hR => ?_
      exact holds_common hR (by table_decide) (by table_decide) rfl rfl
    · have hp7 : (7, Value.pred false) ∈ factsAt L 2456 d :=
        fact_mem (by ink_values; simp; omega) (by table_decide)
      have h6' := seg_braF (L := L) (g := g) Flow.code_2456 hp7
      have h7 := (s_top (g := g) hd).live_start (s' := 2456) (d := d) rfl (by table_decide)
      have hs : start d = { d with site := .qkBar } := by simp [start, h0, h6]
      rw [hs]
      exact h5.comp (h6'.comp h7)

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
