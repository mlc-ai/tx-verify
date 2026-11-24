-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WxSmOrder
public import Kernels.InklingRelDecode.Proof.Progress.WxProOrder
public import Kernels.InklingRelDecode.Proof.Progress.WuEnd
public import Kernels.InklingRelDecode.Proof.Interface.KkBar
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0

@[expose] public section

/-!
# `BarTime.lag0l`: a default lane with no more barrier-0 events is no later

The statement (`Assemble.Lag0l`, the field `lag0l` of `BarTime`): thread `g` makes a
`bar.sync 0, 128` at its event `k`, from its state `d`; a default-partition thread `y` of its CTA
has made at most as many barrier-0 events as `g` before `k`. Then `y` has not exited and
`threadTime y ≤ time d`.

The proof uses the agreement of the CTA's lazy-rescale decisions (`Lk.DecAgree`, from
`Lk.decAgree_every`): with it the number of barrier-0 events before a default-partition state is a
function of the state and of the CTA (`B0N.cnt_eq`, `Kk.cnt_val`, `B0N.rinv_all`):

* a state of the common start: at most one, and it is timed at most 26;
* a prologue state: `2 + proOff`, and the prologue is straight-line code (`WxProOrder.lean`);
* a softmax state: `2 + C0 + phi site i + RD`, ordered with the time by `WxSmOrder.lean`;
* an epilogue state: at least `2 + C0 + Lfun num_iters + nResc num_iters`, more than any
  `bar.sync 0, 128` has before it (`B0N.cnt_sm_all`, `B0N.cnt_pro`).

`y` is at a state now, or stopped at its last event (`Wu.end_cases`, which takes `¬ HasUb X`). In
the first case its count is the count of its state (`cmp_le`); in the second, the count of the
state before the last event plus that event's barrier-0 event, and the time is one more
(`cmp_lt`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Static facts -/

/-- A softmax state with its site facts has a nonnegative count. -/
theorem phi_nonneg {Dc : Nat → Prop} {d : Sm.D} (hJ : JS Dc d) : 0 ≤ phi d.site d.i := by
  obtain ⟨hJ1, -⟩ := hJ
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp_all [phi, mid, resc] <;> (try split_ifs) <;> omega

/-- Every prologue site is at most the last one, `bar18`. -/
theorem pro_idx_le (s : ProA.Site) : s.ctorIdx ≤ 181 := by
  cases s <;> decide

/-- A softmax barrier site is timed at least at slot `0`'s softmax band. -/
theorem smT_bar_ge {d : Sm.D} (hb : smB0 d.site = 2) : slot 0 + bandS ≤ smT d := by
  rw [smT_loop (bar_loop hb)]
  unfold slot
  have := Nat.zero_le d.i
  nlinarith

/-! ### The state of the barrier event -/

/-- **The state of a `bar.sync 0, 128`**: a default-partition thread at a prologue or a softmax
barrier site. -/
theorem bar_state128 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {d : TSt}
    (he : X.get (g, k) = some ⟨pc, .bar 0 (some 128) .sync⟩)
    (hσ : St Q L X g k = some (some d)) :
    ∃ s, d = .d s ∧ g % L.block < 128 ∧
      ((∃ p, s = .pro p ∧ proB0 p.site = 2) ∨ (∃ m, s = .sm m ∧ smB0 m.site = 2)) := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  rcases b0_count hpre hX hf.sound he hσ with ⟨h, -⟩ | ⟨-, h2⟩
  · cases h
  cases d with
  | w ws => exact absurd h2 (w_b0_ne ws)
  | d s =>
    refine ⟨s, rfl, (cls_inv k _ hk hσ).mp trivial, ?_⟩
    have hz : b0At (DComp.pc s) ≠ 0 := by
      have : b0At (TSt.pc (.d s)) = 2 := h2
      simp only [TSt.pc] at this
      omega
    rcases b0_state hz with ⟨d0, rfl, -⟩ | ⟨p, rfl, hp⟩ | ⟨m, rfl, hm⟩ | ⟨d0, rfl, -⟩
    · exact absurd h2 (dstart_b0At_le d0.site)
    · exact .inl ⟨p, rfl, hp⟩
    · exact .inr ⟨m, rfl, hm⟩
    · exact absurd h2 (epi_b0At_le d0.site)

/-! ### The comparison of a lane's state with the barrier state -/

/-- **An epilogue state has more barrier-0 events than a `bar.sync 0, 128`.** -/
theorem epi_more (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hD : ∀ c j, DecAgree Q L X c j) {g k y ky : Nat}
    {e : Event} {s : DComp.St} {d1 : Epi.D} (hg : g < L.threads) (hy : y < L.threads)
    (hc : y / L.block = g / L.block) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d s)))
    (hbar : (∃ p, s = .pro p ∧ proB0 p.site = 2) ∨ (∃ m, s = .sm m ∧ smB0 m.site = 2))
    (hky : ky ≤ (X.tr y).length) (hσy : St Q L X y ky = some (some (.d (.epi d1)))) :
    cnt0 X g k < cnt0 X y ky := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hC : C0 Q L y = C0 Q L g := by simp only [C0, nbQ_cta (Q := Q) hc]
  have hN : nIt Q L y = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block hc .z, ProA.cta_eq_of_block hc .x]
  have h1 := cnt_epi (I := nIt Q L y) hpre hX hf hy (fun j _ => hD _ j) hky hσy
  rw [Nat.min_self, hC, hN, hc] at h1
  have h2 : (2 : Int) ≤ dN0 (.epi d1) := by
    simp only [dN0]; split <;> omega
  have hl := lfun_nonneg (nIt Q L g)
  have hn0 : (0 : Int) ≤ ((nResc (Dc Q L X (g / L.block)) (nIt Q L g) : Nat) : Int) :=
    Int.natCast_nonneg _
  rcases hbar with ⟨p, rfl, hp⟩ | ⟨m, rfl, hm⟩
  · have := cnt_pro hpre hX hf hg hk hσ hp
    have : (cnt0 X g k : Int) < cnt0 X y ky := by omega
    exact_mod_cast this
  · obtain ⟨hlt, -, hup⟩ := cnt_sm_all hpre hX hf hg (hD _) he hσ hm
    have := lfun_ge hlt
    have : (cnt0 X g k : Int) < cnt0 X y ky := by omega
    exact_mod_cast this

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hD : ∀ c j, DecAgree Q L X c j) {g k y ky : Nat} {e : Event} {s sy : DComp.St}
    (hg : g < L.threads) (hy : y < L.threads) (hc : y / L.block = g / L.block)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hbar : (∃ p, s = .pro p ∧ proB0 p.site = 2) ∨ (∃ m, s = .sm m ∧ smB0 m.site = 2))
    (hky : ky ≤ (X.tr y).length) (hσy : St Q L X y ky = some (some (.d sy)))
include hpre hX hf hD hg hy hc he hσ hbar hky hσy

/-- **The four situations** of a default state `sy` of `y` against the barrier state `s` of `g`:
`sy` is earlier by its kind; both are softmax states with their counts; both are prologue states
with their counts; or `sy` has more barrier-0 events. -/
theorem kinds :
    dcompT sy < dcompT s ∨
    (∃ m1 m, sy = .sm m1 ∧ s = .sm m ∧ smB0 m.site = 2 ∧
      JS (Dc Q L X (g / L.block)) m1 ∧ JS (Dc Q L X (g / L.block)) m ∧
      (cnt0 X y ky : Int) = 2 + C0 Q L g + phi m1.site m1.i + RD (Dc Q L X (g / L.block)) m1 ∧
      (cnt0 X g k : Int) = 2 + C0 Q L g + phi m.site m.i + RD (Dc Q L X (g / L.block)) m) ∨
    (∃ p1 p, sy = .pro p1 ∧ s = .pro p ∧ proB0 p.site = 2 ∧ p1.site.afterSk = true ∧
      ProA.Gate L y p1.site p1.dt ∧ ProA.Gate L g p.site p.dt ∧
      nbOf L y p1.dt = nbOf L g p.dt ∧
      cnt0 X y ky = 2 + proOff L y p1 ∧ cnt0 X g k = 2 + proOff L g p) ∨
    cnt0 X g k < cnt0 X y ky := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hC : C0 Q L y = C0 Q L g := by simp only [C0, nbQ_cta (Q := Q) hc]
  have hN : nIt Q L y = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block hc .z, ProA.cta_eq_of_block hc .x]
  have hC1 := c0_pos (Q := Q) (L := L) g
  -- the count of the barrier state is below `2 + C0` (prologue) or bounded by its iteration
  have hgup : (∃ p, s = .pro p ∧ proB0 p.site = 2 ∧ (cnt0 X g k : Int) < 2 + C0 Q L g) ∨
      (∃ m, s = .sm m ∧ smB0 m.site = 2 ∧ m.i < nIt Q L g ∧ 2 + C0 Q L g ≤ (cnt0 X g k : Int) ∧
        (cnt0 X g k : Int) ≤ 2 + C0 Q L g + 4 * (m.i : Int) + 1 +
          nResc (Dc Q L X (g / L.block)) (nIt Q L g)) := by
    rcases hbar with ⟨p, rfl, hp⟩ | ⟨m, rfl, hm⟩
    · exact .inl ⟨p, rfl, hp, cnt_pro hpre hX hf hg hk hσ hp⟩
    · obtain ⟨h1, h2, h3⟩ := cnt_sm_all hpre hX hf hg (hD _) he hσ hm
      exact .inr ⟨m, rfl, hm, h1, h2, h3⟩
  -- a time above the prologue's
  have hgt : ∀ m, s = .sm m → smB0 m.site = 2 → 281 < dcompT s := by
    rintro m rfl hm
    have := smT_bar_ge hm
    simp only [dcompT]
    wt_omega
  cases sy with
  | dstart d0 =>
    left
    have h1 := dstartT_le d0
    rcases hbar with ⟨p, rfl, -⟩ | ⟨m, rfl, hm⟩
    · simp only [dcompT, proT]; omega
    · have := hgt m rfl hm; simp only [dcompT] at this ⊢; omega
  | epi d1 =>
    right; right; right
    exact epi_more hpre hX hf hD hg hy hc he hσ hbar hky hσy
  | sm m1 =>
    have hv := Kk.cnt_val hpre hX hf hy (hD _) hky hσy
    rw [hc, hC] at hv
    obtain ⟨hJ1, hv⟩ := hv
    rcases hgup with ⟨p, rfl, -, hp⟩ | ⟨m, rfl, hm, -, -, -⟩
    · right; right; right
      have := phi_nonneg hJ1
      have : (cnt0 X g k : Int) < cnt0 X y ky := by omega
      exact_mod_cast this
    · right; left
      obtain ⟨hJ, hv'⟩ := Kk.cnt_val hpre hX hf hg (hD _) hk hσ
      exact ⟨m1, m, rfl, rfl, hm, hJ1, hJ, hv, hv'⟩
  | pro p1 =>
    rcases hbar with ⟨p, rfl, hp⟩ | ⟨m, rfl, hm⟩
    · by_cases ha : p1.site.afterSk = true
      · right; right; left
        have hG1 := (pgSo_all hpre hX hf (g := y) ky _ hσy).1
        have hG := (pgSo_all hpre hX hf (g := g) k _ hσ).1
        have hn1 := nbOf_pro hpre hX hf hy hσy ha
        have hn := nbOf_pro hpre hX hf hg hσ (pro_b0_afterSk hp)
        have hq : nbQ Q L y = nbQ Q L g := nbQ_cta hc
        have c1 := cnt_eq hpre hX hf hy hky hσy
        rw [nb_pro hpre hX hf hy hky hσy] at c1
        have c2 := cnt_eq hpre hX hf hg hk hσ
        rw [nb_pro hpre hX hf hg hk hσ] at c2
        simp only [dN0, p128] at c1 c2
        refine ⟨p1, p, rfl, rfl, hp, ha, hG1, hG, by rw [hn1, hn, hq], ?_, ?_⟩ <;> omega
      · left
        have h1 := early_idx (by simpa using ha)
        have h2 := bar_idx hp
        simp only [dcompT, proT]
        omega
    · left
      have h1 := hgt m rfl hm
      have h2 := pro_idx_le p1.site
      show proT p1 < _
      simp only [proT]
      omega

/-- **A lane's state with at most the barrier state's count is no later.** -/
theorem cmp_le (hle : cnt0 X y ky ≤ cnt0 X g k) : dcompT sy ≤ dcompT s := by
  rcases kinds hpre hX hf hD hg hy hc he hσ hbar hky hσy with h | h | h | h
  · exact h.le
  · obtain ⟨m1, m, rfl, rfl, hm, hJ1, hJ, h1, h2⟩ := h
    have : (cnt0 X y ky : Int) ≤ cnt0 X g k := by exact_mod_cast hle
    exact sm_le hJ1 hJ hm (by omega)
  · obtain ⟨p1, p, rfl, rfl, hp, -, hG1, hG, hN, h1, h2⟩ := h
    have := pro_le hG1 hG hN hp (by omega)
    simp only [dcompT, proT]
    omega
  · omega

/-- **A lane's state whose count with its own barrier-0 event is at most the barrier state's count
is earlier.** -/
theorem cmp_lt (hle : cnt0 X y ky + (if b0At (DComp.pc sy) ≠ 0 then 1 else 0) ≤ cnt0 X g k) :
    dcompT sy < dcompT s := by
  rcases kinds hpre hX hf hD hg hy hc he hσ hbar hky hσy with h | h | h | h
  · exact h
  · obtain ⟨m1, m, rfl, rfl, hm, hJ1, hJ, h1, h2⟩ := h
    have hi : smInc m1.site = ((if b0At (DComp.pc (.sm m1)) ≠ 0 then 1 else 0 : Nat) : Int) := by
      simp only [smInc, DComp.pc, sm_b0At]
      unfold smB0
      split <;> simp
    have : ((cnt0 X y ky + (if b0At (DComp.pc (.sm m1)) ≠ 0 then 1 else 0) : Nat) : Int) ≤
        cnt0 X g k := by exact_mod_cast hle
    push_cast at this
    exact sm_lt hJ1 hJ hm (by omega)
  · obtain ⟨p1, p, rfl, rfl, hp, -, hG1, hG, hN, h1, h2⟩ := h
    have hi : proInc p1.site = (if b0At (DComp.pc (.pro p1)) ≠ 0 then 1 else 0) := by
      simp only [proInc, DComp.pc, pro_b0At]
      unfold proB0
      split <;> simp
    have := pro_lt hG1 hG hN hp (by omega)
    simp only [dcompT, proT]
    omega
  · omega
end

/-! ### `lag0l` -/

/-- **`BarTime.lag0l`** (`Assemble.Lag0l` for `Wt.time`), when the lazy-rescale decisions of every
CTA agree and the execution has no undefined behaviour. -/
theorem lag0l_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hub : ¬ HasUb X) (hD : ∀ c j, DecAgree Q L X c j)
    {g k pc y : Nat} {d : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .bar 0 (some 128) .sync⟩)
    (hσ : St Q L X g k = some (some d)) (hy : y < L.threads)
    (hc : y / L.block = g / L.block) (hyd : y % L.block < 128)
    (hle : (X.tr y).countP (Execution.isBarId 0) ≤
      ((X.tr g).take k).countP (Execution.isBarId 0)) :
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (timed Wt.time Q L) X y ≤ Wt.time g d := by
  obtain ⟨s, rfl, -, hbar⟩ := bar_state128 hpre hX hf he hσ
  have hall : (X.tr y).countP (Execution.isBarId 0) = cnt0 X y (X.tr y).length := by
    unfold cnt0; rw [List.take_length]
  have hle' : cnt0 X y (X.tr y).length ≤ cnt0 X g k := by rw [← hall]; exact hle
  have hnx : ∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    have hj' : j ≤ (X.tr y).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr y)[j]? = _ from hj)).1.le
    rcases exit_event_state hX hf.sound hf.tracked hj with ⟨de, hσ', -⟩ | ⟨x, hσ', -⟩
    · have h1 := epi_more hpre hX hf hD hg hy hc he hσ hbar hj' hσ'
      have h2 : cnt0 X y j ≤ cnt0 X y (X.tr y).length :=
        (List.take_sublist_take_left hj').countP_le
      omega
    · obtain ⟨s', hs'⟩ := dstate_of hj' hσ' hyd
      cases hs'
  refine ⟨hnx, ?_⟩
  rcases Wu.end_cases hX hf.sound hf.tracked hub hy hnx with
    ⟨σ, hσy, -⟩ | ⟨σ, e1, hpos, hσy, hnone, -, he1⟩
  · obtain ⟨sy, rfl⟩ := dstate_of le_rfl hσy hyd
    rw [threadTime_eq hσy]
    exact cmp_le hpre hX hf hD hg hy hc he hσ hbar le_rfl hσy hle'
  · have hk1 : (X.tr y).length - 1 ≤ (X.tr y).length := Nat.sub_le _ _
    obtain ⟨sy, rfl⟩ := dstate_of hk1 hσy hyd
    rw [threadTime_stop hσy hnone]
    have hs1 : (X.tr y).length = (X.tr y).length - 1 + 1 := by omega
    have hcs : cnt0 X y (X.tr y).length = cnt0 X y ((X.tr y).length - 1) +
        if Execution.isBarId 0 e1 = true then 1 else 0 := by
      conv_lhs => rw [hs1]
      unfold cnt0
      rw [List.take_add_one, show (X.tr y)[(X.tr y).length - 1]? = some e1 from he1]
      simp [List.countP_append]
    have hb : Execution.isBarId 0 e1 = true ↔ b0At (DComp.pc sy) ≠ 0 :=
      b0_event hpre hX hf.sound he1 hσy
    have : (if Execution.isBarId 0 e1 = true then 1 else 0) =
        (if b0At (DComp.pc sy) ≠ 0 then 1 else 0) := by
      simp only [hb]
    have := cmp_lt hpre hX hf hD hg hy hc he hσ hbar hk1 hσy (by omega)
    show dcompT sy + 1 ≤ dcompT s
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
