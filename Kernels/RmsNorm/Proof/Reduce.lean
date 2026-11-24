-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Values
public import Kernels.RmsNorm.Proof.Protocol.Shfl

@[expose] public section

/-! # The reductions

A lane's value after `k` butterfly rounds is the lanes' values combined by the first `k` rounds
(`bfk`): round `k` adds the value of the lane whose index differs in bit `bfOff k`, which the
lane receives from that lane's shuffle of the same number (`shfl_source`). So each lane's received
values are the rounds' values of its partner lanes (`ra_eq` for the warps' reductions of their
lanes' sums of squares, `rb_eq` for warp 0's reduction of the warp sums), and lane `0` of each
warp stores the warp's sum (`warp_sum`), thread `0` the CTA's total (`cta_total`), which is the
row's sum of squares (`total_eq`), which the load of the total reads (`tt_eq`). The values are the
outcomes of the code (`bsumV`), which on real summands read as the real sums (`bsumV_fin`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow Finset

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The lanes' values after the first `k` butterfly rounds. -/
def bfk : Nat → (Nat → ℝ) → Nat → ℝ
  | 0, V => V
  | k + 1, V => bf (bfOff k) (bfk k V)

theorem bfk_five (V : Nat → ℝ) : bfk 5 V = bfAll V := rfl

/-- A running sum of the partners' round values is the lane's round value. -/
theorem bsum_bfk (V : Nat → ℝ) (l : Nat) (r : Nat → ℝ) :
    ∀ k, (∀ k' < k, r k' = bfk k' V (l ^^^ bfOff k')) → bsum (V l) r k = bfk k V l
  | 0, _ => rfl
  | k + 1, h => by
    rw [bsum, bsum_bfk V l r k (fun k' hk' => h k' (by omega)), h k (by omega)]
    rfl

theorem fmaSum_congr {v w : Nat → ℝ} {z : ℝ} :
    ∀ {n}, (∀ m < n, v m = w m) → fmaSum v n z = fmaSum w n z
  | 0, _ => rfl
  | n + 1, h => by
    rw [fmaSum, fmaSum, fmaSum_congr (fun m hm => h m (by omega)), h n (by omega)]

/-- The sum of squares of thread `g`'s inputs of row `i`, as computed. -/
def ssqT (P : Params) (g i : Nat) : ℝ := fmaSum (xin P g i 1) 8 (fmaSum (xin P g i 0) 8 0)

/-- The lanes' sums of squares of warp `w` of CTA `c`. -/
def lanesV (P : Params) (c i w : Nat) (l : Nat) : ℝ := ssqT P (256 * c + 32 * w + l) i

theorem bfly_source {l : Nat} (hl : l < 32) {b : Nat} (hb : b < 32) :
    shflSource .bfly l b 31 = (l ^^^ b, true) := by
  have hx : l ^^^ b < 2 ^ 5 := Nat.xor_lt_two_pow (by omega) (by omega)
  simp only [shflSource, Nat.reduceMod, Nat.reduceDiv, Nat.and_zero, Nat.reduceSub,
    Nat.zero_or, Nat.mod_eq_of_lt hb]
  split_ifs with h
  · rfl
  · exact absurd (by norm_num at hx ⊢; omega) h

theorem bfOff_lt (k : Nat) : bfOff k < 32 := by unfold bfOff; split <;> omega

/-- The event of a shuffle site is a shuffle. -/
theorem shfl_event {g : Nat} {d : D} {e : Event} (h : SiteEvent P g d e)
    (hs : d.site.isShfl = true) :
    ∃ pc m a b c recv ok, e = ⟨pc, .shfl m a b c recv ok⟩ := by
  obtain ⟨t, o, hf⟩ := h
  rcases hsd : d.site <;> simp only [hsd, Site.isShfl, Bool.false_eq_true] at hs <;>
    simp only [siteTmpl, hsd, Fires] at hf <;> obtain ⟨recv, ok, rfl, -⟩ := hf <;>
    exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- The sum of warp `w` of CTA `c` in row `i`. -/
def warpW (P : Params) (c i w : Nat) : ℝ := ∑ l ∈ range 32, lanesV P c i w l

/-- The operands of warp 0's butterfly: the warp sums in lanes `0..7`, `0` in the others. -/
def warpU (P : Params) (c i l : Nat) : ℝ := if l < 8 then warpW P c i l else 0

/-- **The warp sums of a CTA add up to the row's sum of squares.** -/
theorem total_eq (P : Params) (c i : Nat) :
    ∑ w ∈ range 8, warpW P c i w = ∑ k ∈ range 4096, xe P (c + 152 * i) k ^ 2 := by
  have hT : ∀ t < 256, ssqT P (256 * c + t) i =
      ∑ m ∈ range 8, xe P (c + 152 * i) (8 * t + m) ^ 2 +
        ∑ m ∈ range 8, xe P (c + 152 * i) (2048 + (8 * t + m)) ^ 2 := by
    intro t ht
    have h1 : (256 * c + t) / 256 = c := by omega
    have h2 : (256 * c + t) % 256 = t := by omega
    simp only [ssqT, fmaSum_eq, xin, row, h1, h2, zero_add]
    congr 1
    exact sum_congr rfl fun m _ => by ring_nf
  have hW : ∑ w ∈ range 8, warpW P c i w = ∑ t ∈ range 256, ssqT P (256 * c + t) i := by
    simp only [warpW, lanesV]
    rw [← sum_range_mul (fun t => ssqT P (256 * c + t) i) 32 8]
    exact sum_congr rfl fun w _ => sum_congr rfl fun l _ => by rw [Nat.add_assoc]
  rw [hW, sum_congr rfl fun t ht => hT t (mem_range.mp ht), sum_add_distrib,
    sum_range_mul (fun j => xe P (c + 152 * i) j ^ 2) 8 256,
    sum_range_mul (fun j => xe P (c + 152 * i) (2048 + j) ^ 2) 8 256,
    show (4096 : Nat) = 256 * 8 + 2048 from rfl, sum_range_add]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **A state past a row's loads holds its sum of squares.** -/
theorem ssq_eq {g k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e) (hA : At P L X g k d e)
    (hr : d.site.inRow = true) (hp : 16 ≤ d.pos g) : ssqV d = fl (ssqT P g d.i) := by
  unfold ssqV ssqT
  rw [xb_eq hpre hX ht he hA hr hp, xa_eq hpre hX ht he hA hr (by omega)]
  exact fmaRun_fl (fun m hm => xw_xwords P g d.i 1 hm)
    (fmaRun_fin (fun m hm => xw_xwords P g d.i 0 hm) valFloat_z0 8 le_rfl) (n := 7) (by decide)

/-- The received value of a butterfly round: the source lane's operand of the same round of the
same row. -/
theorem round_source {z k1 : Nat} {d1 : D} {pc : Nat} {m : ShflMode} {a : Value} {b c : Nat}
    {recv : Value} {ok : Bool} (he : X.get (z, k1) = some ⟨pc, .shfl m a b c recv ok⟩)
    (hA : At P L X z k1 d1 ⟨pc, .shfl m a b c recv ok⟩) (hs : d1.site.isShfl = true)
    (hq : d1.site ≠ .shfl0) :
    ∃ ks ds pcs bs cs rs os, X.get (srcLane m z b c, ks) = some ⟨pcs, .shfl m recv bs cs rs os⟩ ∧
      At P L X (srcLane m z b c) ks ds ⟨pcs, .shfl m recv bs cs rs os⟩ ∧ ds.site = d1.site ∧
      ds.i = d1.i := by
  obtain ⟨ks, ds, pcs, bs, cs, rs, os, hes, hAs, hsc⟩ := shfl_source hpre hX ht he hA
  obtain ⟨h1, h2, -⟩ := srcLane_warp m z b c
  obtain ⟨hsite, hi⟩ := same_round hAs.inv hA.inv (isShfl_of_event hAs.event) hs h1 h2 hsc
  exact ⟨ks, ds, pcs, bs, cs, rs, os, hes, hAs, hsite, hi (by rw [hsite]; exact hq)⟩

/-- **The values a lane received in its warp's butterfly**: round `k` brings the round's value of
the partner lane. -/
theorem ra_eq : ∀ k < 5, ∀ {z kz : Nat} {dz : D} {e : Event}, X.get (z, kz) = some e →
    At P L X z kz dz e → dz.site.inRow = true → 24 + k < dz.pos z →
    valFloat .f32 (dz.ra k) =
      .ok (bfk k (lanesV P (z / 256) dz.i (z % 256 / 32)) (z % 256 % 32 ^^^ bfOff k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk5 z kz dz e he hA hr hp
  have hub := At.not_ub hX ht he hA
  have hkz : kz = rowBase z dz.i + dz.pos z := hA.index.trans (idx_of_row hr)
  have hlt := pos_lt hA.inv hr
  rw [hA.data.ra hr k hk5 hp, List.getElem?_take,
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h')]
  obtain ⟨d1, e1, he1, hA1, hi1, hp1, hr1⟩ := row_state hpre hX ht he hub (i := dz.i) (q := 24 + k)
    (by omega) (.inl (by omega))
  have hs1 := bfa_of_pos hA1.inv hr1 hk5 hp1
  obtain ⟨pc, m, a, b, c, recv, ok, rfl⟩ := shfl_event hA1.event (by simp [hs1, Site.isShfl])
  have hform : m = .bfly ∧ a = bsumV (ssqV d1) d1.ra k ∧ b = bfOff k ∧ c = 31 := by
    rcases shfl_site hA1.event with ⟨h, -⟩ | ⟨k', h, h2⟩ | ⟨k', h, -⟩ <;> rw [hs1] at h <;>
      try cases h
    exact h2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hform
  obtain ⟨ks, ds, pcs, bs, cs, rs, os, hes, hAs, hss, his⟩ :=
    round_source hpre hX ht he1 hA1 (by simp [hs1, Site.isShfl]) (by rw [hs1]; simp)
  rw [hs1] at hss
  rw [hi1] at his
  obtain ⟨hz1, hz2, hz3⟩ := srcLane_warp .bfly z (bfOff k) 31
  rw [bfly_source (Nat.mod_lt _ (by decide)) (bfOff_lt k)] at hz3
  set s := srcLane .bfly z (bfOff k) 31
  have hrecv : recv = bsumV (ssqV ds) ds.ra k := by
    rcases shfl_site hAs.event with ⟨h, -⟩ | ⟨k', h, -, h2, -⟩ | ⟨k', h, -⟩ <;> rw [hss] at h <;>
      try cases h
    exact h2
  have hrs' : ds.site.inRow = true := by simp [hss, Site.inRow]
  have hps : ds.pos s = 24 + k := by simp [D.pos, hss]
  have hssq := ssq_eq hpre hX ht hes hAs hrs' (by omega)
  have hra : ∀ k' < k, valFloat .f32 (ds.ra k') =
      .ok (bfk k' (lanesV P (z / 256) dz.i (z % 256 / 32)) (s % 256 % 32 ^^^ bfOff k')) := by
    intro k' hk'
    rw [ih k' hk' (by omega) hes hAs hrs' (by omega), his, hz1, hz2]
  have hV : lanesV P (z / 256) dz.i (z % 256 / 32) (s % 256 % 32) = ssqT P s ds.i := by
    unfold lanesV
    rw [his]
    congr 1
    omega
  rw [← Nat.add_assoc] at he1
  change valFloat .f32 (recvOf (X.get (z, _))) = _
  rw [he1]
  simp only [recvOf]
  rw [hrecv, hssq, bsumV_fin (valFloat_fl _) k hra, ← hV, bsum_bfk _ _ _ k (fun _ _ => rfl), hz3]

/-- **Lane `0` of a warp stores the warp's sum.** -/
theorem warp_sum {x kx : Nat} {dx : D} {e : Event} (he : X.get (x, kx) = some e)
    (hA : At P L X x kx dx e) (hs : dx.site = .stws) :
    bsumV (ssqV dx) dx.ra 5 = fl (warpW P (x / 256) dx.i (x % 256 / 32)) := by
  have hr : dx.site.inRow = true := by simp [hs, Site.inRow]
  have hl := hA.inv.stws hs
  have hp : dx.pos x = 29 := by simp [D.pos, hs]
  have hV : ssqT P x dx.i = lanesV P (x / 256) dx.i (x % 256 / 32) 0 := by
    unfold lanesV; congr 1; omega
  rw [ssq_eq hpre hX ht he hA hr (by omega), hV,
    bsumV_fl (valFloat_fl _) (n := 4) (rr := fun k' =>
      bfk k' (lanesV P (x / 256) dx.i (x % 256 / 32)) (0 ^^^ bfOff k'))
      (fun k' hk' => by rw [ra_eq hpre hX ht k' (by omega) he hA hr (by omega), hl]),
    bsum_bfk _ 0 _ 5 (fun _ _ => rfl), bfk_five, bfAll_eq]
  rfl

/-- **Warp 0's lanes hold the warp sums**: lane `l < 8` loaded warp `l`'s sum. -/
theorem u_eq {y k : Nat} {d : D} {e : Event} (he : X.get (y, k) = some e) (hA : At P L X y k d e)
    (hr : d.site.inRow = true) (h32 : y % 256 < 32) (hp : 30 + l0 y + l8 y ≤ d.pos y) :
    d.u = if y % 256 < 8 then fl (warpW P (y / 256) d.i (y % 256)) else b32 0 := by
  rw [hA.data.u hr h32 hp]
  split_ifs with h8
  · have hub := At.not_ub hX ht he hA
    have hk : k = rowBase y d.i + d.pos y := hA.index.trans (idx_of_row hr)
    have hl8 : l8 y = 1 := by simp [l8, h8]
    have hlt := pos_lt hA.inv hr
    rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h' => absurd (by omega) h')]
    obtain ⟨d1, e1, he1, hA1, hi1, hp1, hr1⟩ := row_state hpre hX ht he hub (i := d.i)
      (q := 30 + l0 y) (by unfold rowLen p1; omega) (.inl (by omega))
    have hs1 := ldws_of_pos hA1.inv hr1 h8 hp1
    obtain ⟨pc, a, bs, rfl⟩ := rd_event hA1.event (by simp [hs1, Site.isLoad])
    obtain ⟨kx, dx, pcx, hex, hAx, hsx, hix, hbs⟩ := ldws_bytes hpre hX ht he1 hA1 hs1
    rw [← Nat.add_assoc] at he1
    change rdv (X.get (y, _)) = _
    rw [he1, hbs, warp_sum hpre hX ht hex hAx hsx, rdv_fl, hix, hi1]
    congr 2 <;> omega
  · rfl

/-- A lane of warp 0 holds its operand of the second butterfly. -/
theorem u_val {y k : Nat} {d : D} {e : Event} (he : X.get (y, k) = some e) (hA : At P L X y k d e)
    (hr : d.site.inRow = true) (h32 : y % 256 < 32) (hp : 30 + l0 y + l8 y ≤ d.pos y) :
    valFloat .f32 d.u = .ok (warpU P (y / 256) d.i (y % 256)) := by
  rw [u_eq hpre hX ht he hA hr h32 hp]
  unfold warpU
  split_ifs
  · exact valFloat_fl _
  · exact valFloat_z0

/-- **The values warp 0's lanes received in its butterfly.** -/
theorem rb_eq : ∀ k < 5, ∀ {z kz : Nat} {dz : D} {e : Event}, X.get (z, kz) = some e →
    At P L X z kz dz e → dz.site.inRow = true → z % 256 < 32 →
    30 + l0 z + l8 z + k < dz.pos z →
    valFloat .f32 (dz.rb k) = .ok (bfk k (warpU P (z / 256) dz.i) (z % 256 ^^^ bfOff k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk5 z kz dz e he hA hr h32 hp
  have hub := At.not_ub hX ht he hA
  have hkz : kz = rowBase z dz.i + dz.pos z := hA.index.trans (idx_of_row hr)
  have hlt := pos_lt hA.inv hr
  rw [hA.data.rb hr h32 k hk5 hp, List.getElem?_take,
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h')]
  obtain ⟨d1, e1, he1, hA1, hi1, hp1, hr1⟩ := row_state hpre hX ht he hub (i := dz.i)
    (q := 30 + l0 z + l8 z + k) (by omega) (.inl (by omega))
  have hs1 := bfb_of_pos hA1.inv hr1 h32 hk5 hp1
  obtain ⟨pc, m, a, b, c, recv, ok, rfl⟩ := shfl_event hA1.event (by simp [hs1, Site.isShfl])
  have hform : m = .bfly ∧ a = bfbOp d1 k ∧ b = bfOff k ∧ c = 31 := by
    rcases shfl_site hA1.event with ⟨h, -⟩ | ⟨k', h, -⟩ | ⟨k', h, h2⟩ <;> rw [hs1] at h <;>
      try cases h
    exact h2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hform
  obtain ⟨ks, ds, pcs, bs, cs, rs, os, hes, hAs, hss, his⟩ :=
    round_source hpre hX ht he1 hA1 (by simp [hs1, Site.isShfl]) (by rw [hs1]; simp)
  rw [hs1] at hss
  rw [hi1] at his
  obtain ⟨hz1, hz2, hz3⟩ := srcLane_warp .bfly z (bfOff k) 31
  rw [bfly_source (Nat.mod_lt _ (by decide)) (bfOff_lt k)] at hz3
  set s := srcLane .bfly z (bfOff k) 31
  have hs32 : s % 256 < 32 := by omega
  have hlane : s % 256 = z % 256 ^^^ bfOff k := by
    have h1 : s % 256 % 32 = s % 256 := Nat.mod_eq_of_lt hs32
    have h2 : z % 256 % 32 = z % 256 := Nat.mod_eq_of_lt h32
    simp only at hz3
    rw [← h1, hz3, h2]
  have hrecv : recv = bfbOp ds k := by
    rcases shfl_site hAs.event with ⟨h, -⟩ | ⟨k', h, -⟩ | ⟨k', h, -, h2, -⟩ <;> rw [hss] at h <;>
      try cases h
    exact h2
  have hrs : ds.site.inRow = true := by simp [hss, Site.inRow]
  have hps : ds.pos s = 30 + l0 s + l8 s + k := by simp [D.pos, hss]
  have hU : valFloat .f32 ds.u = .ok (warpU P (z / 256) dz.i (s % 256)) := by
    rw [u_val hpre hX ht hes hAs hrs hs32 (by omega), his, hz1]
  have hrb : ∀ k' < k, valFloat .f32 (ds.rb k') =
      .ok (bfk k' (warpU P (z / 256) dz.i) (s % 256 ^^^ bfOff k')) := by
    intro k' hk'
    rw [ih k' hk' (by omega) hes hAs hrs hs32 (by omega), his, hz1]
  rw [show rowBase z dz.i + (30 + l0 z + l8 z + k) = rowBase z dz.i + 30 + l0 z + l8 z + k by
    omega] at he1
  change valFloat .f32 (recvOf (X.get (z, _))) = _
  rw [he1]
  simp only [recvOf]
  rw [hrecv, bfbOp, bsumV_fin hU k hrb, bsum_bfk _ _ _ k (fun _ _ => rfl), hlane]

/-- **Thread `0` stores the CTA's total**, the sum of its warps' sums. -/
theorem cta_total {x kx : Nat} {dx : D} {e : Event} (he : X.get (x, kx) = some e)
    (hA : At P L X x kx dx e) (hs : dx.site = .stts) :
    bsumV dx.u dx.rb 5 = fl (∑ w ∈ range 8, warpW P (x / 256) dx.i w) := by
  have hr : dx.site.inRow = true := by simp [hs, Site.inRow]
  have h0 := hA.inv.stts hs
  have hl0 : l0 x = 1 := by simp [l0, h0]
  have hl8 : l8 x = 1 := by simp [l8, h0]
  have hp : dx.pos x = 37 := by simp [D.pos, hs, hl0, hl8]
  have hU : valFloat .f32 dx.u = .ok (warpU P (x / 256) dx.i 0) := by
    rw [u_val hpre hX ht he hA hr (by omega) (by omega), h0]
  rw [bsumV_fl hU (n := 4) (rr := fun k' => bfk k' (warpU P (x / 256) dx.i) (0 ^^^ bfOff k'))
      (fun k' hk' => by rw [rb_eq hpre hX ht k' (by omega) he hA hr (by omega) (by omega), h0]),
    bsum_bfk _ 0 _ 5 (fun _ _ => rfl), bfk_five, bfAll_eq, show (32 : Nat) = 8 + 24 from rfl,
    sum_range_add]
  have hz : ∑ l ∈ range 24, warpU P (x / 256) dx.i (8 + l) = 0 :=
    sum_eq_zero fun l _ => by simp [warpU]
  rw [hz, add_zero]
  exact congrArg fl (sum_congr rfl fun w hw => by simp [warpU, mem_range.mp hw])

/-- **A state past a row's load of the total holds the row's sum of squares.** -/
theorem tt_eq {g k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e) (hA : At P L X g k d e)
    (hr : d.site.inRow = true) (hp : p1 g + 1 < d.pos g) :
    d.tt = fl (∑ m ∈ range 4096, xe P (row g d.i) m ^ 2) := by
  have hub := At.not_ub hX ht he hA
  have hk : k = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
  have hlt := pos_lt hA.inv hr
  rw [hA.data.tt hr hp, List.getElem?_take, ite_eq_left_iff.mpr (fun h' => absurd (by omega) h')]
  obtain ⟨d1, e1, he1, hA1, hi1, hp1, hr1⟩ := row_state hpre hX ht he hub (i := d.i)
    (q := p1 g + 1) (by unfold rowLen; omega) (.inl (by omega))
  have hs1 := ldts_of_pos hA1.inv hr1 hp1
  obtain ⟨pc, a, bs, rfl⟩ := rd_event hA1.event (by simp [hs1, Site.isLoad])
  obtain ⟨kx, dx, pcx, hex, hAx, hsx, hix, hbs⟩ := ldts_bytes hpre hX ht he1 hA1 hs1
  rw [← Nat.add_assoc] at he1
  change rdv (X.get (g, _)) = _
  rw [he1, hbs, cta_total hpre hX ht hex hAx hsx, rdv_fl, total_eq, hix, hi1,
    show 256 * (g / 256) / 256 + 152 * d.i = row g d.i by simp only [row]; omega]

end
end PTX.Kernels.RmsNorm.Proof
