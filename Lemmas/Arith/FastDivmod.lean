-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Set.Function
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# FastDivmod and static persistent schedules

CuTeDSL's `FastDivmod` divides a 32-bit unsigned `n` by a host-known divisor `d` with
```
hi = mul.hi.u32(n, m);  t = (n - hi) >> s1;  q = (t + hi) >> s2
```
(`sub.s32`, `add.s32` wrap modulo `2^32`), and the remainder is `n - q * d` (`mul.lo`,
`sub`).  The host triple `(m, s1, s2)` is the Granlund-Montgomery / Hacker's Delight
"round-up, add" variant: for `l = ceil(log2 d)` the 33-bit magic is `2^32 + m =
ceil(2^(32+l) / d)`, `s1 = 1`, `s2 = l - 1`; `d = 1` is encoded `(0, 0, 0)` (as CUTLASS's
`find_divisor`).  The CuTeDSL host code is closed source, so this formula is derived to
match the instruction sequence; the theorem proves it exact for every `n < 2^32` and
`1 ≤ d < 2^31`.

The second half is generic schedule arithmetic: the items a static persistent worker
visits (`c, c + G, c + 2G, ...`), their partition and counts, and the nested-divmod
decomposition of a linear tile index.
-/

namespace FastDivmod

/-- The 32-bit word modulus. -/
def W : Nat := 2 ^ 32

/-- `mul.hi.u32`: the high word of the 64-bit product. -/
def mulHi (a b : Nat) : Nat := (a % W) * (b % W) / W

/-- `mul.lo`: the low word of the product. -/
def mulLo (a b : Nat) : Nat := (a * b) % W

/-- `sub.s32` as 32-bit two's complement wraparound. -/
def sub32 (a b : Nat) : Nat := (a % W + W - b % W) % W

/-- `add.s32` as 32-bit two's complement wraparound. -/
def add32 (a b : Nat) : Nat := (a + b) % W

/-- `shr.u32`: logical right shift of a 32-bit word (shift amounts `≥ 32` give `0`). -/
def shr32 (a s : Nat) : Nat := a % W / 2 ^ s

/-- Host-side `(multiplier, shift1, shift2)` for divisor `d`. -/
def params (d : Nat) : Nat × Nat × Nat :=
  if d ≤ 1 then (0, 0, 0)
  else ((2 ^ (32 + Nat.clog 2 d) + d - 1) / d - W, 1, Nat.clog 2 d - 1)

/-- The device-side quotient: exactly the instruction sequence. -/
def quot (m s1 s2 n : Nat) : Nat :=
  let hi := mulHi n m
  shr32 (add32 (shr32 (sub32 n hi) s1) hi) s2

/-- Quotient from the host triple. -/
def quotP (p : Nat × Nat × Nat) (n : Nat) : Nat := quot p.1 p.2.1 p.2.2 n

/-- The device-side remainder `n - q * d` in 32-bit arithmetic. -/
def rem (d q n : Nat) : Nat := sub32 n (mulLo q d)

theorem sub32_of_le {a b : Nat} (hb : b ≤ a) (ha : a < W) : sub32 a b = a - b := by
  unfold sub32
  have : b < W := by omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt this]
  rcases Nat.eq_or_lt_of_le hb with h | h
  · subst h; simp
  · rw [show a + W - b = (a - b) + W by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- Round-up magic lemma: `M * d = 2^(32+l) + e` with `e < d`, `d ≤ 2^l`, `n < 2^32`
gives `n * M / 2^(32+l) = n / d`. -/
theorem magic_div {n d l M e : Nat} (hd : 0 < d) (hdl : d ≤ 2 ^ l) (hn : n < 2 ^ 32)
    (hM : M * d = 2 ^ (32 + l) + e) (he : e < d) : n * M / 2 ^ (32 + l) = n / d := by
  have hD : 2 ^ (32 + l) = 2 ^ 32 * 2 ^ l := pow_add 2 32 l
  have hpos : 0 < 2 ^ (32 + l) := by positivity
  have hne : n * e < 2 ^ (32 + l) := by
    rw [hD]
    exact Nat.mul_lt_mul'' hn (by omega)
  have hnd := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  set q := n / d
  set r := n % d
  have hkey : n * M * d = n * 2 ^ (32 + l) + n * e := by
    calc n * M * d = n * (M * d) := by ring
      _ = _ := by rw [hM]; ring
  apply Nat.div_eq_of_lt_le
  · -- q * D ≤ n * M
    refine Nat.le_of_mul_le_mul_right ?_ hd
    calc q * 2 ^ (32 + l) * d = (d * q) * 2 ^ (32 + l) := by ring
      _ ≤ n * 2 ^ (32 + l) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ n * M * d := by rw [hkey]; omega
  · -- n * M < (q + 1) * D
    refine Nat.lt_of_mul_lt_mul_right (a := d) ?_
    calc n * M * d = n * 2 ^ (32 + l) + n * e := hkey
      _ < (n + 1) * 2 ^ (32 + l) := by rw [Nat.add_mul, one_mul]; omega
      _ ≤ (d * (q + 1)) * 2 ^ (32 + l) := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (q + 1) * 2 ^ (32 + l) * d := by ring

/-- The host triple is exact on every 32-bit dividend, for divisors `1 < d < 2^31`. -/
theorem quotP_params_of_one_lt {d n : Nat} (hd1 : 1 < d) (hd : d < 2 ^ 31) (hn : n < 2 ^ 32) :
    quotP (params d) n = n / d := by
  have hW : W = 2 ^ 32 := rfl
  have hdl : d ≤ 2 ^ Nat.clog 2 d := Nat.le_pow_clog (by norm_num) d
  have hlo : 2 ^ (Nat.clog 2 d - 1) < d := Nat.pow_pred_clog_lt_self (by norm_num) hd1
  generalize hl : Nat.clog 2 d = l at hdl hlo
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hdl; omega
    · exact h
  have h2l : 2 ^ l = 2 * 2 ^ (l - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hDeq : 2 ^ (32 + l) = 2 ^ 32 * 2 ^ l := pow_add 2 32 l
  generalize hP : 2 ^ (l - 1) = P at hlo h2l
  -- the magic constant `M = ceil(2^(32+l) / d)`, with `M * d = 2^(32+l) + e`, `e < d`
  have hd0 : 0 < d := by omega
  have h1 := Nat.div_add_mod (2 ^ (32 + l) + d - 1) d
  have h2 := Nat.mod_lt (2 ^ (32 + l) + d - 1) hd0
  generalize hM : (2 ^ (32 + l) + d - 1) / d = M at h1
  generalize hs : (2 ^ (32 + l) + d - 1) % d = s at h1 h2
  rw [Nat.mul_comm] at h1
  have hMd : M * d = 2 ^ (32 + l) + (d - 1 - s) := by
    have := Nat.mul_comm d M
    omega
  have hMlo : 2 ^ 32 ≤ M := by
    apply Nat.le_of_mul_le_mul_right _ hd0
    calc 2 ^ 32 * d ≤ 2 ^ 32 * 2 ^ l := Nat.mul_le_mul_left _ hdl
      _ = 2 ^ (32 + l) := hDeq.symm
      _ ≤ M * d := by omega
  have hMhi : M < 2 ^ 33 := by
    apply Nat.lt_of_mul_lt_mul_right (a := d)
    have : 2 ^ 33 * d = 2 ^ 33 * (d - 1) + 2 ^ 33 := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  generalize hm : M - 2 ^ 32 = m
  have hmM : M = 2 ^ 32 + m := by omega
  have hm32 : m < 2 ^ 32 := by omega
  have hpar : (params d) = (m, 1, l - 1) := by
    have hnd : ¬ d ≤ 1 := by omega
    simp only [params, hnd, ↓reduceIte, hl, hW, hM, hm]
  unfold quotP
  rw [hpar]
  simp only [quot, mulHi, shr32, add32, hW]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm32]
  have hhi : n * m / 2 ^ 32 ≤ n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
    nlinarith
  have hs1 : sub32 n (n * m / 2 ^ 32) = n - n * m / 2 ^ 32 :=
    sub32_of_le hhi hn
  rw [hs1, Nat.mod_eq_of_lt (by omega : n - n * m / 2 ^ 32 < 2 ^ 32), pow_one]
  have hNM : n * M / 2 ^ 32 = n + n * m / 2 ^ 32 := by
    have : n * M = 2 ^ 32 * n + n * m := by rw [hmM]; ring
    rw [this, Nat.mul_add_div (by positivity)]
  have hsum : (n - n * m / 2 ^ 32) / 2 + n * m / 2 ^ 32 = n * M / 2 ^ 32 / 2 := by omega
  have hb : (n - n * m / 2 ^ 32) / 2 + n * m / 2 ^ 32 < 2 ^ 32 := by omega
  simp only [Nat.mod_eq_of_lt hb]
  rw [hsum, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rw [hP, ← h2l, ← hDeq]
  exact magic_div hd0 hdl hn hMd (by omega)

/-- The host triple is exact for every divisor `1 ≤ d < 2^31` and 32-bit dividend. -/
theorem quot_params {d n : Nat} (hd1 : 1 ≤ d) (hd : d < 2 ^ 31) (hn : n < 2 ^ 32) :
    quotP (params d) n = n / d := by
  rcases Nat.eq_or_lt_of_le hd1 with h | h
  · subst h
    have hW : W = 2 ^ 32 := rfl
    simp [quotP, params, quot, mulHi, shr32, add32, sub32, hW]
    omega
  · exact quotP_params_of_one_lt h hd hn

/-- The remainder `n - q * d` in 32-bit arithmetic is `n % d` once `q = n / d`. -/
theorem rem_eq_mod {d n : Nat} (hn : n < 2 ^ 32) :
    rem d (n / d) n = n % d := by
  have hW : W = 2 ^ 32 := rfl
  have hle : n / d * d ≤ n := Nat.div_mul_le_self n d
  have hlo : mulLo (n / d) d = n / d * d := Nat.mod_eq_of_lt (by omega)
  have := Nat.div_add_mod n d
  unfold rem
  rw [hlo, sub32_of_le hle (by omega)]
  have h2 : d * (n / d) = n / d * d := Nat.mul_comm _ _
  omega

/-- Quotient and remainder, as the kernel computes them, are `n / d` and `n % d`. -/
theorem divmod_params {d n : Nat} (hd1 : 1 ≤ d) (hd : d < 2 ^ 31) (hn : n < 2 ^ 32) :
    quotP (params d) n = n / d ∧ rem d (quotP (params d) n) n = n % d := by
  have h := quot_params hd1 hd hn
  exact ⟨h, by rw [h]; exact rem_eq_mod hn⟩

end FastDivmod

namespace StaticSchedule

/-- The items `c, c + G, c + 2G, ...` below `T` visited by worker `c` of `G` workers. -/
def visits (G T c : Nat) : Finset Nat := (Finset.range T).filter (fun t => t % G = c)

/-- The number of items of worker `c`: `ceil((T - c) / G)`, and `0` once `T ≤ c`. -/
def count (G T c : Nat) : Nat := (T - c + G - 1) / G

theorem mem_visits {G T c t : Nat} : t ∈ visits G T c ↔ t < T ∧ t % G = c := by
  simp [visits]

theorem count_eq_zero {G T c : Nat} (hc : T ≤ c) (hG : 0 < G) : count G T c = 0 := by
  unfold count
  rw [Nat.sub_eq_zero_of_le hc, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

/-- Worker `c < G` visits exactly `c + G * k` for `k < count`. -/
theorem visits_eq_image {G T c : Nat} (hG : 0 < G) (hc : c < G) :
    visits G T c = (Finset.range (count G T c)).image (fun k => c + G * k) := by
  ext t
  simp only [mem_visits, Finset.mem_image, Finset.mem_range, count]
  constructor
  · rintro ⟨ht, hm⟩
    refine ⟨t / G, ?_, ?_⟩
    · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hG]
      have := Nat.div_add_mod t G
      have h2 : (t / G + 1) * G = G * (t / G) + G := by ring
      omega
    · have := Nat.div_add_mod t G
      omega
  · rintro ⟨k, hk, rfl⟩
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hG] at hk
    have h2 : (k + 1) * G = G * k + G := by ring
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem card_visits {G T c : Nat} (hG : 0 < G) (hc : c < G) :
    (visits G T c).card = (T - c + G - 1) / G := by
  rw [visits_eq_image hG hc, Finset.card_image_of_injective _ (fun a b h => by
    have := Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel h); exact this),
    Finset.card_range]
  rfl

theorem visits_disjoint {G T c c' : Nat} (h : c ≠ c') :
    Disjoint (visits G T c) (visits G T c') := by
  rw [Finset.disjoint_left]
  intro t h1 h2
  rw [mem_visits] at h1 h2
  omega

/-- The worker visit sets for `c < G` cover exactly `{0, ..., T - 1}`. -/
theorem biUnion_visits {G T : Nat} (hG : 0 < G) :
    (Finset.range G).biUnion (visits G T) = Finset.range T := by
  ext t
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_visits]
  constructor
  · rintro ⟨c, _, ht, _⟩; exact ht
  · intro ht; exact ⟨t % G, Nat.mod_lt _ hG, ht, rfl⟩

/-- Every item belongs to exactly one worker `c < G`, namely `t % G`. -/
theorem existsUnique_worker {G T t : Nat} (hG : 0 < G) (ht : t < T) :
    ∃! c, c < G ∧ t ∈ visits G T c := by
  refine ⟨t % G, ⟨Nat.mod_lt _ hG, mem_visits.2 ⟨ht, rfl⟩⟩, ?_⟩
  rintro c ⟨_, hc⟩
  exact (mem_visits.1 hc).2.symm

/-- The per-worker item counts sum to `T`. -/
theorem sum_count {G T : Nat} (hG : 0 < G) :
    (Finset.range G).sum (fun c => (T - c + G - 1) / G) = T := by
  have h := congrArg Finset.card (biUnion_visits (T := T) hG)
  rw [Finset.card_biUnion (fun a _ b _ hab => visits_disjoint hab), Finset.card_range] at h
  exact (Finset.sum_congr rfl
    (fun c hc => (card_visits hG (Finset.mem_range.1 hc)).symm)).trans h

end StaticSchedule

namespace TileDecomp

/-- Linearize `(n, h, b)` as `(n * H + h) * B + b`. -/
def linear (H B n h b : Nat) : Nat := (n * H + h) * B + b

/-- Split a linear index by two nested divmods: `(t / B / H, t / B % H, t % B)`. -/
def split (H B t : Nat) : Nat × Nat × Nat := (t / B / H, t / B % H, t % B)

theorem linear_split {H B t : Nat} : linear H B (t / B / H) (t / B % H) (t % B) = t := by
  unfold linear
  have h1 := Nat.div_add_mod (t / B) H
  have h2 := Nat.div_add_mod t B
  rw [Nat.mul_comm (t / B / H) H, h1]
  rw [Nat.mul_comm (t / B) B]
  exact h2

theorem split_linear {H B n h b : Nat} (hH : h < H) (hB : b < B) :
    split H B (linear H B n h b) = (n, h, b) := by
  have hBpos : 0 < B := by omega
  have hHpos : 0 < H := by omega
  have e1 : ((n * H + h) * B + b) / B = n * H + h := by
    rw [Nat.mul_comm, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hB, Nat.add_zero]
  have e2 : ((n * H + h) * B + b) % B = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hB]
  have e3 : (n * H + h) / H = n := by
    rw [Nat.mul_comm, Nat.mul_add_div hHpos, Nat.div_eq_of_lt hH, Nat.add_zero]
  have e4 : (n * H + h) % H = h := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hH]
  simp only [split, linear, e1, e2, e3, e4]

theorem split_lt {H B N t : Nat} (hB : 0 < B) (hH : 0 < H) (ht : t < B * H * N) :
    t / B / H < N ∧ t / B % H < H ∧ t % B < B := by
  refine ⟨?_, Nat.mod_lt _ hH, Nat.mod_lt _ hB⟩
  rw [Nat.div_lt_iff_lt_mul hH, Nat.div_lt_iff_lt_mul hB]
  calc t < B * H * N := ht
    _ = N * H * B := by ring

theorem linear_lt {H B N n h b : Nat} (hn : n < N) (hh : h < H) (hb : b < B) :
    linear H B n h b < B * H * N := by
  unfold linear
  have h1 : (n * H + h + 1) ≤ N * H := by nlinarith
  calc (n * H + h) * B + b < (n * H + h + 1) * B := by nlinarith
    _ ≤ N * H * B := Nat.mul_le_mul_right _ h1
    _ = B * H * N := by ring

/-- For `B, H > 0`, `t ↦ (t / B / H, t / B % H, t % B)` is a bijection from
`{t < B * H * N}` onto triples `(n, h, b)` with `n < N`, `h < H`, `b < B`. -/
theorem split_bijOn {H B N : Nat} (hB : 0 < B) (hH : 0 < H) :
    Set.BijOn (fun t => (t / B / H, t / B % H, t % B)) (Set.Iio (B * H * N))
      (Set.Iio N ×ˢ Set.Iio H ×ˢ Set.Iio B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, b, c⟩ := split_lt hB hH (N := N) ht
    exact ⟨a, b, c⟩
  · intro t ht t' ht' h
    have := linear_split (H := H) (B := B) (t := t)
    have := linear_split (H := H) (B := B) (t := t')
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [← linear_split (H := H) (B := B) (t := t), ← linear_split (H := H) (B := B) (t := t'),
      h1, h2, h3]
  · rintro ⟨n, h, b⟩ ⟨hn, hh, hb⟩
    exact ⟨linear H B n h b, linear_lt hn hh hb, by
      have := split_linear (n := n) hh hb; simpa [split] using this⟩

end TileDecomp
