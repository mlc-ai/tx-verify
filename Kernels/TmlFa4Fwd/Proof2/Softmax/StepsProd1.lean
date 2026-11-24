-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsNarr1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ProdEq
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Gen.Prod1

@[expose] public section

/-! # The first round's bias products

The first round's products (pcs 3593 to 3849, `Gen.prod1_run`): each bias pair's halves widened,
packed, multiplied by the bias scale's pair and added to the score pair. The run's condition holds
by the kinds of its start values (bias halves, the scale word a positive real, the score pairs
reals; `prod1_ok`), and its end values are the products' closed forms (`prod1_pairs`: the scaled
bias plus the score, or `-∞` for a masked half, the form `mask_max` reads). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The register of half `n` of a round's bias loads (`base` 786 in the first round). -/
abbrev halfReg (base n : Nat) : Nat := base + 8 * (n / 8) + 7 - n % 8

/-- The payload of bias half `n`. -/
abbrev bbr (v : V) (n : Nat) : ℝ := v.br ⟨n / 8 % 16, Nat.mod_lt _ (by decide)⟩ (n % 8)

theorem halvesList_eq (v : V) : halvesList false v =
    (List.range 128).map fun n => (halfReg 786 n, hv16 (bpf v n) (bbr v n)) := by
  kernel_rfl

/-- The data table of the first round from its bias fence to its named-barrier arrival. -/
theorem valuesData_barr (v : V) : valuesData p L g ⟨.barr false, v, 0, []⟩ =
    valuesPairs .first v 64 ++ valuesRun p v ++ halvesList false v := by
  show _ ++ _ ++ (halvesList false v).take 128 = _
  rw [List.take_of_length_le (by unfold halvesList; rfl)]
  rfl

theorem barr_nodup (v : V) :
    ((valuesPairs .first v 64 ++ valuesRun p v ++ halvesList false v).map Prod.fst).Nodup :=
  nodup_of_nodupB (by kernel_rfl)

theorem valueOfD_barr {v : V} {q : Nat × Value}
    (hq : q ∈ valuesPairs .first v 64 ++ valuesRun p v ++ halvesList false v) :
    valueOfD p L g ⟨.barr false, v, 0, []⟩ q.1 = q.2 := by
  have := lookup_prefix (X := []) (barr_nodup (p := p) v) hq
  simp only [List.append_nil] at this
  simp only [valueOfD, valuesData_barr, this, Option.getD_some]

theorem barr_half (v : V) {n : Nat} (hn : n < 128) :
    valueOfD p L g ⟨.barr false, v, 0, []⟩ (halfReg 786 n) = hv16 (bpf v n) (bbr v n) :=
  valueOfD_barr (q := (halfReg 786 n, _)) (List.mem_append_right _ (by
    rw [halvesList_eq]; exact List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩))

theorem barr_pair (v : V) {j : Nat} (hj : j < 64) :
    valueOfD p L g ⟨.barr false, v, 0, []⟩ (7303 + j) =
      .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))) :=
  valueOfD_barr (q := (7303 + j, _)) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

/-- The values at pc 3593, after the scale-word reads (pcs 3591, 3592). -/
def vProd1 (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  Function.update (valueOfD p L g ⟨.barr false, v, 0, []⟩) 7135
    (.bits 32 (Epilogue.paramW p.invScaleBits))

theorem vProd1_half (v : V) {n : Nat} (hn : n < 128) :
    vProd1 p L g v (halfReg 786 n) = hv16 (bpf v n) (bbr v n) := by
  rw [vProd1, Function.update_of_ne (by simp only [halfReg]; omega)]
  exact barr_half v hn

theorem vProd1_pair (v : V) {j : Nat} (hj : j < 64) :
    vProd1 p L g v (7303 + j) =
      .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))) := by
  rw [vProd1, Function.update_of_ne (by omega)]
  exact barr_pair v hj

/-! ### The condition of the run -/

/-- The kinds of the run's start values. -/
def prod1K : List (Nat × Kd) :=
  (List.range' 786 128).map (fun r => (r, .h16)) ++ (7135, .s .pw) ::
    (List.range' 7303 64).map fun r => (r, .pr .fl)

theorem h16_hv16 (b : Bool) (r : ℝ) : Kd.h16.Has (hv16 b r) := by
  cases b
  · exact .inr rfl
  · exact .inl ⟨r, rfl⟩

theorem s14_pw (hp : Pre p L m) : SK.pw.Has (.bits 32 (Epilogue.paramW p.invScaleBits)) := by
  obtain ⟨s, t, -, ht, -, ht0⟩ := hp.scales
  exact paramW_pw ht ht0 (hp.values (14, p.invScaleBits) (by simp [Params.scalarWords])).1

theorem s14_read (hp : Pre p L m) : Assumption.readEReal .f32
    (.bits 32 (Epilogue.paramW p.invScaleBits)) = some (.ok ((s14 p : ℝ) : EReal)) :=
  readEReal_bits_fin (s14_word hp).1

theorem prod1K_has (hp : Pre p L m) (v : V) : ∀ q ∈ prod1K, q.2.Has (vProd1 p L g v q.1) := by
  intro q hq
  simp only [prod1K, List.mem_append, List.mem_cons, List.mem_map, List.mem_range'] at hq
  rcases hq with ⟨r, ⟨i, hi, rfl⟩, rfl⟩ | rfl | ⟨r, ⟨j, hj, rfl⟩, rfl⟩
  · -- a bias half: register `786 + i` is half `n` with `halfReg 786 n = 786 + i`
    have hn : halfReg 786 (8 * (i / 8) + 7 - i % 8) = 786 + 1 * i := by
      simp only [halfReg]; omega
    show Kd.h16.Has (vProd1 p L g v (786 + 1 * i))
    rw [← hn, vProd1_half v (by omega)]
    exact h16_hv16 _ _
  · show SK.pw.Has (vProd1 p L g v 7135)
    rw [vProd1, Function.update_self]
    exact s14_pw hp
  · show (Kd.pr .fl).Has (vProd1 p L g v (7303 + 1 * j))
    rw [show 7303 + 1 * j = 7303 + j by omega, vProd1_pair v (by omega)]
    exact pair_has (has_float_fl _) (has_float_fl _)

theorem prod1_facts0_eq (V : Nat → Value) :
    Gen.prod1_facts0 V = factsFrom ((Gen.prod1_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The role readings of the run's items are the widenings (`widenE`). -/
macro "fns_okprod1" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.prod1_items0, Gen.prod1_items1, Gen.prod1_items2,
    Gen.prod1_items3, Gen.prod1_items4, Gen.prod1_items5, Gen.prod1_items6, Gen.prod1_items7,
    Gen.prod1_items8, and_true, true_and]
  repeat' first | exact Gen.widenE_spec | exact Gen.packE_spec | constructor))

/-- The kinds after each piece of the products (literal lists; irreducible, so that only the
kernel's checks evaluate them). -/
@[irreducible] def pL1 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf prod1K) Gen.prod1_items0)
@[irreducible] def pL2 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL1) Gen.prod1_items1)
@[irreducible] def pL3 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL2) Gen.prod1_items2)
@[irreducible] def pL4 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL3) Gen.prod1_items3)
@[irreducible] def pL5 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL4) Gen.prod1_items4)
@[irreducible] def pL6 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts6 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL5) Gen.prod1_items5)
@[irreducible] def pL7 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts7 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL6) Gen.prod1_items6)
@[irreducible] def pL8 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts8 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL7) Gen.prod1_items7)
@[irreducible] def pL9 : List (Nat × Kd) :=
  kList ((Gen.prod1_facts9 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pL8) Gen.prod1_items8)

theorem prod1_kok (V : Nat → Value) :
    (kOk (kOf prod1K) Gen.prod1_items0 &&
      kNext prod1K Gen.prod1_items0 ((Gen.prod1_facts1 V).map Prod.fst) pL1 &&
      kOk (kOf pL1) Gen.prod1_items1 &&
      kNext pL1 Gen.prod1_items1 ((Gen.prod1_facts2 V).map Prod.fst) pL2 &&
      kOk (kOf pL2) Gen.prod1_items2 &&
      kNext pL2 Gen.prod1_items2 ((Gen.prod1_facts3 V).map Prod.fst) pL3 &&
      kOk (kOf pL3) Gen.prod1_items3 &&
      kNext pL3 Gen.prod1_items3 ((Gen.prod1_facts4 V).map Prod.fst) pL4 &&
      kOk (kOf pL4) Gen.prod1_items4 &&
      kNext pL4 Gen.prod1_items4 ((Gen.prod1_facts5 V).map Prod.fst) pL5 &&
      kOk (kOf pL5) Gen.prod1_items5 &&
      kNext pL5 Gen.prod1_items5 ((Gen.prod1_facts6 V).map Prod.fst) pL6 &&
      kOk (kOf pL6) Gen.prod1_items6 &&
      kNext pL6 Gen.prod1_items6 ((Gen.prod1_facts7 V).map Prod.fst) pL7 &&
      kOk (kOf pL7) Gen.prod1_items7 &&
      kNext pL7 Gen.prod1_items7 ((Gen.prod1_facts8 V).map Prod.fst) pL8 &&
      kOk (kOf pL8) Gen.prod1_items8 &&
      kNext pL8 Gen.prod1_items8 ((Gen.prod1_facts9 V).map Prod.fst) pL9) = true := by
  unfold prod1K
  kernel_rfl

theorem prod1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf prod1K r).Has (lookupD (Gen.prod1_facts0 V1) r)) :
    Gen.prod1_cond V1 ∧ ∀ r, (kOf pL9 r).Has (lookupD (Gen.prod1_facts9 V1) r) := by
  have h18 := prod1_kok V1
  have hn9 := (band_split h18).2
  have h17 := (band_split h18).1
  have hk8 := (band_split h17).2
  have h16 := (band_split h17).1
  have hn8 := (band_split h16).2
  have h15 := (band_split h16).1
  have hk7 := (band_split h15).2
  have h14 := (band_split h15).1
  have hn7 := (band_split h14).2
  have h13 := (band_split h14).1
  have hk6 := (band_split h13).2
  have h12 := (band_split h13).1
  have hn6 := (band_split h12).2
  have h11 := (band_split h12).1
  have hk5 := (band_split h11).2
  have h10 := (band_split h11).1
  have hn5 := (band_split h10).2
  have h9 := (band_split h10).1
  have hk4 := (band_split h9).2
  have h8 := (band_split h9).1
  have hn4 := (band_split h8).2
  have h7 := (band_split h8).1
  have hk3 := (band_split h7).2
  have h6 := (band_split h7).1
  have hn3 := (band_split h6).2
  have h5 := (band_split h6).1
  have hk2 := (band_split h5).2
  have h4 := (band_split h5).1
  have hn2 := (band_split h4).2
  have h3 := (band_split h4).1
  have hk1 := (band_split h3).2
  have h2 := (band_split h3).1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.prod1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts0 V1)) Gen.prod1_items0) = Gen.prod1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.prod1_items0 := by fns_okprod1
  obtain ⟨c0, k1⟩ := kpiece_lit (L := prod1K) (L' := pL1) (G := Gen.prod1_facts1 V1)
    (items := Gen.prod1_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.prod1_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts1 V1)) Gen.prod1_items1) = Gen.prod1_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.prod1_items1 := by fns_okprod1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := pL1) (L' := pL2) (G := Gen.prod1_facts2 V1)
    (items := Gen.prod1_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.prod1_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts2 V1)) Gen.prod1_items2) = Gen.prod1_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.prod1_items2 := by fns_okprod1
  obtain ⟨c2, k3⟩ := kpiece_lit (L := pL2) (L' := pL3) (G := Gen.prod1_facts3 V1)
    (items := Gen.prod1_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.prod1_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts3 V1)) Gen.prod1_items3) = Gen.prod1_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.prod1_items3 := by fns_okprod1
  obtain ⟨c3, k4⟩ := kpiece_lit (L := pL3) (L' := pL4) (G := Gen.prod1_facts4 V1)
    (items := Gen.prod1_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.prod1_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts4 V1)) Gen.prod1_items4) = Gen.prod1_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.prod1_items4 := by fns_okprod1
  obtain ⟨c4, k5⟩ := kpiece_lit (L := pL4) (L' := pL5) (G := Gen.prod1_facts5 V1)
    (items := Gen.prod1_items4) hG4 hk4 k4 hf4 hn5
  have hG5 : factsFrom ((Gen.prod1_facts6 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts5 V1)) Gen.prod1_items5) = Gen.prod1_facts6 V1 := by
    kernel_rfl
  have hf5 : kFns Gen.prod1_items5 := by fns_okprod1
  obtain ⟨c5, k6⟩ := kpiece_lit (L := pL5) (L' := pL6) (G := Gen.prod1_facts6 V1)
    (items := Gen.prod1_items5) hG5 hk5 k5 hf5 hn6
  have hG6 : factsFrom ((Gen.prod1_facts7 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts6 V1)) Gen.prod1_items6) = Gen.prod1_facts7 V1 := by
    kernel_rfl
  have hf6 : kFns Gen.prod1_items6 := by fns_okprod1
  obtain ⟨c6, k7⟩ := kpiece_lit (L := pL6) (L' := pL7) (G := Gen.prod1_facts7 V1)
    (items := Gen.prod1_items6) hG6 hk6 k6 hf6 hn7
  have hG7 : factsFrom ((Gen.prod1_facts8 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts7 V1)) Gen.prod1_items7) = Gen.prod1_facts8 V1 := by
    kernel_rfl
  have hf7 : kFns Gen.prod1_items7 := by fns_okprod1
  obtain ⟨c7, k8⟩ := kpiece_lit (L := pL7) (L' := pL8) (G := Gen.prod1_facts8 V1)
    (items := Gen.prod1_items7) hG7 hk7 k7 hf7 hn8
  have hG8 : factsFrom ((Gen.prod1_facts9 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prod1_facts8 V1)) Gen.prod1_items8) = Gen.prod1_facts9 V1 := by
    kernel_rfl
  have hf8 : kFns Gen.prod1_items8 := by fns_okprod1
  obtain ⟨c8, k9⟩ := kpiece_lit (L := pL8) (L' := pL9) (G := Gen.prod1_facts9 V1)
    (items := Gen.prod1_items8) hG8 hk8 k8 hf8 hn9
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, k9⟩

theorem prod1_ok (hp : Pre p L m) (v : V) : Gen.prod1_cond (vProd1 p L g v) := by
  have k0 : ∀ r, (kOf prod1K r).Has (lookupD (Gen.prod1_facts0 (vProd1 p L g v)) r) := by
    rw [prod1_facts0_eq]
    exact kstart (by kernel_rfl) (prod1K_has hp v)
  exact (prod1_chain _ k0).1

/-! ### The products' values -/

theorem prod_lane (W : Nat → Value) (v : V) {t : ℝ} {S : Value} (ht : 0 < t) (hS : Clean S)
    (hSr : Assumption.readEReal .f32 S = some (.ok (t : EReal))) {a b c : Nat} {n0 n1 : Nat}
    (ha : W a = hv16 (bpf v n0) (bbr v n0)) (hb : W b = hv16 (bpf v n1) (bbr v n1))
    (hc : W c = .pair (.float .f32 (v.score n0)) (.float .f32 (v.score n1))) :
    okVal (.bits 64 0) (fma2E (joinValue (okVal (.bits 32 0) (Gen.widenE [W a]))
      (okVal (.bits 32 0) (Gen.widenE [W b]))) (joinValue S S) (W c)) =
    .pair (bvl (bpf v n0) (bbr v n0 * t + v.score n0))
      (bvl (bpf v n1) (bbr v n1 * t + v.score n1)) := by
  rw [ha, hb, hc]
  exact prod_eq ht hS hSr

/-- **The products' values** at pc 3850, from the values at pc 3593. -/
theorem prod1_pairs (hp : Pre p L m) (v : V) : ∀ R, Holds R (Gen.prod1_facts9 (vProd1 p L g v)) →
    Holds R ((7896, joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits))) ::
      (7897, .pair (bvl (bpf v 0) (bps p v 0)) (bvl (bpf v 1) (bps p v 1))) ::
      (7899, .pair (bvl (bpf v 2) (bps p v 2)) (bvl (bpf v 3) (bps p v 3))) ::
      (7901, .pair (bvl (bpf v 4) (bps p v 4)) (bvl (bpf v 5) (bps p v 5))) ::
      (7903, .pair (bvl (bpf v 6) (bps p v 6)) (bvl (bpf v 7) (bps p v 7))) ::
      (7905, .pair (bvl (bpf v 8) (bps p v 8)) (bvl (bpf v 9) (bps p v 9))) ::
      (7907, .pair (bvl (bpf v 10) (bps p v 10)) (bvl (bpf v 11) (bps p v 11))) ::
      (7909, .pair (bvl (bpf v 12) (bps p v 12)) (bvl (bpf v 13) (bps p v 13))) ::
      (7911, .pair (bvl (bpf v 14) (bps p v 14)) (bvl (bpf v 15) (bps p v 15))) ::
      (7913, .pair (bvl (bpf v 16) (bps p v 16)) (bvl (bpf v 17) (bps p v 17))) ::
      (7915, .pair (bvl (bpf v 18) (bps p v 18)) (bvl (bpf v 19) (bps p v 19))) ::
      (7917, .pair (bvl (bpf v 20) (bps p v 20)) (bvl (bpf v 21) (bps p v 21))) ::
      (7919, .pair (bvl (bpf v 22) (bps p v 22)) (bvl (bpf v 23) (bps p v 23))) ::
      (7921, .pair (bvl (bpf v 24) (bps p v 24)) (bvl (bpf v 25) (bps p v 25))) ::
      (7923, .pair (bvl (bpf v 26) (bps p v 26)) (bvl (bpf v 27) (bps p v 27))) ::
      (7925, .pair (bvl (bpf v 28) (bps p v 28)) (bvl (bpf v 29) (bps p v 29))) ::
      (7927, .pair (bvl (bpf v 30) (bps p v 30)) (bvl (bpf v 31) (bps p v 31))) ::
      (7929, .pair (bvl (bpf v 32) (bps p v 32)) (bvl (bpf v 33) (bps p v 33))) ::
      (7931, .pair (bvl (bpf v 34) (bps p v 34)) (bvl (bpf v 35) (bps p v 35))) ::
      (7933, .pair (bvl (bpf v 36) (bps p v 36)) (bvl (bpf v 37) (bps p v 37))) ::
      (7935, .pair (bvl (bpf v 38) (bps p v 38)) (bvl (bpf v 39) (bps p v 39))) ::
      (7937, .pair (bvl (bpf v 40) (bps p v 40)) (bvl (bpf v 41) (bps p v 41))) ::
      (7939, .pair (bvl (bpf v 42) (bps p v 42)) (bvl (bpf v 43) (bps p v 43))) ::
      (7941, .pair (bvl (bpf v 44) (bps p v 44)) (bvl (bpf v 45) (bps p v 45))) ::
      (7943, .pair (bvl (bpf v 46) (bps p v 46)) (bvl (bpf v 47) (bps p v 47))) ::
      (7945, .pair (bvl (bpf v 48) (bps p v 48)) (bvl (bpf v 49) (bps p v 49))) ::
      (7947, .pair (bvl (bpf v 50) (bps p v 50)) (bvl (bpf v 51) (bps p v 51))) ::
      (7949, .pair (bvl (bpf v 52) (bps p v 52)) (bvl (bpf v 53) (bps p v 53))) ::
      (7951, .pair (bvl (bpf v 54) (bps p v 54)) (bvl (bpf v 55) (bps p v 55))) ::
      (7953, .pair (bvl (bpf v 56) (bps p v 56)) (bvl (bpf v 57) (bps p v 57))) ::
      (7955, .pair (bvl (bpf v 58) (bps p v 58)) (bvl (bpf v 59) (bps p v 59))) ::
      (7957, .pair (bvl (bpf v 60) (bps p v 60)) (bvl (bpf v 61) (bps p v 61))) ::
      (7959, .pair (bvl (bpf v 62) (bps p v 62)) (bvl (bpf v 63) (bps p v 63))) ::
      (7961, .pair (bvl (bpf v 64) (bps p v 64)) (bvl (bpf v 65) (bps p v 65))) ::
      (7963, .pair (bvl (bpf v 66) (bps p v 66)) (bvl (bpf v 67) (bps p v 67))) ::
      (7965, .pair (bvl (bpf v 68) (bps p v 68)) (bvl (bpf v 69) (bps p v 69))) ::
      (7967, .pair (bvl (bpf v 70) (bps p v 70)) (bvl (bpf v 71) (bps p v 71))) ::
      (7969, .pair (bvl (bpf v 72) (bps p v 72)) (bvl (bpf v 73) (bps p v 73))) ::
      (7971, .pair (bvl (bpf v 74) (bps p v 74)) (bvl (bpf v 75) (bps p v 75))) ::
      (7973, .pair (bvl (bpf v 76) (bps p v 76)) (bvl (bpf v 77) (bps p v 77))) ::
      (7975, .pair (bvl (bpf v 78) (bps p v 78)) (bvl (bpf v 79) (bps p v 79))) ::
      (7977, .pair (bvl (bpf v 80) (bps p v 80)) (bvl (bpf v 81) (bps p v 81))) ::
      (7979, .pair (bvl (bpf v 82) (bps p v 82)) (bvl (bpf v 83) (bps p v 83))) ::
      (7981, .pair (bvl (bpf v 84) (bps p v 84)) (bvl (bpf v 85) (bps p v 85))) ::
      (7983, .pair (bvl (bpf v 86) (bps p v 86)) (bvl (bpf v 87) (bps p v 87))) ::
      (7985, .pair (bvl (bpf v 88) (bps p v 88)) (bvl (bpf v 89) (bps p v 89))) ::
      (7987, .pair (bvl (bpf v 90) (bps p v 90)) (bvl (bpf v 91) (bps p v 91))) ::
      (7989, .pair (bvl (bpf v 92) (bps p v 92)) (bvl (bpf v 93) (bps p v 93))) ::
      (7991, .pair (bvl (bpf v 94) (bps p v 94)) (bvl (bpf v 95) (bps p v 95))) ::
      (7993, .pair (bvl (bpf v 96) (bps p v 96)) (bvl (bpf v 97) (bps p v 97))) ::
      (7995, .pair (bvl (bpf v 98) (bps p v 98)) (bvl (bpf v 99) (bps p v 99))) ::
      (7997, .pair (bvl (bpf v 100) (bps p v 100)) (bvl (bpf v 101) (bps p v 101))) ::
      (7999, .pair (bvl (bpf v 102) (bps p v 102)) (bvl (bpf v 103) (bps p v 103))) ::
      (8001, .pair (bvl (bpf v 104) (bps p v 104)) (bvl (bpf v 105) (bps p v 105))) ::
      (8003, .pair (bvl (bpf v 106) (bps p v 106)) (bvl (bpf v 107) (bps p v 107))) ::
      (8005, .pair (bvl (bpf v 108) (bps p v 108)) (bvl (bpf v 109) (bps p v 109))) ::
      (8007, .pair (bvl (bpf v 110) (bps p v 110)) (bvl (bpf v 111) (bps p v 111))) ::
      (8009, .pair (bvl (bpf v 112) (bps p v 112)) (bvl (bpf v 113) (bps p v 113))) ::
      (8011, .pair (bvl (bpf v 114) (bps p v 114)) (bvl (bpf v 115) (bps p v 115))) ::
      (8013, .pair (bvl (bpf v 116) (bps p v 116)) (bvl (bpf v 117) (bps p v 117))) ::
      (8015, .pair (bvl (bpf v 118) (bps p v 118)) (bvl (bpf v 119) (bps p v 119))) ::
      (8017, .pair (bvl (bpf v 120) (bps p v 120)) (bvl (bpf v 121) (bps p v 121))) ::
      (8019, .pair (bvl (bpf v 122) (bps p v 122)) (bvl (bpf v 123) (bps p v 123))) ::
      (8021, .pair (bvl (bpf v 124) (bps p v 124)) (bvl (bpf v 125) (bps p v 125))) ::
      (8023, .pair (bvl (bpf v 126) (bps p v 126)) (bvl (bpf v 127) (bps p v 127))) ::
      []) := by
  intro R hR
  have ht := (s14_word hp).2
  have hS := SK.clean (s14_pw hp)
  have hSr := s14_read hp
  have hS7135 : vProd1 p L g v 7135 = .bits 32 (Epilogue.paramW p.invScaleBits) := by
    rw [vProd1, Function.update_self]
  have hh : ∀ n < 128, vProd1 p L g v (halfReg 786 n) = hv16 (bpf v n) (bbr v n) :=
    fun n hn => vProd1_half v hn
  have hx : ∀ j < 64, vProd1 p L g v (7303 + j) =
      .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))) :=
    fun j hj => vProd1_pair v hj
  simp only [Gen.prod1_facts9, holds_cons, holds_nil] at hR ⊢
  obtain ⟨h7896, hR⟩ := hR
  refine ⟨by rw [h7896, Gen.prod1_v3596, hS7135], ?_⟩
  obtain ⟨h7897, hR⟩ := hR
  refine ⟨by
    rw [h7897, Gen.prod1_v3597, Gen.prod1_v3595, Gen.prod1_v3593, Gen.prod1_v3594,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 0 (by decide))
      (hh 1 (by decide)) (hx 0 (by decide))), ?_⟩
  obtain ⟨h7899, hR⟩ := hR
  refine ⟨by
    rw [h7899, Gen.prod1_v3601, Gen.prod1_v3600, Gen.prod1_v3598, Gen.prod1_v3599,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 2 (by decide))
      (hh 3 (by decide)) (hx 1 (by decide))), ?_⟩
  obtain ⟨h7901, hR⟩ := hR
  refine ⟨by
    rw [h7901, Gen.prod1_v3605, Gen.prod1_v3604, Gen.prod1_v3602, Gen.prod1_v3603,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 4 (by decide))
      (hh 5 (by decide)) (hx 2 (by decide))), ?_⟩
  obtain ⟨h7903, hR⟩ := hR
  refine ⟨by
    rw [h7903, Gen.prod1_v3609, Gen.prod1_v3608, Gen.prod1_v3606, Gen.prod1_v3607,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 6 (by decide))
      (hh 7 (by decide)) (hx 3 (by decide))), ?_⟩
  obtain ⟨h7905, hR⟩ := hR
  refine ⟨by
    rw [h7905, Gen.prod1_v3613, Gen.prod1_v3612, Gen.prod1_v3610, Gen.prod1_v3611,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 8 (by decide))
      (hh 9 (by decide)) (hx 4 (by decide))), ?_⟩
  obtain ⟨h7907, hR⟩ := hR
  refine ⟨by
    rw [h7907, Gen.prod1_v3617, Gen.prod1_v3616, Gen.prod1_v3614, Gen.prod1_v3615,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 10 (by decide))
      (hh 11 (by decide)) (hx 5 (by decide))), ?_⟩
  obtain ⟨h7909, hR⟩ := hR
  refine ⟨by
    rw [h7909, Gen.prod1_v3621, Gen.prod1_v3620, Gen.prod1_v3618, Gen.prod1_v3619,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 12 (by decide))
      (hh 13 (by decide)) (hx 6 (by decide))), ?_⟩
  obtain ⟨h7911, hR⟩ := hR
  refine ⟨by
    rw [h7911, Gen.prod1_v3625, Gen.prod1_v3624, Gen.prod1_v3622, Gen.prod1_v3623,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 14 (by decide))
      (hh 15 (by decide)) (hx 7 (by decide))), ?_⟩
  obtain ⟨h7913, hR⟩ := hR
  refine ⟨by
    rw [h7913, Gen.prod1_v3629, Gen.prod1_v3628, Gen.prod1_v3626, Gen.prod1_v3627,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 16 (by decide))
      (hh 17 (by decide)) (hx 8 (by decide))), ?_⟩
  obtain ⟨h7915, hR⟩ := hR
  refine ⟨by
    rw [h7915, Gen.prod1_v3633, Gen.prod1_v3632, Gen.prod1_v3630, Gen.prod1_v3631,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 18 (by decide))
      (hh 19 (by decide)) (hx 9 (by decide))), ?_⟩
  obtain ⟨h7917, hR⟩ := hR
  refine ⟨by
    rw [h7917, Gen.prod1_v3637, Gen.prod1_v3636, Gen.prod1_v3634, Gen.prod1_v3635,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 20 (by decide))
      (hh 21 (by decide)) (hx 10 (by decide))), ?_⟩
  obtain ⟨h7919, hR⟩ := hR
  refine ⟨by
    rw [h7919, Gen.prod1_v3641, Gen.prod1_v3640, Gen.prod1_v3638, Gen.prod1_v3639,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 22 (by decide))
      (hh 23 (by decide)) (hx 11 (by decide))), ?_⟩
  obtain ⟨h7921, hR⟩ := hR
  refine ⟨by
    rw [h7921, Gen.prod1_v3645, Gen.prod1_v3644, Gen.prod1_v3642, Gen.prod1_v3643,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 24 (by decide))
      (hh 25 (by decide)) (hx 12 (by decide))), ?_⟩
  obtain ⟨h7923, hR⟩ := hR
  refine ⟨by
    rw [h7923, Gen.prod1_v3649, Gen.prod1_v3648, Gen.prod1_v3646, Gen.prod1_v3647,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 26 (by decide))
      (hh 27 (by decide)) (hx 13 (by decide))), ?_⟩
  obtain ⟨h7925, hR⟩ := hR
  refine ⟨by
    rw [h7925, Gen.prod1_v3653, Gen.prod1_v3652, Gen.prod1_v3650, Gen.prod1_v3651,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 28 (by decide))
      (hh 29 (by decide)) (hx 14 (by decide))), ?_⟩
  obtain ⟨h7927, hR⟩ := hR
  refine ⟨by
    rw [h7927, Gen.prod1_v3657, Gen.prod1_v3656, Gen.prod1_v3654, Gen.prod1_v3655,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 30 (by decide))
      (hh 31 (by decide)) (hx 15 (by decide))), ?_⟩
  obtain ⟨h7929, hR⟩ := hR
  refine ⟨by
    rw [h7929, Gen.prod1_v3661, Gen.prod1_v3660, Gen.prod1_v3658, Gen.prod1_v3659,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 32 (by decide))
      (hh 33 (by decide)) (hx 16 (by decide))), ?_⟩
  obtain ⟨h7931, hR⟩ := hR
  refine ⟨by
    rw [h7931, Gen.prod1_v3665, Gen.prod1_v3664, Gen.prod1_v3662, Gen.prod1_v3663,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 34 (by decide))
      (hh 35 (by decide)) (hx 17 (by decide))), ?_⟩
  obtain ⟨h7933, hR⟩ := hR
  refine ⟨by
    rw [h7933, Gen.prod1_v3669, Gen.prod1_v3668, Gen.prod1_v3666, Gen.prod1_v3667,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 36 (by decide))
      (hh 37 (by decide)) (hx 18 (by decide))), ?_⟩
  obtain ⟨h7935, hR⟩ := hR
  refine ⟨by
    rw [h7935, Gen.prod1_v3673, Gen.prod1_v3672, Gen.prod1_v3670, Gen.prod1_v3671,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 38 (by decide))
      (hh 39 (by decide)) (hx 19 (by decide))), ?_⟩
  obtain ⟨h7937, hR⟩ := hR
  refine ⟨by
    rw [h7937, Gen.prod1_v3677, Gen.prod1_v3676, Gen.prod1_v3674, Gen.prod1_v3675,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 40 (by decide))
      (hh 41 (by decide)) (hx 20 (by decide))), ?_⟩
  obtain ⟨h7939, hR⟩ := hR
  refine ⟨by
    rw [h7939, Gen.prod1_v3681, Gen.prod1_v3680, Gen.prod1_v3678, Gen.prod1_v3679,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 42 (by decide))
      (hh 43 (by decide)) (hx 21 (by decide))), ?_⟩
  obtain ⟨h7941, hR⟩ := hR
  refine ⟨by
    rw [h7941, Gen.prod1_v3685, Gen.prod1_v3684, Gen.prod1_v3682, Gen.prod1_v3683,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 44 (by decide))
      (hh 45 (by decide)) (hx 22 (by decide))), ?_⟩
  obtain ⟨h7943, hR⟩ := hR
  refine ⟨by
    rw [h7943, Gen.prod1_v3689, Gen.prod1_v3688, Gen.prod1_v3686, Gen.prod1_v3687,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 46 (by decide))
      (hh 47 (by decide)) (hx 23 (by decide))), ?_⟩
  obtain ⟨h7945, hR⟩ := hR
  refine ⟨by
    rw [h7945, Gen.prod1_v3693, Gen.prod1_v3692, Gen.prod1_v3690, Gen.prod1_v3691,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 48 (by decide))
      (hh 49 (by decide)) (hx 24 (by decide))), ?_⟩
  obtain ⟨h7947, hR⟩ := hR
  refine ⟨by
    rw [h7947, Gen.prod1_v3697, Gen.prod1_v3696, Gen.prod1_v3694, Gen.prod1_v3695,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 50 (by decide))
      (hh 51 (by decide)) (hx 25 (by decide))), ?_⟩
  obtain ⟨h7949, hR⟩ := hR
  refine ⟨by
    rw [h7949, Gen.prod1_v3701, Gen.prod1_v3700, Gen.prod1_v3698, Gen.prod1_v3699,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 52 (by decide))
      (hh 53 (by decide)) (hx 26 (by decide))), ?_⟩
  obtain ⟨h7951, hR⟩ := hR
  refine ⟨by
    rw [h7951, Gen.prod1_v3705, Gen.prod1_v3704, Gen.prod1_v3702, Gen.prod1_v3703,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 54 (by decide))
      (hh 55 (by decide)) (hx 27 (by decide))), ?_⟩
  obtain ⟨h7953, hR⟩ := hR
  refine ⟨by
    rw [h7953, Gen.prod1_v3709, Gen.prod1_v3708, Gen.prod1_v3706, Gen.prod1_v3707,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 56 (by decide))
      (hh 57 (by decide)) (hx 28 (by decide))), ?_⟩
  obtain ⟨h7955, hR⟩ := hR
  refine ⟨by
    rw [h7955, Gen.prod1_v3713, Gen.prod1_v3712, Gen.prod1_v3710, Gen.prod1_v3711,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 58 (by decide))
      (hh 59 (by decide)) (hx 29 (by decide))), ?_⟩
  obtain ⟨h7957, hR⟩ := hR
  refine ⟨by
    rw [h7957, Gen.prod1_v3717, Gen.prod1_v3716, Gen.prod1_v3714, Gen.prod1_v3715,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 60 (by decide))
      (hh 61 (by decide)) (hx 30 (by decide))), ?_⟩
  obtain ⟨h7959, hR⟩ := hR
  refine ⟨by
    rw [h7959, Gen.prod1_v3721, Gen.prod1_v3720, Gen.prod1_v3718, Gen.prod1_v3719,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 62 (by decide))
      (hh 63 (by decide)) (hx 31 (by decide))), ?_⟩
  obtain ⟨h7961, hR⟩ := hR
  refine ⟨by
    rw [h7961, Gen.prod1_v3725, Gen.prod1_v3724, Gen.prod1_v3722, Gen.prod1_v3723,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 64 (by decide))
      (hh 65 (by decide)) (hx 32 (by decide))), ?_⟩
  obtain ⟨h7963, hR⟩ := hR
  refine ⟨by
    rw [h7963, Gen.prod1_v3729, Gen.prod1_v3728, Gen.prod1_v3726, Gen.prod1_v3727,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 66 (by decide))
      (hh 67 (by decide)) (hx 33 (by decide))), ?_⟩
  obtain ⟨h7965, hR⟩ := hR
  refine ⟨by
    rw [h7965, Gen.prod1_v3733, Gen.prod1_v3732, Gen.prod1_v3730, Gen.prod1_v3731,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 68 (by decide))
      (hh 69 (by decide)) (hx 34 (by decide))), ?_⟩
  obtain ⟨h7967, hR⟩ := hR
  refine ⟨by
    rw [h7967, Gen.prod1_v3737, Gen.prod1_v3736, Gen.prod1_v3734, Gen.prod1_v3735,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 70 (by decide))
      (hh 71 (by decide)) (hx 35 (by decide))), ?_⟩
  obtain ⟨h7969, hR⟩ := hR
  refine ⟨by
    rw [h7969, Gen.prod1_v3741, Gen.prod1_v3740, Gen.prod1_v3738, Gen.prod1_v3739,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 72 (by decide))
      (hh 73 (by decide)) (hx 36 (by decide))), ?_⟩
  obtain ⟨h7971, hR⟩ := hR
  refine ⟨by
    rw [h7971, Gen.prod1_v3745, Gen.prod1_v3744, Gen.prod1_v3742, Gen.prod1_v3743,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 74 (by decide))
      (hh 75 (by decide)) (hx 37 (by decide))), ?_⟩
  obtain ⟨h7973, hR⟩ := hR
  refine ⟨by
    rw [h7973, Gen.prod1_v3749, Gen.prod1_v3748, Gen.prod1_v3746, Gen.prod1_v3747,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 76 (by decide))
      (hh 77 (by decide)) (hx 38 (by decide))), ?_⟩
  obtain ⟨h7975, hR⟩ := hR
  refine ⟨by
    rw [h7975, Gen.prod1_v3753, Gen.prod1_v3752, Gen.prod1_v3750, Gen.prod1_v3751,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 78 (by decide))
      (hh 79 (by decide)) (hx 39 (by decide))), ?_⟩
  obtain ⟨h7977, hR⟩ := hR
  refine ⟨by
    rw [h7977, Gen.prod1_v3757, Gen.prod1_v3756, Gen.prod1_v3754, Gen.prod1_v3755,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 80 (by decide))
      (hh 81 (by decide)) (hx 40 (by decide))), ?_⟩
  obtain ⟨h7979, hR⟩ := hR
  refine ⟨by
    rw [h7979, Gen.prod1_v3761, Gen.prod1_v3760, Gen.prod1_v3758, Gen.prod1_v3759,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 82 (by decide))
      (hh 83 (by decide)) (hx 41 (by decide))), ?_⟩
  obtain ⟨h7981, hR⟩ := hR
  refine ⟨by
    rw [h7981, Gen.prod1_v3765, Gen.prod1_v3764, Gen.prod1_v3762, Gen.prod1_v3763,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 84 (by decide))
      (hh 85 (by decide)) (hx 42 (by decide))), ?_⟩
  obtain ⟨h7983, hR⟩ := hR
  refine ⟨by
    rw [h7983, Gen.prod1_v3769, Gen.prod1_v3768, Gen.prod1_v3766, Gen.prod1_v3767,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 86 (by decide))
      (hh 87 (by decide)) (hx 43 (by decide))), ?_⟩
  obtain ⟨h7985, hR⟩ := hR
  refine ⟨by
    rw [h7985, Gen.prod1_v3773, Gen.prod1_v3772, Gen.prod1_v3770, Gen.prod1_v3771,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 88 (by decide))
      (hh 89 (by decide)) (hx 44 (by decide))), ?_⟩
  obtain ⟨h7987, hR⟩ := hR
  refine ⟨by
    rw [h7987, Gen.prod1_v3777, Gen.prod1_v3776, Gen.prod1_v3774, Gen.prod1_v3775,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 90 (by decide))
      (hh 91 (by decide)) (hx 45 (by decide))), ?_⟩
  obtain ⟨h7989, hR⟩ := hR
  refine ⟨by
    rw [h7989, Gen.prod1_v3781, Gen.prod1_v3780, Gen.prod1_v3778, Gen.prod1_v3779,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 92 (by decide))
      (hh 93 (by decide)) (hx 46 (by decide))), ?_⟩
  obtain ⟨h7991, hR⟩ := hR
  refine ⟨by
    rw [h7991, Gen.prod1_v3785, Gen.prod1_v3784, Gen.prod1_v3782, Gen.prod1_v3783,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 94 (by decide))
      (hh 95 (by decide)) (hx 47 (by decide))), ?_⟩
  obtain ⟨h7993, hR⟩ := hR
  refine ⟨by
    rw [h7993, Gen.prod1_v3789, Gen.prod1_v3788, Gen.prod1_v3786, Gen.prod1_v3787,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 96 (by decide))
      (hh 97 (by decide)) (hx 48 (by decide))), ?_⟩
  obtain ⟨h7995, hR⟩ := hR
  refine ⟨by
    rw [h7995, Gen.prod1_v3793, Gen.prod1_v3792, Gen.prod1_v3790, Gen.prod1_v3791,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 98 (by decide))
      (hh 99 (by decide)) (hx 49 (by decide))), ?_⟩
  obtain ⟨h7997, hR⟩ := hR
  refine ⟨by
    rw [h7997, Gen.prod1_v3797, Gen.prod1_v3796, Gen.prod1_v3794, Gen.prod1_v3795,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 100 (by decide))
      (hh 101 (by decide)) (hx 50 (by decide))), ?_⟩
  obtain ⟨h7999, hR⟩ := hR
  refine ⟨by
    rw [h7999, Gen.prod1_v3801, Gen.prod1_v3800, Gen.prod1_v3798, Gen.prod1_v3799,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 102 (by decide))
      (hh 103 (by decide)) (hx 51 (by decide))), ?_⟩
  obtain ⟨h8001, hR⟩ := hR
  refine ⟨by
    rw [h8001, Gen.prod1_v3805, Gen.prod1_v3804, Gen.prod1_v3802, Gen.prod1_v3803,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 104 (by decide))
      (hh 105 (by decide)) (hx 52 (by decide))), ?_⟩
  obtain ⟨h8003, hR⟩ := hR
  refine ⟨by
    rw [h8003, Gen.prod1_v3809, Gen.prod1_v3808, Gen.prod1_v3806, Gen.prod1_v3807,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 106 (by decide))
      (hh 107 (by decide)) (hx 53 (by decide))), ?_⟩
  obtain ⟨h8005, hR⟩ := hR
  refine ⟨by
    rw [h8005, Gen.prod1_v3813, Gen.prod1_v3812, Gen.prod1_v3810, Gen.prod1_v3811,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 108 (by decide))
      (hh 109 (by decide)) (hx 54 (by decide))), ?_⟩
  obtain ⟨h8007, hR⟩ := hR
  refine ⟨by
    rw [h8007, Gen.prod1_v3817, Gen.prod1_v3816, Gen.prod1_v3814, Gen.prod1_v3815,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 110 (by decide))
      (hh 111 (by decide)) (hx 55 (by decide))), ?_⟩
  obtain ⟨h8009, hR⟩ := hR
  refine ⟨by
    rw [h8009, Gen.prod1_v3821, Gen.prod1_v3820, Gen.prod1_v3818, Gen.prod1_v3819,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 112 (by decide))
      (hh 113 (by decide)) (hx 56 (by decide))), ?_⟩
  obtain ⟨h8011, hR⟩ := hR
  refine ⟨by
    rw [h8011, Gen.prod1_v3825, Gen.prod1_v3824, Gen.prod1_v3822, Gen.prod1_v3823,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 114 (by decide))
      (hh 115 (by decide)) (hx 57 (by decide))), ?_⟩
  obtain ⟨h8013, hR⟩ := hR
  refine ⟨by
    rw [h8013, Gen.prod1_v3829, Gen.prod1_v3828, Gen.prod1_v3826, Gen.prod1_v3827,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 116 (by decide))
      (hh 117 (by decide)) (hx 58 (by decide))), ?_⟩
  obtain ⟨h8015, hR⟩ := hR
  refine ⟨by
    rw [h8015, Gen.prod1_v3833, Gen.prod1_v3832, Gen.prod1_v3830, Gen.prod1_v3831,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 118 (by decide))
      (hh 119 (by decide)) (hx 59 (by decide))), ?_⟩
  obtain ⟨h8017, hR⟩ := hR
  refine ⟨by
    rw [h8017, Gen.prod1_v3837, Gen.prod1_v3836, Gen.prod1_v3834, Gen.prod1_v3835,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 120 (by decide))
      (hh 121 (by decide)) (hx 60 (by decide))), ?_⟩
  obtain ⟨h8019, hR⟩ := hR
  refine ⟨by
    rw [h8019, Gen.prod1_v3841, Gen.prod1_v3840, Gen.prod1_v3838, Gen.prod1_v3839,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 122 (by decide))
      (hh 123 (by decide)) (hx 61 (by decide))), ?_⟩
  obtain ⟨h8021, hR⟩ := hR
  refine ⟨by
    rw [h8021, Gen.prod1_v3845, Gen.prod1_v3844, Gen.prod1_v3842, Gen.prod1_v3843,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 124 (by decide))
      (hh 125 (by decide)) (hx 62 (by decide))), ?_⟩
  obtain ⟨h8023, hR⟩ := hR
  refine ⟨by
    rw [h8023, Gen.prod1_v3849, Gen.prod1_v3848, Gen.prod1_v3846, Gen.prod1_v3847,
      Gen.prod1_v3596, hS7135]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 126 (by decide))
      (hh 127 (by decide)) (hx 63 (by decide))), ?_⟩
  trivial

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
