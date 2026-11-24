-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsProd1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Gen.ProdB

@[expose] public section

/-! # The bias round's products

The bias round's products (pcs 5279 to 5534, `Gen.prodB_run`), as the first round's
(`StepsProd1.lean`): each bias pair's halves widened, packed, multiplied by the bias scale's pair
(register 7896, a value of the bias round's table) and added to the score pair. The run's
condition holds by the kinds of its start values (`prodB_ok`), and its end values are the
products' closed forms (`prodB_pairs`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem halvesListB_eq (v : V) : halvesList true v =
    (List.range 128).map fun n => (halfReg 914 n, hv16 (bpf v n) (bbr v n)) := by
  kernel_rfl

/-- The data table of a bias round at its named-barrier arrival. -/
theorem valuesData_barrB (v : V) : valuesData p L g ⟨.barr true, v, 0, []⟩ =
    valuesPairs .bias v 64 ++ valuesRun p v ++ halvesList true v := by
  show _ ++ _ ++ (halvesList true v).take 128 = _
  rw [List.take_of_length_le (by unfold halvesList; rfl)]
  rfl

theorem barrB_nodup (v : V) :
    ((valuesPairs .bias v 64 ++ valuesRun p v ++ halvesList true v).map Prod.fst).Nodup :=
  nodup_of_nodupB (by kernel_rfl)

theorem valueOfD_barrB {v : V} {q : Nat × Value}
    (hq : q ∈ valuesPairs .bias v 64 ++ valuesRun p v ++ halvesList true v) :
    valueOfD p L g ⟨.barr true, v, 0, []⟩ q.1 = q.2 := by
  have := lookup_prefix (X := []) (barrB_nodup (p := p) v) hq
  simp only [List.append_nil] at this
  simp only [valueOfD, valuesData_barrB, this, Option.getD_some]

theorem barrB_half (v : V) {n : Nat} (hn : n < 128) :
    valueOfD p L g ⟨.barr true, v, 0, []⟩ (halfReg 914 n) = hv16 (bpf v n) (bbr v n) :=
  valueOfD_barrB (q := (halfReg 914 n, _)) (List.mem_append_right _ (by
    rw [halvesListB_eq]; exact List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩))

theorem barrB_pair (v : V) {j : Nat} (hj : j < 64) :
    valueOfD p L g ⟨.barr true, v, 0, []⟩ (7367 + j) =
      .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))) :=
  valueOfD_barrB (q := (7367 + j, _)) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

/-- The bias scale's pair in the bias round's table. -/
theorem barrB_scale (v : V) : valueOfD p L g ⟨.barr true, v, 0, []⟩ 7896 =
    joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits)) := by
  rw [valueOfD_ctl _ (by decide)]
  kernel_rfl

/-- The values at pc 5279: the arrival state's. -/
abbrev vProdB (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  valueOfD p L g ⟨.barr true, v, 0, []⟩

/-! ### The condition of the run -/

/-- The kinds of the run's start values. -/
def prodBK : List (Nat × Kd) :=
  (List.range' 914 128).map (fun r => (r, .h16)) ++ (7896, .pr .pw) ::
    (List.range' 7367 64).map fun r => (r, .pr .fl)

theorem prodBK_has (hp : Pre p L m) (v : V) :
    ∀ q ∈ prodBK, q.2.Has (vProdB p L g v q.1) := by
  intro q hq
  simp only [prodBK, List.mem_append, List.mem_cons, List.mem_map, List.mem_range'] at hq
  rcases hq with ⟨r, ⟨i, hi, rfl⟩, rfl⟩ | rfl | ⟨r, ⟨j, hj, rfl⟩, rfl⟩
  · have hn : halfReg 914 (8 * (i / 8) + 7 - i % 8) = 914 + 1 * i := by
      simp only [halfReg]; omega
    show Kd.h16.Has (vProdB p L g v (914 + 1 * i))
    rw [← hn, vProdB, barrB_half v (by omega)]
    exact h16_hv16 _ _
  · show (Kd.pr .pw).Has (vProdB p L g v 7896)
    rw [vProdB, barrB_scale]
    exact join_has (s14_pw hp) (s14_pw hp)
  · show (Kd.pr .fl).Has (vProdB p L g v (7367 + 1 * j))
    rw [show 7367 + 1 * j = 7367 + j by omega, vProdB, barrB_pair v (by omega)]
    exact pair_has (has_float_fl _) (has_float_fl _)

theorem prodB_facts0_eq (V : Nat → Value) :
    Gen.prodB_facts0 V = factsFrom ((Gen.prodB_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The role readings of the run's items are the widenings (`widenE`). -/
macro "fns_okprodB" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.prodB_items0, Gen.prodB_items1, Gen.prodB_items2,
    Gen.prodB_items3, Gen.prodB_items4, Gen.prodB_items5, Gen.prodB_items6, Gen.prodB_items7,
    and_true, true_and]
  repeat' first | exact Gen.widenE_spec | exact Gen.packE_spec | constructor))

/-- The kinds after each piece of the products. -/
@[irreducible] def pB1 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf prodBK) Gen.prodB_items0)
@[irreducible] def pB2 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB1) Gen.prodB_items1)
@[irreducible] def pB3 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB2) Gen.prodB_items2)
@[irreducible] def pB4 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB3) Gen.prodB_items3)
@[irreducible] def pB5 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB4) Gen.prodB_items4)
@[irreducible] def pB6 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts6 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB5) Gen.prodB_items5)
@[irreducible] def pB7 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts7 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB6) Gen.prodB_items6)
@[irreducible] def pB8 : List (Nat × Kd) :=
  kList ((Gen.prodB_facts8 fun _ => .pred false).map Prod.fst)
    (kOut (kOf pB7) Gen.prodB_items7)

theorem prodB_kok (V : Nat → Value) :
    (kOk (kOf prodBK) Gen.prodB_items0 &&
      kNext prodBK Gen.prodB_items0 ((Gen.prodB_facts1 V).map Prod.fst) pB1 &&
      kOk (kOf pB1) Gen.prodB_items1 &&
      kNext pB1 Gen.prodB_items1 ((Gen.prodB_facts2 V).map Prod.fst) pB2 &&
      kOk (kOf pB2) Gen.prodB_items2 &&
      kNext pB2 Gen.prodB_items2 ((Gen.prodB_facts3 V).map Prod.fst) pB3 &&
      kOk (kOf pB3) Gen.prodB_items3 &&
      kNext pB3 Gen.prodB_items3 ((Gen.prodB_facts4 V).map Prod.fst) pB4 &&
      kOk (kOf pB4) Gen.prodB_items4 &&
      kNext pB4 Gen.prodB_items4 ((Gen.prodB_facts5 V).map Prod.fst) pB5 &&
      kOk (kOf pB5) Gen.prodB_items5 &&
      kNext pB5 Gen.prodB_items5 ((Gen.prodB_facts6 V).map Prod.fst) pB6 &&
      kOk (kOf pB6) Gen.prodB_items6 &&
      kNext pB6 Gen.prodB_items6 ((Gen.prodB_facts7 V).map Prod.fst) pB7 &&
      kOk (kOf pB7) Gen.prodB_items7 &&
      kNext pB7 Gen.prodB_items7 ((Gen.prodB_facts8 V).map Prod.fst) pB8) = true := by
  unfold prodBK
  kernel_rfl

theorem prodB_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf prodBK r).Has (lookupD (Gen.prodB_facts0 V1) r)) :
    Gen.prodB_cond V1 ∧ ∀ r, (kOf pB8 r).Has (lookupD (Gen.prodB_facts8 V1) r) := by
  have h16 := prodB_kok V1
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
  have hG0 : factsFrom ((Gen.prodB_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts0 V1)) Gen.prodB_items0) = Gen.prodB_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.prodB_items0 := by fns_okprodB
  obtain ⟨c0, k1⟩ := kpiece_lit (L := prodBK) (L' := pB1) (G := Gen.prodB_facts1 V1)
    (items := Gen.prodB_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.prodB_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts1 V1)) Gen.prodB_items1) = Gen.prodB_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.prodB_items1 := by fns_okprodB
  obtain ⟨c1, k2⟩ := kpiece_lit (L := pB1) (L' := pB2) (G := Gen.prodB_facts2 V1)
    (items := Gen.prodB_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.prodB_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts2 V1)) Gen.prodB_items2) = Gen.prodB_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.prodB_items2 := by fns_okprodB
  obtain ⟨c2, k3⟩ := kpiece_lit (L := pB2) (L' := pB3) (G := Gen.prodB_facts3 V1)
    (items := Gen.prodB_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.prodB_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts3 V1)) Gen.prodB_items3) = Gen.prodB_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.prodB_items3 := by fns_okprodB
  obtain ⟨c3, k4⟩ := kpiece_lit (L := pB3) (L' := pB4) (G := Gen.prodB_facts4 V1)
    (items := Gen.prodB_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.prodB_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts4 V1)) Gen.prodB_items4) = Gen.prodB_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.prodB_items4 := by fns_okprodB
  obtain ⟨c4, k5⟩ := kpiece_lit (L := pB4) (L' := pB5) (G := Gen.prodB_facts5 V1)
    (items := Gen.prodB_items4) hG4 hk4 k4 hf4 hn5
  have hG5 : factsFrom ((Gen.prodB_facts6 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts5 V1)) Gen.prodB_items5) = Gen.prodB_facts6 V1 := by
    kernel_rfl
  have hf5 : kFns Gen.prodB_items5 := by fns_okprodB
  obtain ⟨c5, k6⟩ := kpiece_lit (L := pB5) (L' := pB6) (G := Gen.prodB_facts6 V1)
    (items := Gen.prodB_items5) hG5 hk5 k5 hf5 hn6
  have hG6 : factsFrom ((Gen.prodB_facts7 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts6 V1)) Gen.prodB_items6) = Gen.prodB_facts7 V1 := by
    kernel_rfl
  have hf6 : kFns Gen.prodB_items6 := by fns_okprodB
  obtain ⟨c6, k7⟩ := kpiece_lit (L := pB6) (L' := pB7) (G := Gen.prodB_facts7 V1)
    (items := Gen.prodB_items6) hG6 hk6 k6 hf6 hn7
  have hG7 : factsFrom ((Gen.prodB_facts8 V1).map Prod.fst)
      (xFinal (lookupD (Gen.prodB_facts7 V1)) Gen.prodB_items7) = Gen.prodB_facts8 V1 := by
    kernel_rfl
  have hf7 : kFns Gen.prodB_items7 := by fns_okprodB
  obtain ⟨c7, k8⟩ := kpiece_lit (L := pB7) (L' := pB8) (G := Gen.prodB_facts8 V1)
    (items := Gen.prodB_items7) hG7 hk7 k7 hf7 hn8
  exact ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, k8⟩

theorem prodB_ok (hp : Pre p L m) (v : V) : Gen.prodB_cond (vProdB p L g v) := by
  have k0 : ∀ r, (kOf prodBK r).Has (lookupD (Gen.prodB_facts0 (vProdB p L g v)) r) := by
    rw [prodB_facts0_eq]
    exact kstart (by kernel_rfl) (prodBK_has hp v)
  exact (prodB_chain _ k0).1

/-! ### The products' values -/

/-- **The products' values** at pc 5535, from the values at pc 5279. -/
theorem prodB_pairs (hp : Pre p L m) (v : V) :
    ∀ R, Holds R (Gen.prodB_facts8 (vProdB p L g v)) →
    Holds R ((7896, joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits))) ::
      (8317, .pair (bvl (bpf v 0) (bps p v 0)) (bvl (bpf v 1) (bps p v 1))) ::
      (8319, .pair (bvl (bpf v 2) (bps p v 2)) (bvl (bpf v 3) (bps p v 3))) ::
      (8321, .pair (bvl (bpf v 4) (bps p v 4)) (bvl (bpf v 5) (bps p v 5))) ::
      (8323, .pair (bvl (bpf v 6) (bps p v 6)) (bvl (bpf v 7) (bps p v 7))) ::
      (8325, .pair (bvl (bpf v 8) (bps p v 8)) (bvl (bpf v 9) (bps p v 9))) ::
      (8327, .pair (bvl (bpf v 10) (bps p v 10)) (bvl (bpf v 11) (bps p v 11))) ::
      (8329, .pair (bvl (bpf v 12) (bps p v 12)) (bvl (bpf v 13) (bps p v 13))) ::
      (8331, .pair (bvl (bpf v 14) (bps p v 14)) (bvl (bpf v 15) (bps p v 15))) ::
      (8333, .pair (bvl (bpf v 16) (bps p v 16)) (bvl (bpf v 17) (bps p v 17))) ::
      (8335, .pair (bvl (bpf v 18) (bps p v 18)) (bvl (bpf v 19) (bps p v 19))) ::
      (8337, .pair (bvl (bpf v 20) (bps p v 20)) (bvl (bpf v 21) (bps p v 21))) ::
      (8339, .pair (bvl (bpf v 22) (bps p v 22)) (bvl (bpf v 23) (bps p v 23))) ::
      (8341, .pair (bvl (bpf v 24) (bps p v 24)) (bvl (bpf v 25) (bps p v 25))) ::
      (8343, .pair (bvl (bpf v 26) (bps p v 26)) (bvl (bpf v 27) (bps p v 27))) ::
      (8345, .pair (bvl (bpf v 28) (bps p v 28)) (bvl (bpf v 29) (bps p v 29))) ::
      (8347, .pair (bvl (bpf v 30) (bps p v 30)) (bvl (bpf v 31) (bps p v 31))) ::
      (8349, .pair (bvl (bpf v 32) (bps p v 32)) (bvl (bpf v 33) (bps p v 33))) ::
      (8351, .pair (bvl (bpf v 34) (bps p v 34)) (bvl (bpf v 35) (bps p v 35))) ::
      (8353, .pair (bvl (bpf v 36) (bps p v 36)) (bvl (bpf v 37) (bps p v 37))) ::
      (8355, .pair (bvl (bpf v 38) (bps p v 38)) (bvl (bpf v 39) (bps p v 39))) ::
      (8357, .pair (bvl (bpf v 40) (bps p v 40)) (bvl (bpf v 41) (bps p v 41))) ::
      (8359, .pair (bvl (bpf v 42) (bps p v 42)) (bvl (bpf v 43) (bps p v 43))) ::
      (8361, .pair (bvl (bpf v 44) (bps p v 44)) (bvl (bpf v 45) (bps p v 45))) ::
      (8363, .pair (bvl (bpf v 46) (bps p v 46)) (bvl (bpf v 47) (bps p v 47))) ::
      (8365, .pair (bvl (bpf v 48) (bps p v 48)) (bvl (bpf v 49) (bps p v 49))) ::
      (8367, .pair (bvl (bpf v 50) (bps p v 50)) (bvl (bpf v 51) (bps p v 51))) ::
      (8369, .pair (bvl (bpf v 52) (bps p v 52)) (bvl (bpf v 53) (bps p v 53))) ::
      (8371, .pair (bvl (bpf v 54) (bps p v 54)) (bvl (bpf v 55) (bps p v 55))) ::
      (8373, .pair (bvl (bpf v 56) (bps p v 56)) (bvl (bpf v 57) (bps p v 57))) ::
      (8375, .pair (bvl (bpf v 58) (bps p v 58)) (bvl (bpf v 59) (bps p v 59))) ::
      (8377, .pair (bvl (bpf v 60) (bps p v 60)) (bvl (bpf v 61) (bps p v 61))) ::
      (8379, .pair (bvl (bpf v 62) (bps p v 62)) (bvl (bpf v 63) (bps p v 63))) ::
      (8381, .pair (bvl (bpf v 64) (bps p v 64)) (bvl (bpf v 65) (bps p v 65))) ::
      (8383, .pair (bvl (bpf v 66) (bps p v 66)) (bvl (bpf v 67) (bps p v 67))) ::
      (8385, .pair (bvl (bpf v 68) (bps p v 68)) (bvl (bpf v 69) (bps p v 69))) ::
      (8387, .pair (bvl (bpf v 70) (bps p v 70)) (bvl (bpf v 71) (bps p v 71))) ::
      (8389, .pair (bvl (bpf v 72) (bps p v 72)) (bvl (bpf v 73) (bps p v 73))) ::
      (8391, .pair (bvl (bpf v 74) (bps p v 74)) (bvl (bpf v 75) (bps p v 75))) ::
      (8393, .pair (bvl (bpf v 76) (bps p v 76)) (bvl (bpf v 77) (bps p v 77))) ::
      (8395, .pair (bvl (bpf v 78) (bps p v 78)) (bvl (bpf v 79) (bps p v 79))) ::
      (8397, .pair (bvl (bpf v 80) (bps p v 80)) (bvl (bpf v 81) (bps p v 81))) ::
      (8399, .pair (bvl (bpf v 82) (bps p v 82)) (bvl (bpf v 83) (bps p v 83))) ::
      (8401, .pair (bvl (bpf v 84) (bps p v 84)) (bvl (bpf v 85) (bps p v 85))) ::
      (8403, .pair (bvl (bpf v 86) (bps p v 86)) (bvl (bpf v 87) (bps p v 87))) ::
      (8405, .pair (bvl (bpf v 88) (bps p v 88)) (bvl (bpf v 89) (bps p v 89))) ::
      (8407, .pair (bvl (bpf v 90) (bps p v 90)) (bvl (bpf v 91) (bps p v 91))) ::
      (8409, .pair (bvl (bpf v 92) (bps p v 92)) (bvl (bpf v 93) (bps p v 93))) ::
      (8411, .pair (bvl (bpf v 94) (bps p v 94)) (bvl (bpf v 95) (bps p v 95))) ::
      (8413, .pair (bvl (bpf v 96) (bps p v 96)) (bvl (bpf v 97) (bps p v 97))) ::
      (8415, .pair (bvl (bpf v 98) (bps p v 98)) (bvl (bpf v 99) (bps p v 99))) ::
      (8417, .pair (bvl (bpf v 100) (bps p v 100)) (bvl (bpf v 101) (bps p v 101))) ::
      (8419, .pair (bvl (bpf v 102) (bps p v 102)) (bvl (bpf v 103) (bps p v 103))) ::
      (8421, .pair (bvl (bpf v 104) (bps p v 104)) (bvl (bpf v 105) (bps p v 105))) ::
      (8423, .pair (bvl (bpf v 106) (bps p v 106)) (bvl (bpf v 107) (bps p v 107))) ::
      (8425, .pair (bvl (bpf v 108) (bps p v 108)) (bvl (bpf v 109) (bps p v 109))) ::
      (8427, .pair (bvl (bpf v 110) (bps p v 110)) (bvl (bpf v 111) (bps p v 111))) ::
      (8429, .pair (bvl (bpf v 112) (bps p v 112)) (bvl (bpf v 113) (bps p v 113))) ::
      (8431, .pair (bvl (bpf v 114) (bps p v 114)) (bvl (bpf v 115) (bps p v 115))) ::
      (8433, .pair (bvl (bpf v 116) (bps p v 116)) (bvl (bpf v 117) (bps p v 117))) ::
      (8435, .pair (bvl (bpf v 118) (bps p v 118)) (bvl (bpf v 119) (bps p v 119))) ::
      (8437, .pair (bvl (bpf v 120) (bps p v 120)) (bvl (bpf v 121) (bps p v 121))) ::
      (8439, .pair (bvl (bpf v 122) (bps p v 122)) (bvl (bpf v 123) (bps p v 123))) ::
      (8441, .pair (bvl (bpf v 124) (bps p v 124)) (bvl (bpf v 125) (bps p v 125))) ::
      (8443, .pair (bvl (bpf v 126) (bps p v 126)) (bvl (bpf v 127) (bps p v 127))) ::
      []) := by
  intro R hR
  have ht := (s14_word hp).2
  have hS := SK.clean (s14_pw hp)
  have hSr := s14_read hp
  have hS7896 : vProdB p L g v 7896 = joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits)) := barrB_scale v
  have hh : ∀ n < 128, vProdB p L g v (halfReg 914 n) = hv16 (bpf v n) (bbr v n) :=
    fun n hn => barrB_half v hn
  have hx : ∀ j < 64, vProdB p L g v (7367 + j) =
      .pair (.float .f32 (v.score (2 * j))) (.float .f32 (v.score (2 * j + 1))) :=
    fun j hj => barrB_pair v hj
  simp only [Gen.prodB_facts8, holds_cons, holds_nil] at hR ⊢
  obtain ⟨h7896, hR⟩ := hR
  refine ⟨by rw [h7896, hS7896], ?_⟩
  obtain ⟨h8317, hR⟩ := hR
  refine ⟨by
    rw [h8317, Gen.prodB_v5282, Gen.prodB_v5281, Gen.prodB_v5279, Gen.prodB_v5280, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 0 (by decide))
      (hh 1 (by decide)) (hx 0 (by decide))), ?_⟩
  obtain ⟨h8319, hR⟩ := hR
  refine ⟨by
    rw [h8319, Gen.prodB_v5286, Gen.prodB_v5285, Gen.prodB_v5283, Gen.prodB_v5284, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 2 (by decide))
      (hh 3 (by decide)) (hx 1 (by decide))), ?_⟩
  obtain ⟨h8321, hR⟩ := hR
  refine ⟨by
    rw [h8321, Gen.prodB_v5290, Gen.prodB_v5289, Gen.prodB_v5287, Gen.prodB_v5288, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 4 (by decide))
      (hh 5 (by decide)) (hx 2 (by decide))), ?_⟩
  obtain ⟨h8323, hR⟩ := hR
  refine ⟨by
    rw [h8323, Gen.prodB_v5294, Gen.prodB_v5293, Gen.prodB_v5291, Gen.prodB_v5292, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 6 (by decide))
      (hh 7 (by decide)) (hx 3 (by decide))), ?_⟩
  obtain ⟨h8325, hR⟩ := hR
  refine ⟨by
    rw [h8325, Gen.prodB_v5298, Gen.prodB_v5297, Gen.prodB_v5295, Gen.prodB_v5296, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 8 (by decide))
      (hh 9 (by decide)) (hx 4 (by decide))), ?_⟩
  obtain ⟨h8327, hR⟩ := hR
  refine ⟨by
    rw [h8327, Gen.prodB_v5302, Gen.prodB_v5301, Gen.prodB_v5299, Gen.prodB_v5300, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 10 (by decide))
      (hh 11 (by decide)) (hx 5 (by decide))), ?_⟩
  obtain ⟨h8329, hR⟩ := hR
  refine ⟨by
    rw [h8329, Gen.prodB_v5306, Gen.prodB_v5305, Gen.prodB_v5303, Gen.prodB_v5304, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 12 (by decide))
      (hh 13 (by decide)) (hx 6 (by decide))), ?_⟩
  obtain ⟨h8331, hR⟩ := hR
  refine ⟨by
    rw [h8331, Gen.prodB_v5310, Gen.prodB_v5309, Gen.prodB_v5307, Gen.prodB_v5308, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 14 (by decide))
      (hh 15 (by decide)) (hx 7 (by decide))), ?_⟩
  obtain ⟨h8333, hR⟩ := hR
  refine ⟨by
    rw [h8333, Gen.prodB_v5314, Gen.prodB_v5313, Gen.prodB_v5311, Gen.prodB_v5312, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 16 (by decide))
      (hh 17 (by decide)) (hx 8 (by decide))), ?_⟩
  obtain ⟨h8335, hR⟩ := hR
  refine ⟨by
    rw [h8335, Gen.prodB_v5318, Gen.prodB_v5317, Gen.prodB_v5315, Gen.prodB_v5316, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 18 (by decide))
      (hh 19 (by decide)) (hx 9 (by decide))), ?_⟩
  obtain ⟨h8337, hR⟩ := hR
  refine ⟨by
    rw [h8337, Gen.prodB_v5322, Gen.prodB_v5321, Gen.prodB_v5319, Gen.prodB_v5320, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 20 (by decide))
      (hh 21 (by decide)) (hx 10 (by decide))), ?_⟩
  obtain ⟨h8339, hR⟩ := hR
  refine ⟨by
    rw [h8339, Gen.prodB_v5326, Gen.prodB_v5325, Gen.prodB_v5323, Gen.prodB_v5324, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 22 (by decide))
      (hh 23 (by decide)) (hx 11 (by decide))), ?_⟩
  obtain ⟨h8341, hR⟩ := hR
  refine ⟨by
    rw [h8341, Gen.prodB_v5330, Gen.prodB_v5329, Gen.prodB_v5327, Gen.prodB_v5328, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 24 (by decide))
      (hh 25 (by decide)) (hx 12 (by decide))), ?_⟩
  obtain ⟨h8343, hR⟩ := hR
  refine ⟨by
    rw [h8343, Gen.prodB_v5334, Gen.prodB_v5333, Gen.prodB_v5331, Gen.prodB_v5332, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 26 (by decide))
      (hh 27 (by decide)) (hx 13 (by decide))), ?_⟩
  obtain ⟨h8345, hR⟩ := hR
  refine ⟨by
    rw [h8345, Gen.prodB_v5338, Gen.prodB_v5337, Gen.prodB_v5335, Gen.prodB_v5336, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 28 (by decide))
      (hh 29 (by decide)) (hx 14 (by decide))), ?_⟩
  obtain ⟨h8347, hR⟩ := hR
  refine ⟨by
    rw [h8347, Gen.prodB_v5342, Gen.prodB_v5341, Gen.prodB_v5339, Gen.prodB_v5340, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 30 (by decide))
      (hh 31 (by decide)) (hx 15 (by decide))), ?_⟩
  obtain ⟨h8349, hR⟩ := hR
  refine ⟨by
    rw [h8349, Gen.prodB_v5346, Gen.prodB_v5345, Gen.prodB_v5343, Gen.prodB_v5344, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 32 (by decide))
      (hh 33 (by decide)) (hx 16 (by decide))), ?_⟩
  obtain ⟨h8351, hR⟩ := hR
  refine ⟨by
    rw [h8351, Gen.prodB_v5350, Gen.prodB_v5349, Gen.prodB_v5347, Gen.prodB_v5348, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 34 (by decide))
      (hh 35 (by decide)) (hx 17 (by decide))), ?_⟩
  obtain ⟨h8353, hR⟩ := hR
  refine ⟨by
    rw [h8353, Gen.prodB_v5354, Gen.prodB_v5353, Gen.prodB_v5351, Gen.prodB_v5352, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 36 (by decide))
      (hh 37 (by decide)) (hx 18 (by decide))), ?_⟩
  obtain ⟨h8355, hR⟩ := hR
  refine ⟨by
    rw [h8355, Gen.prodB_v5358, Gen.prodB_v5357, Gen.prodB_v5355, Gen.prodB_v5356, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 38 (by decide))
      (hh 39 (by decide)) (hx 19 (by decide))), ?_⟩
  obtain ⟨h8357, hR⟩ := hR
  refine ⟨by
    rw [h8357, Gen.prodB_v5362, Gen.prodB_v5361, Gen.prodB_v5359, Gen.prodB_v5360, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 40 (by decide))
      (hh 41 (by decide)) (hx 20 (by decide))), ?_⟩
  obtain ⟨h8359, hR⟩ := hR
  refine ⟨by
    rw [h8359, Gen.prodB_v5366, Gen.prodB_v5365, Gen.prodB_v5363, Gen.prodB_v5364, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 42 (by decide))
      (hh 43 (by decide)) (hx 21 (by decide))), ?_⟩
  obtain ⟨h8361, hR⟩ := hR
  refine ⟨by
    rw [h8361, Gen.prodB_v5370, Gen.prodB_v5369, Gen.prodB_v5367, Gen.prodB_v5368, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 44 (by decide))
      (hh 45 (by decide)) (hx 22 (by decide))), ?_⟩
  obtain ⟨h8363, hR⟩ := hR
  refine ⟨by
    rw [h8363, Gen.prodB_v5374, Gen.prodB_v5373, Gen.prodB_v5371, Gen.prodB_v5372, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 46 (by decide))
      (hh 47 (by decide)) (hx 23 (by decide))), ?_⟩
  obtain ⟨h8365, hR⟩ := hR
  refine ⟨by
    rw [h8365, Gen.prodB_v5378, Gen.prodB_v5377, Gen.prodB_v5375, Gen.prodB_v5376, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 48 (by decide))
      (hh 49 (by decide)) (hx 24 (by decide))), ?_⟩
  obtain ⟨h8367, hR⟩ := hR
  refine ⟨by
    rw [h8367, Gen.prodB_v5382, Gen.prodB_v5381, Gen.prodB_v5379, Gen.prodB_v5380, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 50 (by decide))
      (hh 51 (by decide)) (hx 25 (by decide))), ?_⟩
  obtain ⟨h8369, hR⟩ := hR
  refine ⟨by
    rw [h8369, Gen.prodB_v5386, Gen.prodB_v5385, Gen.prodB_v5383, Gen.prodB_v5384, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 52 (by decide))
      (hh 53 (by decide)) (hx 26 (by decide))), ?_⟩
  obtain ⟨h8371, hR⟩ := hR
  refine ⟨by
    rw [h8371, Gen.prodB_v5390, Gen.prodB_v5389, Gen.prodB_v5387, Gen.prodB_v5388, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 54 (by decide))
      (hh 55 (by decide)) (hx 27 (by decide))), ?_⟩
  obtain ⟨h8373, hR⟩ := hR
  refine ⟨by
    rw [h8373, Gen.prodB_v5394, Gen.prodB_v5393, Gen.prodB_v5391, Gen.prodB_v5392, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 56 (by decide))
      (hh 57 (by decide)) (hx 28 (by decide))), ?_⟩
  obtain ⟨h8375, hR⟩ := hR
  refine ⟨by
    rw [h8375, Gen.prodB_v5398, Gen.prodB_v5397, Gen.prodB_v5395, Gen.prodB_v5396, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 58 (by decide))
      (hh 59 (by decide)) (hx 29 (by decide))), ?_⟩
  obtain ⟨h8377, hR⟩ := hR
  refine ⟨by
    rw [h8377, Gen.prodB_v5402, Gen.prodB_v5401, Gen.prodB_v5399, Gen.prodB_v5400, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 60 (by decide))
      (hh 61 (by decide)) (hx 30 (by decide))), ?_⟩
  obtain ⟨h8379, hR⟩ := hR
  refine ⟨by
    rw [h8379, Gen.prodB_v5406, Gen.prodB_v5405, Gen.prodB_v5403, Gen.prodB_v5404, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 62 (by decide))
      (hh 63 (by decide)) (hx 31 (by decide))), ?_⟩
  obtain ⟨h8381, hR⟩ := hR
  refine ⟨by
    rw [h8381, Gen.prodB_v5410, Gen.prodB_v5409, Gen.prodB_v5407, Gen.prodB_v5408, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 64 (by decide))
      (hh 65 (by decide)) (hx 32 (by decide))), ?_⟩
  obtain ⟨h8383, hR⟩ := hR
  refine ⟨by
    rw [h8383, Gen.prodB_v5414, Gen.prodB_v5413, Gen.prodB_v5411, Gen.prodB_v5412, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 66 (by decide))
      (hh 67 (by decide)) (hx 33 (by decide))), ?_⟩
  obtain ⟨h8385, hR⟩ := hR
  refine ⟨by
    rw [h8385, Gen.prodB_v5418, Gen.prodB_v5417, Gen.prodB_v5415, Gen.prodB_v5416, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 68 (by decide))
      (hh 69 (by decide)) (hx 34 (by decide))), ?_⟩
  obtain ⟨h8387, hR⟩ := hR
  refine ⟨by
    rw [h8387, Gen.prodB_v5422, Gen.prodB_v5421, Gen.prodB_v5419, Gen.prodB_v5420, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 70 (by decide))
      (hh 71 (by decide)) (hx 35 (by decide))), ?_⟩
  obtain ⟨h8389, hR⟩ := hR
  refine ⟨by
    rw [h8389, Gen.prodB_v5426, Gen.prodB_v5425, Gen.prodB_v5423, Gen.prodB_v5424, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 72 (by decide))
      (hh 73 (by decide)) (hx 36 (by decide))), ?_⟩
  obtain ⟨h8391, hR⟩ := hR
  refine ⟨by
    rw [h8391, Gen.prodB_v5430, Gen.prodB_v5429, Gen.prodB_v5427, Gen.prodB_v5428, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 74 (by decide))
      (hh 75 (by decide)) (hx 37 (by decide))), ?_⟩
  obtain ⟨h8393, hR⟩ := hR
  refine ⟨by
    rw [h8393, Gen.prodB_v5434, Gen.prodB_v5433, Gen.prodB_v5431, Gen.prodB_v5432, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 76 (by decide))
      (hh 77 (by decide)) (hx 38 (by decide))), ?_⟩
  obtain ⟨h8395, hR⟩ := hR
  refine ⟨by
    rw [h8395, Gen.prodB_v5438, Gen.prodB_v5437, Gen.prodB_v5435, Gen.prodB_v5436, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 78 (by decide))
      (hh 79 (by decide)) (hx 39 (by decide))), ?_⟩
  obtain ⟨h8397, hR⟩ := hR
  refine ⟨by
    rw [h8397, Gen.prodB_v5442, Gen.prodB_v5441, Gen.prodB_v5439, Gen.prodB_v5440, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 80 (by decide))
      (hh 81 (by decide)) (hx 40 (by decide))), ?_⟩
  obtain ⟨h8399, hR⟩ := hR
  refine ⟨by
    rw [h8399, Gen.prodB_v5446, Gen.prodB_v5445, Gen.prodB_v5443, Gen.prodB_v5444, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 82 (by decide))
      (hh 83 (by decide)) (hx 41 (by decide))), ?_⟩
  obtain ⟨h8401, hR⟩ := hR
  refine ⟨by
    rw [h8401, Gen.prodB_v5450, Gen.prodB_v5449, Gen.prodB_v5447, Gen.prodB_v5448, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 84 (by decide))
      (hh 85 (by decide)) (hx 42 (by decide))), ?_⟩
  obtain ⟨h8403, hR⟩ := hR
  refine ⟨by
    rw [h8403, Gen.prodB_v5454, Gen.prodB_v5453, Gen.prodB_v5451, Gen.prodB_v5452, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 86 (by decide))
      (hh 87 (by decide)) (hx 43 (by decide))), ?_⟩
  obtain ⟨h8405, hR⟩ := hR
  refine ⟨by
    rw [h8405, Gen.prodB_v5458, Gen.prodB_v5457, Gen.prodB_v5455, Gen.prodB_v5456, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 88 (by decide))
      (hh 89 (by decide)) (hx 44 (by decide))), ?_⟩
  obtain ⟨h8407, hR⟩ := hR
  refine ⟨by
    rw [h8407, Gen.prodB_v5462, Gen.prodB_v5461, Gen.prodB_v5459, Gen.prodB_v5460, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 90 (by decide))
      (hh 91 (by decide)) (hx 45 (by decide))), ?_⟩
  obtain ⟨h8409, hR⟩ := hR
  refine ⟨by
    rw [h8409, Gen.prodB_v5466, Gen.prodB_v5465, Gen.prodB_v5463, Gen.prodB_v5464, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 92 (by decide))
      (hh 93 (by decide)) (hx 46 (by decide))), ?_⟩
  obtain ⟨h8411, hR⟩ := hR
  refine ⟨by
    rw [h8411, Gen.prodB_v5470, Gen.prodB_v5469, Gen.prodB_v5467, Gen.prodB_v5468, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 94 (by decide))
      (hh 95 (by decide)) (hx 47 (by decide))), ?_⟩
  obtain ⟨h8413, hR⟩ := hR
  refine ⟨by
    rw [h8413, Gen.prodB_v5474, Gen.prodB_v5473, Gen.prodB_v5471, Gen.prodB_v5472, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 96 (by decide))
      (hh 97 (by decide)) (hx 48 (by decide))), ?_⟩
  obtain ⟨h8415, hR⟩ := hR
  refine ⟨by
    rw [h8415, Gen.prodB_v5478, Gen.prodB_v5477, Gen.prodB_v5475, Gen.prodB_v5476, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 98 (by decide))
      (hh 99 (by decide)) (hx 49 (by decide))), ?_⟩
  obtain ⟨h8417, hR⟩ := hR
  refine ⟨by
    rw [h8417, Gen.prodB_v5482, Gen.prodB_v5481, Gen.prodB_v5479, Gen.prodB_v5480, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 100 (by decide))
      (hh 101 (by decide)) (hx 50 (by decide))), ?_⟩
  obtain ⟨h8419, hR⟩ := hR
  refine ⟨by
    rw [h8419, Gen.prodB_v5486, Gen.prodB_v5485, Gen.prodB_v5483, Gen.prodB_v5484, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 102 (by decide))
      (hh 103 (by decide)) (hx 51 (by decide))), ?_⟩
  obtain ⟨h8421, hR⟩ := hR
  refine ⟨by
    rw [h8421, Gen.prodB_v5490, Gen.prodB_v5489, Gen.prodB_v5487, Gen.prodB_v5488, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 104 (by decide))
      (hh 105 (by decide)) (hx 52 (by decide))), ?_⟩
  obtain ⟨h8423, hR⟩ := hR
  refine ⟨by
    rw [h8423, Gen.prodB_v5494, Gen.prodB_v5493, Gen.prodB_v5491, Gen.prodB_v5492, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 106 (by decide))
      (hh 107 (by decide)) (hx 53 (by decide))), ?_⟩
  obtain ⟨h8425, hR⟩ := hR
  refine ⟨by
    rw [h8425, Gen.prodB_v5498, Gen.prodB_v5497, Gen.prodB_v5495, Gen.prodB_v5496, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 108 (by decide))
      (hh 109 (by decide)) (hx 54 (by decide))), ?_⟩
  obtain ⟨h8427, hR⟩ := hR
  refine ⟨by
    rw [h8427, Gen.prodB_v5502, Gen.prodB_v5501, Gen.prodB_v5499, Gen.prodB_v5500, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 110 (by decide))
      (hh 111 (by decide)) (hx 55 (by decide))), ?_⟩
  obtain ⟨h8429, hR⟩ := hR
  refine ⟨by
    rw [h8429, Gen.prodB_v5506, Gen.prodB_v5505, Gen.prodB_v5503, Gen.prodB_v5504, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 112 (by decide))
      (hh 113 (by decide)) (hx 56 (by decide))), ?_⟩
  obtain ⟨h8431, hR⟩ := hR
  refine ⟨by
    rw [h8431, Gen.prodB_v5510, Gen.prodB_v5509, Gen.prodB_v5507, Gen.prodB_v5508, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 114 (by decide))
      (hh 115 (by decide)) (hx 57 (by decide))), ?_⟩
  obtain ⟨h8433, hR⟩ := hR
  refine ⟨by
    rw [h8433, Gen.prodB_v5514, Gen.prodB_v5513, Gen.prodB_v5511, Gen.prodB_v5512, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 116 (by decide))
      (hh 117 (by decide)) (hx 58 (by decide))), ?_⟩
  obtain ⟨h8435, hR⟩ := hR
  refine ⟨by
    rw [h8435, Gen.prodB_v5518, Gen.prodB_v5517, Gen.prodB_v5515, Gen.prodB_v5516, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 118 (by decide))
      (hh 119 (by decide)) (hx 59 (by decide))), ?_⟩
  obtain ⟨h8437, hR⟩ := hR
  refine ⟨by
    rw [h8437, Gen.prodB_v5522, Gen.prodB_v5521, Gen.prodB_v5519, Gen.prodB_v5520, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 120 (by decide))
      (hh 121 (by decide)) (hx 60 (by decide))), ?_⟩
  obtain ⟨h8439, hR⟩ := hR
  refine ⟨by
    rw [h8439, Gen.prodB_v5526, Gen.prodB_v5525, Gen.prodB_v5523, Gen.prodB_v5524, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 122 (by decide))
      (hh 123 (by decide)) (hx 61 (by decide))), ?_⟩
  obtain ⟨h8441, hR⟩ := hR
  refine ⟨by
    rw [h8441, Gen.prodB_v5530, Gen.prodB_v5529, Gen.prodB_v5527, Gen.prodB_v5528, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 124 (by decide))
      (hh 125 (by decide)) (hx 62 (by decide))), ?_⟩
  obtain ⟨h8443, hR⟩ := hR
  refine ⟨by
    rw [h8443, Gen.prodB_v5534, Gen.prodB_v5533, Gen.prodB_v5531, Gen.prodB_v5532, hS7896]
    exact congrArg some (prod_lane _ v ht hS hSr (hh 126 (by decide))
      (hh 127 (by decide)) (hx 63 (by decide))), ?_⟩
  trivial

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
