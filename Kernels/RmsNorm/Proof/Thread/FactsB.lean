-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.FactsStep

@[expose] public section

/-! # The run invariant along the steps of the butterflies, the barriers and the
scalar shared accesses -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {g : Nat}

set_option maxHeartbeats 4000000 in
theorem rf_bfa {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = Site.bfa k)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨recv, ok, rfl, -⟩ := hev
  simp only [next, hs] at hn
  have hk5 := hi.bfa k hs
  by_cases hadd : (floatE (addI true) [bsumV (ssqV d) d.ra k, recv]).toBool = true
  swap
  · simp [hadd] at hn
  simp only [hadd, ↓reduceIte] at hn
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  unfold bfaNext
  by_cases hk1 : k + 1 < 5
  · simp only [hk1, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      intro h1 k' hk' h2
      by_cases hkk : k' = k
      · show Function.update d.ra k recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.ra k recv k' = _
        have h2' : 24 + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.ra (by simp [hs, Site.inRow]) k' hk' h2'
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  have hk4 : k = 4 := by omega
  subst hk4
  by_cases hz : g % 256 % 32 = 0
  · simp only [hz, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, hz]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, hz]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      intro h1 k' hk' h2
      by_cases hkk : k' = 4
      · show Function.update d.ra 4 recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.ra 4 recv k' = _
        have h2' : 24 + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.ra (by simp [hs, Site.inRow]) k' hk' h2'
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  · simp only [hz, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, hz]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, hz]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      intro h1 k' hk' h2
      by_cases hkk : k' = 4
      · show Function.update d.ra 4 recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.ra 4 recv k' = _
        have h2' : 24 + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.ra (by simp [hs, Site.inRow]) k' hk' h2'
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_stws {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stws)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  have := hi.stws hs
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
  case acc =>
    rf_cond [hs]
  case xa =>
    exact keep_xa hD hl rfl rfl (by rf_cond [hs])
  case xb =>
    exact keep_xb hD hl rfl rfl (by rf_cond [hs])
  case ra =>
    exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case u =>
    exact keep_u hD hl rfl rfl (by rf_cond [hs])
  case rb =>
    exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case tt =>
    exact keep_tt hD hl rfl rfl (by rf_cond [hs])
  case rawa =>
    exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
  case rawb =>
    exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
  case rs0a =>
    exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
  case rs0b =>
    exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_bar0 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .bar0)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  split_ifs at hn with h31 h8
  · obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, h31]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, h31]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, h31]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, h31]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  · obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, h31, h8]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, h31, h8]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, h31, h8]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, h31, h8]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  · obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, h31, h8]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, h31, h8]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, h31, h8]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, h31, h8]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      intro _ _ _; show b32 0 = _; simp only [h8, ↓reduceIte]
    case rb =>
      exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_ldws {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldws)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨bs, -, rfl, -⟩ := hev
  simp only [next, hs] at hn
  have h8 := hi.ldws hs
  cases hb : rebuild 3 bs with
  | error f => simp only [hb] at hn; cases hn
  | ok v =>
  simp only [hb] at hn
  split_ifs at hn with h4
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs, h8]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, h8]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, h8]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, h8]
  case acc =>
    rf_cond [hs]
  case xa =>
    exact keep_xa hD hl rfl rfl (by rf_cond [hs])
  case xb =>
    exact keep_xb hD hl rfl rfl (by rf_cond [hs])
  case ra =>
    exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case u =>
    intro _ _ _
    show v = _
    simp only [h8, ↓reduceIte]
    rw [get_last (by have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
    exact (rdv_rd hb).symm
  case rb =>
    exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case tt =>
    exact keep_tt hD hl rfl rfl (by rf_cond [hs])
  case rawa =>
    exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
  case rawb =>
    exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
  case rs0a =>
    exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
  case rs0b =>
    exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_bfb {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = Site.bfb k)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨recv, ok, rfl, -⟩ := hev
  simp only [next, hs] at hn
  have hk5 := (hi.bfb k hs).1
  have hw := (hi.bfb k hs).2
  by_cases hk0 : k = 0
  · subst hk0
    by_cases hadd : (floatE (addI true) [bsumV d.u d.rb 0, recv]).toBool = true
    swap
    · simp [hadd] at hn
    simp only [hadd, ↓reduceIte] at hn
    obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
    simp only [bfbNext, Nat.reduceAdd, Nat.one_lt_ofNat, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      intro h1 hw k' hk' h2
      by_cases hkk : k' = 0
      · show Function.update d.rb 0 recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.rb 0 recv k' = _
        have h2' : 30 + l0 g + l8 g + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.rb (by simp [hs, Site.inRow]) hw k' hk' h2'
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  by_cases hadd : (floatE (addI true) [bsumV d.u d.rb k, recv]).toBool = true
  swap
  · simp [hadd] at hn
  simp only [hadd, ↓reduceIte] at hn
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  unfold bfbNext
  by_cases hk1 : k + 1 < 5
  · simp only [hk1, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      intro h1 hw k' hk' h2
      by_cases hkk : k' = k
      · show Function.update d.rb k recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.rb k recv k' = _
        have h2' : 30 + l0 g + l8 g + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.rb (by simp [hs, Site.inRow]) hw k' hk' h2'
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  have hk4 : k = 4 := by omega
  subst hk4
  by_cases hz : g % 256 = 0
  · simp only [hz, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, hz]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, hz]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      intro h1 hw k' hk' h2
      by_cases hkk : k' = 4
      · show Function.update d.rb 4 recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.rb 4 recv k' = _
        have h2' : 30 + l0 g + l8 g + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.rb (by simp [hs, Site.inRow]) hw k' hk' h2'
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h
  · simp only [hz, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, hz]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, hz]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, hz]
    case acc =>
      rf_cond [hs]
    case xa =>
      exact keep_xa hD hl rfl rfl (by rf_cond [hs])
    case xb =>
      exact keep_xb hD hl rfl rfl (by rf_cond [hs])
    case ra =>
      exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
    case u =>
      exact keep_u hD hl rfl rfl (by rf_cond [hs])
    case rb =>
      intro h1 hw k' hk' h2
      by_cases hkk : k' = 4
      · show Function.update d.rb 4 recv k' = _
        rw [hkk, Function.update_self, get_last (by
          have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega)]
        rfl
      · show Function.update d.rb 4 recv k' = _
        have h2' : 30 + l0 g + l8 g + k' < D.pos g d := by
          simp only [D.pos, hs] at h2 ⊢; rf_omega
        rw [Function.update_of_ne hkk, get_snoc (by
          have := hl (by simp [hs, Site.inRow]); dsimp only; omega)]
        exact hD.rb (by simp [hs, Site.inRow]) hw k' hk' h2'
    case tt =>
      exact keep_tt hD hl rfl rfl (by rf_cond [hs])
    case rawa =>
      exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
    case rawb =>
      exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
    case rs0a =>
      exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
    case rs0b =>
      exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
    case rs1a =>
      exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
    case rs1b =>
      exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
    case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_stts {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stts)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  have := hi.stts hs
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
  case acc =>
    rf_cond [hs]
  case xa =>
    exact keep_xa hD hl rfl rfl (by rf_cond [hs])
  case xb =>
    exact keep_xb hD hl rfl rfl (by rf_cond [hs])
  case ra =>
    exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case u =>
    exact keep_u hD hl rfl rfl (by rf_cond [hs])
  case rb =>
    exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case tt =>
    exact keep_tt hD hl rfl rfl (by rf_cond [hs])
  case rawa =>
    exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
  case rawb =>
    exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
  case rs0a =>
    exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
  case rs0b =>
    exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_bar1 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .bar1)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
  case acc =>
    rf_cond [hs]
  case xa =>
    exact keep_xa hD hl rfl rfl (by rf_cond [hs])
  case xb =>
    exact keep_xb hD hl rfl rfl (by rf_cond [hs])
  case ra =>
    exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case u =>
    exact keep_u hD hl rfl rfl (by rf_cond [hs])
  case rb =>
    exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case tt =>
    exact keep_tt hD hl rfl rfl (by rf_cond [hs])
  case rawa =>
    exact keep_rawa hD hl rfl rfl (by rf_cond [hs])
  case rawb =>
    exact keep_rawb hD hl rfl rfl (by rf_cond [hs])
  case rs0a =>
    exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
  case rs0b =>
    exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_ldts {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldts)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub0 : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  simp only [siteTmpl, hs] at hev
  obtain ⟨bs, -, rfl, -⟩ := hev
  simp only [next, hs] at hn
  cases hb : rebuild 3 bs with
  | error f => simp only [hb] at hn; cases hn
  | ok v =>
  simp only [hb] at hn
  split_ifs at hn with hpos
  obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
  case acc =>
    intro _; simp [hacc0, hsub0]
  case xa =>
    exact keep_xa hD hl rfl rfl (by rf_cond [hs])
  case xb =>
    exact keep_xb hD hl rfl rfl (by rf_cond [hs])
  case ra =>
    exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case u =>
    exact keep_u hD hl rfl rfl (by rf_cond [hs])
  case rb =>
    exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case tt =>
    intro _ _
    show v = _
    rw [get_last (by have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this ⊢; omega),
      rdv_rd hb]
  case rawa =>
    rf_cond [hs]
  case rawb =>
    rf_cond [hs]
  case rs0a =>
    exact keep_rs0a hD hl rfl rfl (by rf_cond [hs])
  case rs0b =>
    exact keep_rs0b hD hl rfl rfl (by rf_cond [hs])
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

end
end PTX.Kernels.RmsNorm.Proof
