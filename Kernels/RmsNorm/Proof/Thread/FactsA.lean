-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.FactsStep

@[expose] public section

/-! # The run invariant along the steps of the warp-index shuffle, the input loads and the
staging stores -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {g : Nat}

set_option maxHeartbeats 4000000 in
theorem rf_shfl0 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .shfl0)
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
  have hi00 := hi0 hs
  split_ifs at hn with hc
  · obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, hi00]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, hi00]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, hi00]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, hi00]
    case acc =>
      intro _; simp [hacc0, hsub0]
    case xa =>
      rf_cond [hs]
    case xb =>
      rf_cond [hs]
    case ra =>
      rf_cond [hs]
    case u =>
      rf_cond [hs]
    case rb =>
      rf_cond [hs]
    case tt =>
      rf_cond [hs]
    case rawa =>
      rf_cond [hs]
    case rawb =>
      rf_cond [hs]
    case rs0a =>
      rf_cond [hs]
    case rs0b =>
      rf_cond [hs]
    case rs1a =>
      rf_cond [hs]
    case rs1b =>
      rf_cond [hs]
    case i0 => intro h; cases h
  · obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs, hi00]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs, hi00]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs, hi00]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs, hi00]
    case acc =>
      intro h; simp [Site.vload] at h
    case xa =>
      rf_cond [hs]
    case xb =>
      rf_cond [hs]
    case ra =>
      rf_cond [hs]
    case u =>
      rf_cond [hs]
    case rb =>
      rf_cond [hs]
    case tt =>
      rf_cond [hs]
    case rawa =>
      rf_cond [hs]
    case rawb =>
      rf_cond [hs]
    case rs0a =>
      rf_cond [hs]
    case rs0b =>
      rf_cond [hs]
    case rs1a =>
      rf_cond [hs]
    case rs1b =>
      rf_cond [hs]
    case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_ldxa {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldxa)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  simp only [siteTmpl, hs] at hev
  obtain ⟨bs, -, rfl, -⟩ := hev
  simp only [next, hs] at hn
  obtain ⟨v, hb, ⟨hm, rfl⟩ | ⟨hm, hk⟩⟩ := loadNext_rd hn
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      intro _
      exact acc_mid (hD.acc (by simp [hs, Site.vload]))
        (by have := hl (by simp [hs, Site.inRow]); simp only [D.pos, D.vbase,
              hs] at this ⊢; omega) hsub4
        (rdv_rd hb)
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
    case i0 => intro h; simp only [hs, reduceCtorEq] at h
  have h3 : d.sub = 3 := by omega
  have h0 := hD.acc (by simp [hs, Site.vload])
  simp only [D.vbase, hs, Nat.add_zero] at h0
  have hlen' : pre.length = rowBase g d.i + 0 + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
  split_ifs at hk with hok
  obtain rfl := (Option.some.inj hk).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
  case acc =>
    intro _; simp
  case xa =>
    intro _ _; exact (acc_last h0 (by simpa using hlen') h3 (rdv_rd hb))
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

set_option maxHeartbeats 4000000 in
theorem rf_stxa0 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stxa0)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rcases storeNext_some hn with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  ·
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
    case i0 => intro h; simp only [hs, reduceCtorEq] at h
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      intro _; simp [hacc0]
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
theorem rf_stxa1 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stxa1)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rcases storeNext_some hn with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  ·
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
    case i0 => intro h; simp only [hs, reduceCtorEq] at h
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      intro _; simp [hacc0]
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
theorem rf_ldxb {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldxb)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  simp only [siteTmpl, hs] at hev
  obtain ⟨bs, -, rfl, -⟩ := hev
  simp only [next, hs] at hn
  obtain ⟨v, hb, ⟨hm, rfl⟩ | ⟨hm, hk⟩⟩ := loadNext_rd hn
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      intro _
      exact acc_mid (hD.acc (by simp [hs, Site.vload]))
        (by have := hl (by simp [hs, Site.inRow]); simp only [D.pos, D.vbase,
              hs] at this ⊢; omega) hsub4
        (rdv_rd hb)
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
    case i0 => intro h; simp only [hs, reduceCtorEq] at h
  have h3 : d.sub = 3 := by omega
  have h0 := hD.acc (by simp [hs, Site.vload])
  simp only [D.vbase, hs] at h0
  have hlen' : pre.length = rowBase g d.i + 12 + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
  split_ifs at hk with hok
  obtain rfl := (Option.some.inj hk).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
    ?rs1a, ?rs1b⟩, ?i0⟩
  · inv_tac
  · rw [List.length_append, hlen]; rf_arith [hs]
  · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
  · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
  case acc =>
    intro _; simp
  case xa =>
    exact keep_xa hD hl rfl rfl (by rf_cond [hs])
  case xb =>
    intro _ _; exact (acc_last h0 hlen' h3 (rdv_rd hb))
  case ra =>
    exact keep_ra hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case u =>
    exact keep_u hD hl rfl rfl (by rf_cond [hs])
  case rb =>
    exact keep_rb hD hl rfl (fun _ _ => rfl) (by rf_cond [hs])
  case tt =>
    exact keep_tt hD hl rfl rfl (by rf_cond [hs])
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

set_option maxHeartbeats 4000000 in
theorem rf_stxb0 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stxb0)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rcases storeNext_some hn with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  ·
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
    case i0 => intro h; simp only [hs, reduceCtorEq] at h
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      intro _; simp [hacc0]
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
theorem rf_stxb1 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stxb1)
    (hev : Fires d.site.pc (siteTmpl P g d t) e o) (hn : next P g d e = some (some d')) :
    RunFacts P g d' (pre ++ [e]) := by
  obtain ⟨hi, hlen, hb0, hb1, hsc, hD, hi0⟩ := hJ
  have hl := hlen_of hlen
  have := hi.sub; have := hi.acc; have := hi.row; have := hi.raw
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  simp only [siteTmpl, hs] at hev
  obtain ⟨rfl, -⟩ := hev
  simp only [next, hs] at hn
  have hacc0 : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rcases storeNext_some hn with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  ·
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
    case i0 => intro h; simp only [hs, reduceCtorEq] at h
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?acc, ?xa, ?xb, ?ra, ?u, ?rb, ?tt, ?rawa, ?rawb, ?rs0a, ?rs0b,
      ?rs1a, ?rs1b⟩, ?i0⟩
    · inv_tac
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      intro _; simp [hacc0]
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

end
end PTX.Kernels.RmsNorm.Proof
