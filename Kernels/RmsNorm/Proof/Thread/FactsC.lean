-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.FactsStep

@[expose] public section

/-! # The run invariant along the steps of the weight loads, the reloads, the output stores
and the last barrier -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {g : Nat}

set_option maxHeartbeats 4000000 in
theorem rf_ldwa {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldwa)
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
  have hlen' : pre.length = rowBase g d.i + (p1 g + 2) + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
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
    intro _ _ _
    dsimp only
    rw [show rowBase g d.i + p1 g + 2 = rowBase g d.i + (p1 g + 2) by omega]
    exact acc_last h0 hlen' h3 (rdv_rd hb)
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
theorem rf_ldsa0 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldsa0)
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
  have hlen' : pre.length = rowBase g d.i + (p1 g + 6) + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
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
    intro _ _ _
    dsimp only
    rw [show rowBase g d.i + p1 g + 6 = rowBase g d.i + (p1 g + 6) by omega]
    exact acc_last h0 hlen' h3 (rdv_rd hb)
  case rs0b =>
    rf_cond [hs]
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_ldsa1 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldsa1)
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
  have hlen' : pre.length = rowBase g d.i + (p1 g + 10) + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
  split_ifs at hk with hok
  obtain rfl := (Option.some.inj hk).symm
  simp only [tileA]
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
    intro _ _ _
    dsimp only
    rw [show rowBase g d.i + p1 g + 10 = rowBase g d.i + (p1 g + 10) by omega]
    exact acc_last h0 hlen' h3 (rdv_rd hb)
  case rs1b =>
    rf_cond [hs]
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_stoa {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stoa)
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
theorem rf_ldwb {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldwb)
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
  have hlen' : pre.length = rowBase g d.i + (p1 g + 18) + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
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
    intro _ _
    dsimp only
    rw [show rowBase g d.i + p1 g + 18 = rowBase g d.i + (p1 g + 18) by omega]
    exact acc_last h0 hlen' h3 (rdv_rd hb)
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
theorem rf_ldsb0 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldsb0)
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
  have hlen' : pre.length = rowBase g d.i + (p1 g + 22) + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
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
    rf_cond [hs]
  case rs0b =>
    intro _ _
    dsimp only
    rw [show rowBase g d.i + p1 g + 22 = rowBase g d.i + (p1 g + 22) by omega]
    exact acc_last h0 hlen' h3 (rdv_rd hb)
  case rs1a =>
    exact keep_rs1a hD hl rfl rfl (by rf_cond [hs])
  case rs1b =>
    exact keep_rs1b hD hl rfl rfl (by rf_cond [hs])
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_ldsb1 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .ldsb1)
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
  have hlen' : pre.length = rowBase g d.i + (p1 g + 26) + d.sub := by
    have := hl (by simp [hs, Site.inRow]); simp only [D.pos, hs] at this; omega
  split_ifs at hk with hok
  obtain rfl := (Option.some.inj hk).symm
  simp only [tileB]
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
    rf_cond [hs]
  case rs1b =>
    intro _ _
    dsimp only
    rw [show rowBase g d.i + p1 g + 26 = rowBase g d.i + (p1 g + 26) by omega]
    exact acc_last h0 hlen' h3 (rdv_rd hb)
  case i0 => intro h; cases h

set_option maxHeartbeats 4000000 in
theorem rf_stob {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .stob)
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
theorem rf_bar2 {d d' : D} {pre : List Event} {e : Event} {t : TState} {o : Option TState}
    (hJ : RunFacts P g d pre) (hs : d.site = .bar2)
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
  split_ifs at hn with hn'
  · obtain rfl := (Option.some.inj (Option.some.inj hn)).symm
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
    · rw [List.length_append, hlen]; rf_arith [hs]
    · rw [countP_snoc, hb0]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hb1]; simp only [Execution.isBarId]; rf_arith [hs]
    · rw [countP_snoc, hsc]; simp only [Execution.isShfl]; rf_arith [hs]
    case acc =>
      rf_cond [hs]
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

end
end PTX.Kernels.RmsNorm.Proof
