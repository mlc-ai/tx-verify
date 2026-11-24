-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSync

@[expose] public section

/-! # The softmax warps' Tensor Memory loads and stores

A softmax thread's `tcgen05.ld` is a load site `ld lp c`: 32 words of its stage's score columns
`32 c …` (`soft_tld`); its implicit `tcgen05.wait::ld` is the next event (the state after the
load is the site `ldW lp c`, whose event is the wait). Its `tcgen05.st` is a store site
`pst lp c`: 16 words of the stage's probability columns `64 + 16 c …` (`soft_tst`). The counts
of the state (`Softmax.Counts`) place every load and store in its tile: a load or a store of
tile `T` of item `i` has `n i + T + 1` successful S-full polls before it, the loads of the tile
come before its stores, and each store site is passed once per tile. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The column of a softmax Tensor Memory address at column `col` of the stage, word `p`. -/
theorem soft_column (L : Launch) (g h col p : Nat) (hw : warpOf L g < 8) (hc : col < 256) :
    (tcDataCell32 L h (Softmax.tmem L g col) p).column = 128 * Softmax.stOf L g + col + p := by
  simp only [tcDataCell32, Softmax.tmem]
  have : Softmax.stOf L g < 2 := by simp only [Softmax.stOf]; omega
  omega

/-- A tile of an item: `n i + T + 1` S-full polls before its loads and stores determine the item
and the tile. -/
theorem tile_inj {n i T i' T' : Nat} (hT : T < n) (hT' : T' < n)
    (h : n * i + T = n * i' + T') : i = i' ∧ T = T' := by
  rcases Nat.lt_or_ge i i' with hl | hl
  · have : n * i + n ≤ n * i' := by nlinarith
    omega
  rcases Nat.lt_or_ge i' i with hl' | hl'
  · have : n * i' + n ≤ n * i := by nlinarith
    omega
  have : i = i' := by omega
  subst this
  omega

/-- The count of a predicate on a later prefix includes an earlier selected event. -/
theorem countP_take_lt {g j k : Nat} {e : Event} {p : Event → Bool} (he : X.get (g, j) = some e)
    (hp : p e = true) (hjk : j < k) :
    ((X.tr g).take j).countP p + 1 ≤ ((X.tr g).take k).countP p := by
  have he' : (X.tr g)[j]? = some e := he
  have h1 : ((X.tr g).take (j + 1)).countP p = ((X.tr g).take j).countP p + 1 := by
    rw [List.take_add_one, he', Option.toList_some, List.countP_append]
    simp [hp]
  have h2 : ((X.tr g).take (j + 1)).countP p ≤ ((X.tr g).take k).countP p :=
    (List.take_sublist_take_left (by omega)).countP_le
  omega

/-- The `tcgen05.st` of a store site has 16 sources. -/
theorem pst_len (lp : Bool) (c : Fin 4) :
    ∃ ta ss, kernel.code[(Softmax.Site.pst lp c).pc]? = some ⟨none, .tcSt ta ss⟩ ∧
      ss.length = 16 := by
  cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
  · exact ⟨_, _, Flow.code_tmemStore_0, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_1, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_2, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_3, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_4, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_5, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_6, rfl⟩
  · exact ⟨_, _, Flow.code_tmemStore_7, rfl⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A softmax thread's `tcgen05.ld`** loads 32 words of its stage's score columns `32 c …`, at
a load site. -/
theorem soft_tld {g i pc a : Nat} {vals : List Value} (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) :
    ∃ (d : Softmax.D) (lp : Bool) (c : Fin 4),
      Frame.stateAt (code L) X g i = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take i) ∧ Softmax.Inv L g d ∧ d.site = .ld lp c ∧
      a = Softmax.tmem L g (32 * c.val) ∧ vals.length = 32 := by
  obtain ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  have h4 := hat.2.2.2.2
  cases hsd : d.site with
  | ld lp c =>
    refine ⟨d, lp, c, hσ, hc, hi, hsd, ?_, ?_⟩
    · simp only [Softmax.Ev, hsd] at hev
      obtain ⟨vals', hk⟩ := hev
      injection hk with hk
      injection hk with h1 h2
    · have key : ∀ {ds : List Nat} {ta col : Nat},
          kernel.code[d.site.pc]? = some ⟨none, .tcLd ds ta⟩ →
          t.regs ta = some (b32 (Softmax.tmem L g col)) → col < 2 ^ 20 →
          vals.length = ds.length := by
        intro ds ta col hcd hr hcol
        obtain rfl := Option.some.inj (hcode.symm.trans hcd)
        have hwt : asms.any (·.tcLdWait t.pc) = true := by
          rw [hat.1, hsd]; exact Softmax.tcLdWait_ld lp c
        have hsub : t.sub = 0 := by rw [hat.2.1, hsd]; rfl
        obtain ⟨vals', hl, he', -⟩ := fires_tcLd_load (fun _ h => by cases h) hwt hsub hr
          (Softmax.tmem_lt hi.warp _ hcol) hf
        injection he' with h1 h2
        injection h2 with h3
        injection h3 with h4 h5
        rw [h5, hl]
      cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_0) (Softmax.regs_ldF0 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_1) (Softmax.regs_ldF1 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_2) (Softmax.regs_ldF2 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_3) (Softmax.regs_ldF3 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_4) (Softmax.regs_ldT0 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_5) (Softmax.regs_ldT1 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_6) (Softmax.regs_ldT2 hsd h4) (by decide)
      · exact key (by rw [hsd]; exact Flow.code_tmemLoad_7) (Softmax.regs_ldT3 hsd h4) (by decide)
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

/-- **A softmax thread's `tcgen05.st`** stores 16 words of its stage's probability columns
`64 + 16 c …`, at a store site. -/
theorem soft_tst {g i pc a : Nat} {vals : List Value} (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc, .tc (.st a vals .s32x32b)⟩) :
    ∃ (d : Softmax.D) (lp : Bool) (c : Fin 4),
      Frame.stateAt (code L) X g i = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take i) ∧ Softmax.Inv L g d ∧ d.site = .pst lp c ∧
      a = Softmax.tmem L g (64 + 16 * c.val) ∧ vals.length = 16 := by
  obtain ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  cases hsd : d.site with
  | pst lp c =>
    refine ⟨d, lp, c, hσ, hc, hi, hsd, ?_, ?_⟩
    · simp only [Softmax.Ev, hsd] at hev
      obtain ⟨vals', hk⟩ := hev
      injection hk with hk
      injection hk with h1 h2
    · obtain ⟨ta, ss, hcd, hl⟩ := pst_len lp c
      rw [hsd] at hcode hf
      obtain rfl := Option.some.inj (hcode.symm.trans hcd)
      rw [fires_tcSt_len (fun _ h => by cases h) hf rfl, hl]
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
