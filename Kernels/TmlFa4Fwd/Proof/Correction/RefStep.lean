-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.RefSucc
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.RefEv
import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' counts are kept by every step

`counts_step`: a step of the correction machine on an event of the state's shape that is no
undefined behaviour keeps the count conjuncts (`RefQ`), with the rounds done and the LSE stores
done updated: one more round at the end of a round, one more LSE store at an LSE site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)
open PTX.Flow.Arith32 (i32_addi toSigned_r32 ne_m1)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

/-! ### Words of the rounds' counter -/

theorem neg32_eq (x : BitVec 64) : neg32 x = i32 (0 - toSigned 32 (r32 x)) :=
  PTX.Flow.Arith32.neg_eq x

/-! ### Site facts -/

set_option maxRecDepth 100000 in
theorem sig_st_all :
    allSites.all (fun s => decide (sig s = some .st) == (s.isFst || s.isLse)) = true := by
  decide +kernel

theorem sig_st (s : Site) : sig s = some .st ↔ s.isFst = true ∨ s.isLse = true := by
  have := List.all_eq_true.mp sig_st_all s (mem_allSites s)
  simp only [beq_iff_eq] at this
  rw [← Bool.or_eq_true, ← this, decide_eq_true_iff]

set_option maxRecDepth 100000 in
theorem finalStores_k_all : allSites.all (fun s =>
    s.isFst || (List.finRange 4).all fun k => finalStores s k == finalStores s 0) = true := by
  decide +kernel

theorem finalStores_k {s : Site} (h : s.isFst = false) (k : Fin 4) :
    finalStores s k = finalStores s 0 := by
  have := List.all_eq_true.mp finalStores_k_all s (mem_allSites s)
  simp only [h, Bool.false_or, List.all_eq_true, List.mem_finRange, beq_iff_eq,
    forall_const] at this
  exact this k

theorem isPoll_fst {s : Site} (h : s.isFst = true) : s.isPoll = false := by
  cases s <;> simp_all [Site.isFst, Site.isPoll]

theorem blocks_frame {v v' : V} (h : frameT v v') : blocks p L g v' = blocks p L g v := by
  obtain ⟨-, h2, h3⟩ := h
  simp only [blocks, rowOff, coords, h2, h3]

theorem scmpi_lt2 (x : BitVec 64) :
    scmpi .lt .s x 2 = decide (toSigned 32 (r32 x) < 2) := by
  have h2 : toSigned 32 (i32 2) = 2 := by decide
  simp only [scmpi, PTX.compare, h2]

theorem blocks_trip (v : V) (t : BitVec 64) :
    blocks p L g { v with trip := t } = blocks p L g v := by
  simp only [blocks, rowOff, coords]

theorem moveOk_of {s s' : Site} (h : s' ∈ nexts s) : moveOk s s' = true :=
  List.all_eq_true.mp (List.all_eq_true.mp moves_ok s (mem_allSites s)) s' h

theorem bump_sig {e : Event} {n : Cnt → Nat} {s : Site}
    (hc : ∀ c, cls L g c e = decide (sig s = some c)) (c : Cnt) :
    Code.bump (cls L g) n e c = n c + if sig s = some c then 1 else 0 := by
  simp only [Code.bump, hc c, decide_eq_true_eq]

/-! ### The step -/

/-- The count conjuncts after a move to a listed successor with `r'` rounds done. -/
theorem refq_move {d d' : D} {e : Event} {n : Cnt → Nat} {r r' ℓ : Nat}
    (hQ : RefQ p L g d n r ℓ) (hc : ∀ c, cls L g c e = decide (sig d.site = some c))
    (hF : MoveFacts d d' e)
    (hp : ∀ c, passed (ptsOf c) d'.site r' =
      passed (ptsOf c) d.site r + if d.site.pc ∈ ptsOf c then 1 else 0)
    (hst : stOk d.site d'.site = true) (hl : lseOk d.site d'.site = true)
    (hk : d'.site.isFst = false ∨ kIn d'.site = 0)
    (hpre : preR d'.site = true → r' = 0)
    (hloop : inRound d'.site.pc = true →
      (r' : Int) + 1 < Bs p L g d'.v ∧ d'.v.trip = i32 (r' - Bs p L g d'.v))
    (htail : tailR d'.site = true →
      (r' : Int) + 1 = Bs p L g d'.v ∨ (r' = 0 ∧ Bs p L g d'.v < 2)) :
    RefQ p L g d' (Code.bump (cls L g) n e) r' (ℓ + if d.site.isLse then 1 else 0) := by
  obtain ⟨-, hk', hfst, -, -, -⟩ := hF
  refine ⟨fun c hcs => ?_, ?_, ?_, fun _ => hk', hpre, hloop, htail⟩
  · rw [bump_sig hc, hQ.cnt c hcs, hp c]
    congr 1
    by_cases h : sig d.site = some c
    · simp [h, (sig_pts d.site hcs).mpr h]
    · have : d.site.pc ∉ ptsOf c := fun hm => h ((sig_pts d.site hcs).mp hm)
      simp [h, this]
  · rw [bump_sig hc, hQ.st]
    simp only [stOk, beq_iff_eq] at hst
    have hd'k : finalStores d'.site d'.k = finalStores d'.site 0 := by
      rcases hk with h | h
      · exact finalStores_k h _
      · rw [hk', h]
    rw [hd'k, hst]
    by_cases hf : d.site.isFst = true
    · have h3 := hfst hf
      have : d.k = 3 := Fin.ext h3
      have hls : d.site.isLse = false := by
        obtain ⟨s, v, k⟩ := d; cases s <;> simp_all [Site.isFst, Site.isLse]
      simp [hf, this, hls, (sig_st d.site).mpr (.inl hf)]
      omega
    · have hf' : d.site.isFst = false := by simpa using hf
      rw [finalStores_k hf' d.k]
      by_cases hls : d.site.isLse = true
      · simp [hf', hls, (sig_st d.site).mpr (.inr hls)]; omega
      · have : sig d.site ≠ some .st := fun h => by
          rcases (sig_st d.site).mp h with h | h <;> simp_all
        simp [hf', hls, this]
  · simp only [lseOk, decide_eq_true_eq] at hl
    have := hQ.lse
    omega

set_option maxRecDepth 100000 in
/-- **The counts are kept by every step** of the correction machine on an event of the state's
shape that is no undefined behaviour. -/
theorem counts_step {d d' : D} {e : Event} {n : Cnt → Nat} {r ℓ : Nat}
    (hQ : RefQ p L g d n r ℓ) (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (h : succ p L g d e = some (some d')) :
    ∃ r' ℓ', RefQ p L g d' (Code.bump (cls L g) n e) r' ℓ' := by
  rcases succ_cases h with ⟨rfl, m, par, a, sc, hw⟩ | ⟨hf, hk3, rfl⟩ | hF
  · -- a failed poll: no class
    refine ⟨r, ℓ, ?_⟩
    have : Code.bump (cls L g) n e = n := by
      funext c; cases c <;> simp [Code.bump, cls, hw]
    rw [this]; exact hQ
  · -- the next element of a vector store
    have hc := ev_cls hev hub (fun hp => absurd hp (by simp [isPoll_fst hf])) (p := p)
    refine ⟨r, ℓ, fun c hcs => ?_, ?_, hQ.lse, fun h => absurd hf (by simp [h]), hQ.pre, hQ.loop,
      hQ.tail⟩
    · rw [bump_sig hc, hQ.cnt c hcs]
      have : sig d.site ≠ some c := fun h =>
        hcs (Option.some.inj (h.symm.trans ((sig_st d.site).mpr (.inl hf))))
      simp [this]
    · simp only [bump_sig hc, hQ.st, (sig_st d.site).mpr (.inl hf), ↓reduceIte]
      obtain ⟨s, v, k⟩ := d
      cases s <;> simp [Site.isFst] at hf
      simp only at hk3 ⊢
      simp only [finalStores]
      have : (k + 1).val = k.val + 1 := by
        rw [Fin.val_add]; simp only [Fin.val_one]; omega
      rw [this]; omega
  · have hc := ev_cls hev hub hF.2.2.2.1
    have hm := moveOk_of hF.1
    simp only [moveOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
    obtain ⟨⟨⟨⟨⟨hpm, hreg⟩, hst⟩, hl⟩, hk⟩, -⟩ := hm
    obtain ⟨s, v, k⟩ := d
    by_cases hr11 : s = .rarr 1 1
    · -- the end of a round
      subst hr11
      simp only [↓reduceIte] at hpm
      have hd' : d' = roundEnd ⟨.rarr 1 1, v, k⟩ := by
        simp only [succ, Fin.isValue, Option.some.injEq] at h; exact h.symm
      obtain ⟨hlt, htrip⟩ := hQ.loop (by dsimp only; decide)
      have hB := toSigned_r32 (blocks p L g v)
      simp only [Bs] at hlt htrip hB
      refine ⟨r + 1, _, refq_move hQ hc hF (passed_rmove r hpm) hst hl ?_ ?_ ?_ ?_⟩
      · rcases hk with h | h
        · exact .inl h
        · exact .inr h
      all_goals subst hd'
      all_goals simp only [roundEnd, D.ite, D.mk', htrip, i32_addi, Bs, blocks_trip]
      all_goals split <;> rename_i hne
      all_goals try simp only [Bs, blocks_trip]
      all_goals first
        | (intro h; exact absurd h (by try_rt ((try dsimp only); decide)))
        | skip
      · intro _
        have := (ne_m1 (by omega) (by omega)).mp hne
        refine ⟨?_, ?_⟩
        · push_cast; omega
        · exact congrArg i32 (by push_cast; ring)
      · intro _
        have : ¬ ((r : Int) - toSigned 32 (r32 (blocks p L g v)) + 1 ≠ -1) := fun h' =>
          hne ((ne_m1 (by omega) (by omega)).mpr h')
        left
        push_cast; omega
    · simp only [hr11, ↓reduceIte] at hpm
      by_cases hn1 : s = .nb 1
      · subst hn1
        have hd' : d' = enterRounds p L g ⟨.nb 1, v, k⟩ := by
          simp only [succ, Fin.isValue, Option.some.injEq] at h; exact h.symm
        have hr0 : r = 0 := hQ.pre (by dsimp only; decide)
        subst hr0
        clear h
        subst hd'
        refine ⟨0, _, refq_move hQ hc hF (passed_move 0 hpm) hst hl ?_ ?_ ?_ ?_⟩
        · rcases hk with h | h
          · exact .inl h
          · exact .inr h
        all_goals simp only [enterRounds, D.ite, D.mk', scmpi_lt2, Bs, blocks_trip]
        all_goals split <;> rename_i hlt
        all_goals try simp only [Bs, blocks_trip]
        all_goals first
          | (intro h; exact absurd h (by try_rt ((try dsimp only); decide)))
          | skip
        · intro _
          simp only [decide_eq_true_eq, not_lt] at hlt
          refine ⟨?_, ?_⟩
          · push_cast; omega
          · rw [neg32_eq]; simp
        · intro _
          simp only [decide_eq_true_eq] at hlt
          exact .inr ⟨by first | rfl | trivial, hlt⟩
      · have hsp : s.special = false := by
          cases s <;> simp_all [Site.special] <;>
            first
            | (rename_i a; fin_cases a <;> simp_all)
            | (rename_i a b; fin_cases a <;> fin_cases b <;> simp_all)
        simp only [hsp, Bool.false_eq_true, false_or, regOk, Bool.and_eq_true, Bool.or_eq_true,
          Bool.not_eq_true'] at hreg
        obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hreg
        have hfr := hF.2.2.2.2.1 hsp
        refine ⟨r, _, refq_move hQ hc hF (passed_move r hpm) hst hl ?_ ?_ ?_ ?_⟩
        · rcases hk with h | h
          · exact .inl h
          · exact .inr h
        · intro h; rcases hr3 with h' | h'
          · simp [h] at h'
          · exact hQ.pre h'
        · intro h
          have hin : inRound s.pc = true := by rcases hr1 with h' | h' <;> simp_all
          have hT := hfr (.inl h)
          rw [Bs, blocks_frame hT, hT.1]
          exact hQ.loop hin
        · intro h
          have hin : tailR s = true := by rcases hr2 with h' | h' <;> simp_all
          have hT := hfr (.inr h)
          rw [Bs, blocks_frame hT]
          exact hQ.tail hin

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
