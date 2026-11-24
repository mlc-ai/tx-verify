-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Machine
public import Lemmas.Flow.Step.TcSteps
public import Lemmas.Flow.Step.SiteIte
public import Lemmas.Flow.LaunchParams

@[expose] public section

/-! # Shared facts and tactics of the correction warps' step files

The launch facts the segments use (the explicit parameters, with `param_12` besides the output
warp's, and the CTA index as `%ctaid.x` reads it), and the role's tactic for the obligations of
one family of sites (`corr_sites`): `site_cases` over the site, segments by `seg_fp` closed by
`rfl` or `sym_close` (`corr_seg`), the successor's invariant by its sub-step (`corr_inv`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem param12 : param 12 =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
    ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
    ptrbf16gmemalign16o1i64div8_0_param_12" := by
  have h : toString (12 : Nat) = "12" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (12 / 10 : Nat) = 1 by decide, show (12 % 10 : Nat) = 2 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 2) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_two.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

theorem params {p : Params} {L : Launch} {m : Mem0} (hp : Pre p L m) :
    explicitParams L (ps p) = L :=
  explicitParams_eq fun n v h => by
    simp only [ps, Epilogue.ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← param12]
      exact (hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])).2
    · rw [← Epilogue.param17]; exact (hp.values (17, p.heads) (by simp [Params.scalarWords])).2
    · rw [← Epilogue.param19]; exact (hp.values (19, p.batch) (by simp [Params.scalarWords])).2
    · rw [← Epilogue.param22]; exact (hp.values (22, 800) (by simp [Params.scalarWords])).2

/-- The CTA index as the role reads it is the launch's (a one-dimensional grid of fewer than
`2 ^ 31` CTAs). -/
theorem ctaR_eq {p : Params} {L : Launch} {m : Mem0} {g : Nat} (hp : Pre p L m)
    (hg : g < L.threads) : ctaR p L g = Epilogue.ctaW L g := by
  have hb := hp.block
  have hgr := hp.grid
  have hc : g / L.block < 2 ^ 32 := by
    simp only [Launch.threads] at hg
    rw [hb] at hg ⊢
    have : g / 512 < L.grid := by omega
    omega
  simp only [ctaR, explicitParams_ctaidOf, explicitParams_block,
    Launch.oneDim_ctaidOf hp.cluster.2.2, Epilogue.ctaW, truncBits]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  show (g / L.block % 2 ^ 64) % 2 ^ 32 % 2 ^ 64 = g / L.block % 2 ^ 64
  rw [Nat.mod_eq_of_lt (show g / L.block < 2 ^ 64 by omega), Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (show g / L.block < 2 ^ 64 by omega)]

/-- The shared barrier at offset `o` of the lane's CTA. -/
abbrev bl (L : Launch) (g o : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + o⟩

/-- The scheduler loop's exit test after the last group, on the role's CTA term. -/
theorem ctaR_succ_le {p : Params} {L : Launch} {m : Mem0} {g : Nat} (hp : Pre p L m)
    (hg : g < L.threads) :
    Epilogue.scmp .le .s (Epilogue.addi (ctaR p L g) 1) (ctaR p L g) = false := by
  rw [ctaR_eq hp hg]
  exact Epilogue.cta_succ_le hp hg

scoped macro_rules | `(tactic| sym_decide) => `(tactic| with_reducible exact ctaR_succ_le ‹_› ‹_›)

/-- The role's landing obligation: the successor's sub-step is 0 (in every branch of a
conditional successor), its segment by `seg_sym` (which walks first and splits a conditional
end itself), else `seg_auto`, and its invariant by the role's tactic. Tried before the
library's rules. -/
scoped macro_rules
  | `(tactic| lands_auto ($seg) ($inv)) => `(tactic| (
      intros
      refine ⟨?seg, ?sub, rfl, ?inv⟩
      case sub => first | rfl | ((repeat' ite_cases) <;> rfl)
      case seg =>
        intro _
        site_norm
        try dsimp only [PTX.Flow.Code.electFacts]
        try drop_norm
        first
          | seg_sym using $seg
          | seg_auto using $seg
      case inv =>
        site_norm
        ($inv)))

/-- The role's segments. -/
macro "corr_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- The invariant of a successor: a state at sub-step 0, or the next element of a vector
store, or the implicit wait of a rescale load. -/
macro "corr_inv" : tactic => `(tactic| first
  | exact fun _ => Or.inl rfl
  | exact fun _ => Or.inr trivial
  | exact fun _ => Or.inr rfl
  | ((intro _; repeat' split) <;> exact Or.inl rfl))

/-- `corr_sites s except […] using […]`: the obligations of the sites of `s` that the theorem's
hypothesis `hs` admits; the lemmas after `using` (hypotheses on the recorded values, say) join
the successor's evaluation. -/
syntax "corr_sites " (ppSpace colGt ident)+ (" except " "[" siteOverride,* "]")?
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_sites $ss* $[except [$ovs,*]]?) => `(tactic|
      site_cases $ss* $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, word32, real32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit,
          passStart, afterTiles, enterRounds, roundEnd, afterVote, afterFinal, afterLse,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.tlOf]
        seg_by (corr_seg) inv_by (corr_inv) guard_by (trivial))
  | `(tactic| corr_sites $ss* $[except [$ovs,*]]? using [$us,*]) => `(tactic|
      site_cases $ss* $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, word32, real32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit,
          passStart, afterTiles, enterRounds, roundEnd, afterVote, afterFinal, afterLse,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.tlOf, $us,*]
        seg_by (corr_seg) inv_by (corr_inv) guard_by (trivial))

/-- `corr_issue lemma`: the obligation of an event that continues at the next instruction by
`lemma` (an override of `corr_sites`). -/
syntax "corr_issue " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_issue $adv) => `(tactic|
      issue_step $adv
        trans [succ, word32, real32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit,
          passStart, afterTiles, enterRounds, roundEnd, afterVote, afterFinal, afterLse,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.tlOf]
        seg_by (corr_seg) inv_by (corr_inv))

/-- A state whose sub-step is not one its site has: its obligation holds vacuously. -/
theorem stepAt_junk {p : Params} {L : Launch} {g : Nat} {d : D}
    (h : ¬ (d.k = 0 ∨ d.site.midOk d.k)) : (code p L g).StepAt d :=
  ⟨fun hi => absurd hi h, fun _ _ hi => absurd hi h⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
