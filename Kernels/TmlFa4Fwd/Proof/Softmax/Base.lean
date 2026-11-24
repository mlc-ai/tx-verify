-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.LdWait
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Lemmas.Flow.LaunchParams
public import Lemmas.Flow.Step.LoadVec
public import Lemmas.Flow.Step.SiteIte
public import Lemmas.Flow.Step.TcSteps
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # Shared facts and tactics of the softmax warps' step files

The launch facts the segments use (the explicit parameters: the exponent and bias scales
besides the output warp's, the CTA index as the second pass's `%ctaid.x` reads it), the decision
rules of the scheduler loop's exit test, and the role's tactic for the obligations of one family
of sites (`soft_sites`): `site_cases` over the site, segments by `seg_fp` closed by `rfl` or
`sym_close`, the successor's invariant by its sub-step (`soft_inv`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
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

theorem param14 : param 14 =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
    ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
    ptrbf16gmemalign16o1i64div8_0_param_14" := by
  have h : toString (14 : Nat) = "14" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (14 / 10 : Nat) = 1 by decide, show (14 % 10 : Nat) = 4 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 4) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_four.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

theorem params {p : Params} {L : Launch} {m : Mem0} (hp : Pre p L m) :
    explicitParams L (ps p) = L :=
  explicitParams_eq fun n v h => by
    simp only [ps, Epilogue.ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← param12]
      exact (hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])).2
    · rw [← param14]
      exact (hp.values (14, p.invScaleBits) (by simp [Params.scalarWords])).2
    · rw [← Epilogue.param17]; exact (hp.values (17, p.heads) (by simp [Params.scalarWords])).2
    · rw [← Epilogue.param19]; exact (hp.values (19, p.batch) (by simp [Params.scalarWords])).2
    · rw [← Epilogue.param22]; exact (hp.values (22, 800) (by simp [Params.scalarWords])).2

/-- The CTA index as the second pass reads it is the launch's (a one-dimensional grid of fewer
than `2 ^ 31` CTAs). -/
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
  generalize g / L.block = c at hc ⊢
  omega

/-- The scheduler loop's exit test after the last group, on the second pass's CTA term. -/
theorem ctaR_succ_le {p : Params} {L : Launch} {m : Mem0} {g : Nat} (hp : Pre p L m)
    (hg : g < L.threads) :
    Epilogue.scmp .le .s (Epilogue.addi (ctaR p L g) 1) (ctaR p L g) = false := by
  rw [ctaR_eq hp hg]
  exact Epilogue.cta_succ_le hp hg

scoped macro_rules | `(tactic| sym_decide) => `(tactic| with_reducible exact ctaR_succ_le ‹_› ‹_›)

/-- The role's exit test (pc 7743): the warp index of a softmax warp rounded down to a multiple
of four is not eight. -/
theorem warp_ne8 {L : Launch} {g : Nat} (hw : g % L.block / 32 < 8) :
    Epilogue.scmpi .ne .b (Epilogue.andi (warpW L g) (-4)) 8 = true := by
  simp only [warpW]
  generalize g % L.block / 32 = w at hw ⊢
  interval_cases w <;> decide

scoped macro_rules | `(tactic| sym_decide) => `(tactic| with_reducible exact warp_ne8 ‹_›)

/-- The role's landing obligation: the successor's sub-step and accumulator are those of a
first state (in every branch of a conditional successor), its segment by `seg_auto`, else
`seg_sym`, and its invariant by the role's tactic. Tried before the library's rules. -/
scoped macro_rules
  | `(tactic| lands_auto ($seg) ($inv)) => `(tactic| (
      intros
      refine ⟨?seg, ?sub, ?acc, ?inv⟩
      case sub => first | rfl | ((repeat' ite_cases) <;> rfl)
      case acc => first | rfl | ((repeat' ite_cases) <;> rfl)
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
macro "soft_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- The invariant of a successor: a first state, or a state midway through its instruction. -/
macro "soft_inv" : tactic => `(tactic| first
  | exact fun _ => Or.inl ⟨rfl, rfl, rfl⟩
  | ((intro _; repeat' split) <;> exact Or.inl ⟨rfl, rfl, rfl⟩)
  | (intro _; right; simp [PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Site.midOk]; done)
  | (intro _; right; simp_all [PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Site.midOk]; done))

/-- `soft_sites s except […] using […]`: the obligations of the sites of `s` that the
theorem's hypothesis `hs` admits. -/
syntax "soft_sites " (ppSpace colGt ident)+ (" except " "[" siteOverride,* "]")?
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| soft_sites $ss* $[except [$ovs,*]]? $[using [$us,*]]?) => do
    let base : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.succ),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.word32),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.scAt),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.D.mk'),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.D.ite),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterTotal),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.loopHead),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.scanExit),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.passStart),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterTiles),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterFirst),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterBias),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterPlain),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.plainEntry),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterLoads),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.afterRound),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.pstNext),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Softmax.ctaOf),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.loopOf),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.Scan.late),
      ← `(Lean.Parser.Tactic.simpLemma| PTX.Kernels.TmlFa4Fwd.Proof.Epilogue.tlOf)]
    let ls := base ++ (match us with | some u => u.getElems | none => #[])
    `(tactic|
      site_cases $ss* $[except [$ovs,*]]? skip_by (simp at hs)
        trans [$ls,*]
        seg_by (soft_seg) inv_by (soft_inv) guard_by (trivial))

/-- A Tensor Memory store that no assumption makes wait (an override of `soft_sites`). -/
syntax "soft_tst" : tactic
macro_rules
  | `(tactic| soft_tst) => `(tactic| (
      refine' (PTX.Flow.Code.step_issueAt (dn := ?dn) ?hc ?hadv ?hn rfl rfl ?hl)
      case hc => code_lookup
      case hadv =>
        intro t e u hpc hf
        exact PTX.Flow.fires_tcSt_next
          (by rw [hpc, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; rfl) hf
      case hn => intro e; rfl
      case hl => lands_auto (soft_seg) (soft_inv)))

/-- The implicit wait of a round's first P store (a site of the kernel's `delayedTmem`
assumption, an override of `soft_sites`): the thread stays at the store at sub-step 1. -/
syntax "soft_tstw" : tactic
macro_rules
  | `(tactic| soft_tstw) => `(tactic| (
      refine PTX.Flow.Code.step_tcStWait (by code_lookup)
        (by rw [PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl) rfl
        (fun _ => rfl) rfl rfl rfl rfl
        (fun _ => Or.inr ⟨rfl, rfl⟩)))

theorem b32_toNat (x : BitVec 64) : Value.bits 32 x = b32 x.toNat := by
  simp [b32]

theorem or32_lt (x y : BitVec 64) : (or32 x y).toNat < 2 ^ 32 := by
  simp only [or32, Epilogue.r32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
  exact Nat.or_lt_two_pow (by omega) (by omega)

theorem ori_lt (x : BitVec 64) (n : Int) : (Mma.ori x n).toNat < 2 ^ 32 := by
  simp only [Mma.ori, Epilogue.r32, Epilogue.i32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
  exact Nat.or_lt_two_pow (by omega) (by omega)

/-- A plain round's score load at sub-step 0 (a site of the kernel's `tcLdDataflow`
assumption): the load writes its 32 destinations (`5188 + 32 c` onward), the machine records the
reals they hold, and the thread stays at the instruction for its implicit wait, whose facts are
those of the registers live after the load: the destinations with their reals
(`valuesLoaded`), every other register with its value at the load. -/
theorem sldp_ok {p : Params} {L : Launch} {g : Nat} {c : Fin 4} {v : V}
    {gd : Option (Nat × Bool)} {ds : List Nat} {ta : Nat} {sh : TcShape} {a0 : Nat}
    (hc : kernel.code[(Site.sld .plain c).pc]? = some ⟨gd, .tcLd ds ta sh none⟩)
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : Assumptions.all.any (·.tcLdWait (Site.sld .plain c).pc) = true)
    (hta : (ta, b32 a0) ∈ factsD p L g (D.mk' (.sld .plain c) v)) (ha0 : a0 < 2 ^ 32)
    (hpc : (Site.sldw c).pc = (Site.sld .plain c).pc)
    (hds : ds = (List.range 32).map (5188 + 32 * c.val + ·))
    (hlive : (liveD ((Site.sld .plain c).pc + 1)).all (fun r =>
      ds.contains r || (liveD (Site.sld .plain c).pc).contains r) = true) :
    (codeD p L g).StepOk (D.mk' (.sld .plain c) v) := by
  refine PTX.Flow.Code.step_tcLdLoad
    (nv := fun vals => match flAll vals with
      | some xs => some (some (⟨.sldw c, { v with sv := Function.update v.sv c xs }, 1, []⟩ : D))
      | none => some none) hc hsh hw hta ha0
    (fun _ vals => by simp only [codeD, succ]; cases flAll vals <;> rfl) rfl rfl
    (fun vals => by cases flAll vals <;> simp) ?_
  intro vals d' hv
  cases hx : flAll vals with
  | none => simp only [hx, Option.some.injEq, reduceCtorEq] at hv
  | some xs =>
  simp only [hx, Option.some.injEq] at hv
  subst hv
  refine ⟨hpc, rfl, rfl, fun _ => Or.inr ⟨rfl, rfl⟩, fun hlen t hF => ?_⟩
  subst hds
  have hnd : ((List.range 32).map (5188 + 32 * c.val + ·)).Nodup :=
    (List.nodup_map_iff (fun a b h => by omega)).mpr List.nodup_range
  show Holds _ (Flow.factsFrom (liveD ((Site.sldw c).pc + 1)) _)
  rw [hpc]
  refine PTX.Flow.holds_setRegs_live hF hnd hlen ?_ ?_
  · intro q hq
    simp only [List.length_map, List.length_range] at hq
    rw [flAll_get hx (by simp [hlen, hq])]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
      Option.map_some, Option.getD_some, valueOfD, valuesData, valuesData0, valuesLoaded,
      List.lookup_append,
      lookup_shift _ _ (List.mem_range.mpr hq), Option.some_or, Function.update_self]
  · intro q hq hnq
    have h := List.all_eq_true.mp hlive q hq
    simp only [Bool.or_eq_true, List.contains_iff_mem] at h
    refine ⟨h.resolve_left hnq, ?_⟩
    have hn : (valuesLoaded { v with sv := Function.update v.sv c xs } c).lookup q = none := by
      refine lookup_shift_none _ _ fun i hi e => hnq ?_
      exact List.mem_map.mpr ⟨i, hi, e⟩
    simp only [valueOfD, valuesData, valuesData0, List.lookup_append, hn, Option.none_or,
      valuesPairs_update .plain v c xs (le_refl _)]
    rfl

/-- A plain round's score load at sub-step 0 (an override of `soft_sites`). -/
syntax "soft_sldp" : tactic
macro_rules
  | `(tactic| soft_sldp) => `(tactic| (
      refine' PTX.Kernels.TmlFa4Fwd.Proof.Softmax.sldp_ok ?hc ?hsh ?hw ?hta ?ha0 rfl ?hds ?hlive
      case hc => code_lookup
      case hsh => intro s hs; cases hs
      case hw => ld_wait
      case hta =>
        rw [← PTX.Kernels.TmlFa4Fwd.Proof.Softmax.b32_toNat]
        exact PTX.Flow.mem_factsFrom (by lit_mem)
      case ha0 => first
        | with_reducible exact PTX.Kernels.TmlFa4Fwd.Proof.Softmax.or32_lt _ _
        | with_reducible exact PTX.Kernels.TmlFa4Fwd.Proof.Softmax.ori_lt _ _
      case hds => decide
      case hlive => kernel_rfl))

/-- A state whose sub-step is not one its site has: its obligation holds vacuously. -/
theorem stepAt_junk {p : Params} {L : Launch} {g : Nat} {d : D}
    (h : ¬ ((d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc)) :
    (codeD p L g).StepAt d :=
  ⟨fun hi => absurd hi h, fun _ _ hi => absurd hi h⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
