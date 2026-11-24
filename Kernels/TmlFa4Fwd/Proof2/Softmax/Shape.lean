-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Ledger
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Shape
public import Lemmas.Flow.Step.ShapeTc

@[expose] public section

/-! # The softmax warps' events by state

The event a state of the softmax warps fires is the event of its site (`Ev`): the `setmaxnreg`;
barrier 2 with 416 threads (`bar1`, the arrival `barEnd`); the stage's named barrier with 128
threads (`bsync`); the arrival at the warp group's named barrier with the correction warps
(`narr`, `finarr`: barrier `nbW`, 64 threads); a poll of the stage's barrier at the site's offset
with the site's parity (`wq`, `ws`, `wb`, `pwend`, `wend`); an arrival of one unit at the stage's
barrier at the site's offset (`barr`, `parr`, `parr2`); a read of the scheduler's word or of the
request, or undefined behaviour; the scheduler's shuffles and ballots as in the output warp, the
ballot's predicate on the pass's CTA index; a Tensor Memory load, its implicit wait, a store, the
implicit wait of a `delayedTmem` store, a store wait (each but the waits for loads may fault); a
bias read or undefined behaviour; a shared store or undefined behaviour; a proxy fence; a warp
barrier and an election (or undefined behaviour); the exit. Addresses of reads, stores and Tensor
Memory accesses are not stated (their values are data or their source facts come later). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (r32 i32 addi andi shru scmp mad32 sub32 mul32 sel
  headsW prefixD)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- The offset of the barrier a poll site polls, and its parity word. -/
def pollOff : Site → Nat
  | .wq | .pwend _ | .wend _ => 192
  | .ws _ => 80
  | .wb _ => 320
  | _ => 0

def pollW (d : D) : BitVec 64 :=
  match d.site with
  | .wq => i32 1
  | .ws .first | .wb false | .pwend .first => i32 0
  | .ws _ => d.v.spar
  | .wb true => d.v.bpar
  | _ => d.v.ppar

/-- The offset of the barrier an arrival site signals. -/
def arrOff : Site → Nat
  | .barr _ => 336
  | .parr _ => 96
  | .parr2 _ => 112
  | _ => 0

/-- The output warp's site of a scheduler site. -/
def Site.toE : Site → Epilogue.Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | _ => .start

/-- A ballot's predicate: the lane's prefix of work is at most the pass's CTA index. -/
def votePredS (p : Params) (L : Launch) (g : Nat) (l : Bool) (c : Epilogue.D) : Bool :=
  scmp .le .s (mad32 (prefixD L g c) (headsW p) (sub32 c.cur (mul32 c.tot (headsW p))))
    (ctaOf p L g l)

/-- The first P store of a round with bias waits for the round's score loads at sub-step 0
(`delayedTmem`). -/
def Site.delayed : Site → Bool
  | .pst .first 0 | .pst .bias 0 => true
  | _ => false

/-- A read, or undefined behaviour. -/
abbrev rdOrUb (e : Event) : Prop := (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f

/-- A Tensor Memory load, or undefined behaviour. -/
abbrev tcLdOrUb (e : Event) : Prop :=
  (∃ a vals sh, e.kind = .tc (.ld a vals sh)) ∨ ∃ f, e.kind = .ub f

/-- The event-shape table of the softmax warps. -/
def Ev (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .setmax => ∃ inc n inst, e.kind = .setMaxReg inc n inst
  | .bar1 => e.kind = .bar 2 (some 416) .sync
  | .barEnd _ => e.kind = .bar 2 (some 416) .arrive ∨ ∃ f, e.kind = .ub f
  | .bsync _ => e.kind = .bar (if stg L g then 12 else 11) (some 128) .sync
  | .narr _ | .finarr => e.kind = .bar (nbW L g).toNat (some 64) .arrive
  | .wq | .ws _ | .wb _ | .pwend _ | .wend _ =>
      ∃ ok, e.kind = .wait (bl L g (pollOff d.site)) ((truncBits 32 (pollW d)).toNat % 2) ok true
        .cta
  | .barr _ | .parr _ | .parr2 _ => e.kind = .arrive (bl L g (arrOff d.site)) 0 1 true .cta
  | .word _ | .q0 | .q1 | .uk | .bld _ _ => rdOrUb e
  | .vote l => ∃ b, e.kind = .vote (2 ^ 32 - 1) (votePredS p L g l d.v.sc) b
  | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ =>
      Epilogue.Ev p L g { d.v.sc with site := d.site.toE } e
  | .sld _ _ => tcLdOrUb e
  | .sldw _ => if d.k.val == 1 then e.kind = .tc .waitLd ∨ (∃ f, e.kind = .ub f) else tcLdOrUb e
  | .pst _ _ => if d.site.delayed && d.k.val == 0 then e.kind = .tc .waitLd
      else (∃ a vals sh, e.kind = .tc (.st a vals sh)) ∨ ∃ f, e.kind = .ub f
  | .pwst _ _ => e.kind = .tc .waitSt ∨ ∃ f, e.kind = .ub f
  | .stat _ | .fin _ => (∃ a bs, e.kind = .wr a bs) ∨ ∃ f, e.kind = .ub f
  | .fence _ => ∃ k sc, e.kind = .fenceProxy k sc
  | .pws _ => (∃ inst, e.kind = .warpBar 4294967295 inst) ∨ ∃ f, e.kind = .ub f
  | .pel _ =>
      (∃ inst ld, e.pc = d.site.pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .exit _ => e.kind = .exit

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stS_cases (L : Launch) (g : Nat) : stS L g = 0 ∨ stS L g = 8 := by
  unfold stS; split <;> simp

/-- The stage's barrier base as the code computes it. -/
theorem sbS_val (hp : Pre p L m) : sbS L g = BitVec.ofNat 64 (L.sharedBase + (stS L g + 0)) := by
  have hs := hp.shared.2.1
  apply BitVec.eq_of_toNat_eq
  simp only [sbS, stS, Epilogue.add32, sel16, r32, truncBits, Mma.sbW]
  cases stg L g <;>
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat, BitVec.toNat_add] <;>
    norm_num <;> omega

/-- A barrier address of the stage, `sbS + n`, as the code computes it. -/
theorem sbSi_val (hp : Pre p L m) {n : Int} (h0 : 0 ≤ n) (hn : n < 1024) :
    addi (sbS L g) n = BitVec.ofNat 64 (L.sharedBase + (stS L g + n.toNat)) := by
  have hs := hp.shared.2.1
  rw [sbS_val hp]
  have h8 := stS_cases L g
  apply BitVec.eq_of_toNat_eq
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have h1 : (n % ((2 ^ 64 : Nat) : Int)).toNat = n.toNat := by omega
  rw [h1]
  rcases h8 with h8 | h8 <;> rw [h8] <;> omega

/-- An mbarrier address of the stage in a register, plus an offset: the stage's barrier. -/
theorem loc_bl (hp : Pre p L m) {t : TState} {r n : Nat} {off : Int} (h0 : 0 ≤ off)
    (hn : n + off.toNat < 1000) (h8 : (n + off.toNat) % 8 = 0)
    (hr : t.regs r = some (b32 (L.sharedBase + (stS L g + n)))) :
    mbarLoc L g t r off = .ok (bl L g (n + off.toNat)) := by
  have hs := hp.shared
  have hc := stS_cases L g
  have := Epilogue.loc_off (g := g) hp (k := stS L g + n) h0 (by omega) (by omega) hr
  rw [this]
  simp only [bl, Except.ok.injEq, Loc.mk.injEq, true_and]
  omega

theorem stg_bar_lt : (sel (stg L g) (i32 12) (i32 11)).toNat < 16 := by
  cases stg L g <;> decide

theorem stg_bar_val : (sel (stg L g) (i32 12) (i32 11)).toNat = if stg L g then 12 else 11 := by
  cases stg L g <;> decide

theorem nbW_lt (hp : Pre p L m) : (nbW L g).toNat < 16 := by
  have hb := hp.block
  simp only [nbW, stg, warpW]
  have hw : g % L.block / 32 < 16 := by rw [hb]; omega
  generalize g % L.block / 32 = w at hw ⊢
  interval_cases w <;> decide

theorem stg_bar_tval :
    (truncBits 32 (sel (stg L g) (i32 12) (i32 11))).toNat = if stg L g then 12 else 11 := by
  cases stg L g <;> decide

theorem trunc_imm128 : (truncBits 32 (BitVec.ofInt 64 128)).toNat = 128 := by decide
theorem trunc_imm64 : (truncBits 32 (BitVec.ofInt 64 64)).toNat = 64 := by decide

theorem nbW_tval (hp : Pre p L m) : (truncBits 32 (nbW L g)).toNat = (nbW L g).toNat := by
  have := nbW_lt (g := g) hp
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

theorem stg_bar_tlt : (truncBits 32 (sel (stg L g) (i32 12) (i32 11))).toNat < 16 := by
  cases stg L g <;> decide

theorem nbW_tlt (hp : Pre p L m) : (truncBits 32 (nbW L g)).toNat < 16 := by
  rw [nbW_tval hp]; exact nbW_lt hp

/-- A register's value at an address site. -/
macro "soft_val" : tactic => `(tactic| (
  simp only [valueOf, values, valuesStart, valuesRole, valuesTile, valuesP1, valuesBias,
    valuesPlain, valuesFin, sbSi, lookupLit, Option.getD_some, Option.getD_none]
  first
    | (rw [sbSi_val ‹Pre _ _ _› (by decide) (by decide)]; rfl)
    | (rw [sbS_val ‹Pre _ _ _›]; rfl)
    | rfl))

set_option hygiene false in
/-- The role's side conditions of `site_shape`: the CTA size, the mbarrier addresses, the
barrier ids, the Tensor Memory address registers and the assumptions of its Tensor Memory
sites. -/
macro "soft_addr" : tactic => `(tactic| first
  | (rw [‹Pre _ _ _›.block]; done)
  | (rw [‹Pre _ _ _›.block]; decide)
  | (rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcLdWait]; kernel_rfl)
  | (rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
  | exact hat.2.1
  | (rw [hat.1]; rfl)
  | (rw [hat.2.1]; decide)
  | (refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; soft_val)
  | with_reducible exact or32_lt _ _
  | with_reducible exact ori_lt _ _
  | exact stg_bar_lt
  | exact stg_bar_tlt
  | exact nbW_lt ‹Pre _ _ _›
  | exact nbW_tlt ‹Pre _ _ _›
  | (refine' loc_bl ‹Pre _ _ _› ?h0 ?hn ?h8 ?hr
     case hr => exact (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by soft_val)
     case h0 => decide
     case hn => decide
     case h8 => decide))

set_option hygiene false in
/-- The Tensor Memory instructions, the bias loads, the stores and the registered `bar.arrive`,
through `site_shape`'s hook. -/
scoped macro_rules
  | `(tactic| shape_inv $hf) => `(tactic| first
      | refine PTX.Flow.shape_store $hf rfl ?_ ?_
      | refine PTX.Flow.shape_ldAny $hf rfl rfl rfl ?_ ?_
      | refine PTX.Flow.shape_tcWaitSt $hf ?_ ?_
      | refine' PTX.Flow.shape_barArriveR $hf ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine' PTX.Flow.shape_tcSt $hf
          (by refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; soft_val)
          (by first | with_reducible exact or32_lt _ _ | with_reducible exact ori_lt _ _)
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl) ?_ ?_
      | refine PTX.Flow.shape_tcStWait $hf
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
          hat.2.1 (by rw [‹Pre _ _ _›.block]) ?_
      | refine' PTX.Flow.shape_tcStStore $hf
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
          (by rw [hat.2.1]; exact Nat.succ_ne_zero 0)
          (by refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; soft_val)
          (by first | with_reducible exact or32_lt _ _ | with_reducible exact ori_lt _ _) ?_ ?_
      | refine PTX.Flow.shape_tcLd $hf (by intro s hs; cases hs)
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcLdWait]; kernel_rfl) ?_ ?_
      | refine' PTX.Flow.shape_tcLdLoad $hf (by intro s hs; cases hs)
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcLdWait]; kernel_rfl)
          (hat.2.1.trans rfl)
          (by refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; soft_val)
          (by first | with_reducible exact or32_lt _ _ | with_reducible exact ori_lt _ _) ?_ ?_
      | refine PTX.Flow.shape_tcLdWait $hf
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcLdWait]; kernel_rfl)
          (by rw [hat.2.1]; exact Nat.succ_ne_zero 0) ?_ ?_)

/-- A shape alternative that `simp` reduced to `True`. -/
scoped macro_rules | `(tactic| shape_close) => `(tactic| trivial)

/-- A barrier event whose id and count the code reads as truncated words. -/
scoped macro_rules | `(tactic| shape_close) => `(tactic|
  (simp only [stg_bar_tval, trunc_imm128, trunc_imm64, nbW_tval ‹Pre _ _ _›]; done))

/-- A shared store of a data register, without its address and value: a write, or undefined
behaviour (an override of `site_shape`, whose store lemma names the value). -/
syntax "soft_st" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| soft_st) => `(tactic| (
      intro t ins e o hat hi hc hf
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine PTX.Flow.shape_store hf rfl ?_ ?_
      all_goals (intros; simp only [Ev]; shape_close)))

/-- The shape obligations of the sites of `s` that the theorem's `hs` admits. -/
syntax "soft_shape" (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| soft_shape $[except [$ovs,*]]?) => `(tactic|
  site_shape s $[except [$ovs,*]]? skip_by (simp at hs)
    unfolding [Ev, Int.reduceToNat, Nat.reduceAdd, Nat.reduceMod, Nat.reduceBEq, ite_true,
      ite_false, pollOff, pollW, arrOff, Site.toE, Site.delayed,
      rdOrUb, tcLdOrUb, votePredS,
      ctaOf, Epilogue.Ev, Epilogue.partialAt]
    reg_vals [valueOf, values, valuesStart, valuesRole, valuesScan, valuesSelect, valuesSelect2,
      valuesReq, valuesTile, valuesP1, valuesBias, valuesPlain, valuesFin, Epilogue.partials,
      Epilogue.loopRegs, Epilogue.lanePreds, lookupLit, livePc]
    addr_by (soft_addr))

/-- A state that its invariant excludes: its shape obligation holds vacuously. -/
theorem shapeAt_junk {d : D}
    (h : ¬ ((d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc)) :
    (code p L g).ShapeAt (Ev p L g) d :=
  fun _ hi => absurd hi h

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
