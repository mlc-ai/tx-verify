-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.LdWait
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.Correction.Base
public import Kernels.TmlFa4Fwd.Proof.Correction.Loads
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Lemmas.Flow.Next
public import Lemmas.Flow.Step.ShapeTc
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl

@[expose] public section

/-! # The correction warps' events by state

The event a state of the correction warps fires is the event of its site (`Ev`, `shape`): the
`setmaxnreg`; barrier 2 with 416 threads (`bar1`, and the arrival `barEnd`); the lane's named
barrier with its softmax warp (`nb`, `rbar`, `fbar`: barrier `nbW k`, 64 threads); an arrival of
one unit on the barrier of the site (`arr`, `free`, `rarr`, `farr0`, `farr`, `fdone`); a poll of
the site's barrier with the site's parity (`fw`, `wend`); a read of the request or of a statistics
word, or undefined behaviour; the scheduler's shuffles and ballots as in the output warp, the
first pass's ballot on the role's CTA index; a rescale stage's ballot of the scale's comparison
with 1; a Tensor Memory load, store or wait (a load or store may fault); a shared or global
store element or undefined behaviour; a proxy fence; the exit. The machine stops exactly on a
returned value of another kind than the site's (`ret`, `stop_iff`), and at the LSE when a row
sum is not positive (the `lg2` rule's condition), which `stop_iff` states as well. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi andi shru scmp mad32 sub32 mul32
  headsW prefixD)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- The shared offset of the barrier an arrival site signals. -/
def arrOff : Site → Nat
  | .arr 0 => 96
  | .arr 1 => 104
  | .free => 192
  | .rarr 0 0 => 96
  | .rarr 0 1 => 200
  | .rarr 1 0 => 104
  | .rarr 1 1 => 192
  | .farr0 => 200
  | .farr 0 => 192
  | .farr 1 => 200
  | .fdone 0 0 => 96
  | .fdone 0 1 => 208
  | .fdone 1 0 => 104
  | .fdone 1 1 => 216
  | _ => 0

/-- The shared offset of the barrier a poll site polls, and its parity. -/
def pollOff : Site → Nat
  | .fw 0 0 => 144
  | .fw 0 1 => 224
  | .fw 1 0 => 152
  | .fw 1 1 => 232
  | .wend _ => 232
  | _ => 0
def pollPar : Site → Nat
  | .fw _ k => k.val
  | .wend l => if l then 0 else 1
  | _ => 0

/-- The lane's two named barriers with its softmax warp, and which one a site meets. -/
def nbW (L : Launch) (g : Nat) : Fin 2 → BitVec 64
  | 0 => nb0W L g
  | 1 => nb1W L g
def barK : Site → Fin 2
  | .nb k => k
  | .rbar st => st
  | .fbar st => st
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

/-- A first-pass ballot's predicate: the lane's prefix of work is at most the role's CTA index. -/
def votePredR (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Bool :=
  scmp .le .s (mad32 (prefixD L g c) (headsW p) (sub32 c.cur (mul32 c.tot (headsW p))))
    (ctaR p L g)

/-- A read of a word, or undefined behaviour. -/
abbrev rdOrUb (e : Event) : Prop := (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f

/-- The event-shape table of the correction warps. -/
def Ev (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .setmax => ∃ inc n inst, e.kind = .setMaxReg inc n inst
  | .bar1 => e.kind = .bar 2 (some 416) .sync
  | .barEnd _ => e.kind = .bar 2 (some 416) .arrive ∨ ∃ f, e.kind = .ub f
  | .nb _ | .rbar _ | .fbar _ => e.kind = .bar (nbW L g (barK d.site)).toNat (some 64) .sync
  | .arr _ | .free | .rarr _ _ | .farr0 | .farr _ | .fdone _ _ =>
      e.kind = .arrive (bl L g (arrOff d.site)) 0 1 true .cta
  | .fw _ _ | .wend _ =>
      ∃ ok, e.kind = .wait (bl L g (pollOff d.site)) (pollPar d.site) ok true .cta
  | .word _ | .q0 | .q1 | .uk | .rscale _ | .fsum _ | .fmax _ => rdOrUb e
  | .vote _ => ∃ b, e.kind = .vote (2 ^ 32 - 1) (votePredR p L g d.v.sc) b
  | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ =>
      Epilogue.Ev p L g { d.v.sc with site := d.site.toE } e
  | .rvote st => ∃ b, e.kind = .vote (2 ^ 32 - 1)
      (Assumption.erealCompare .lt ((sOf d.v st).real : EReal) (1 : ℝ)) b
  | .rld _ _ | .fld _ _ => (∃ a vals sh, e.kind = .tc (.ld a vals sh)) ∨ ∃ f, e.kind = .ub f
  | .rldw _ _ => e.kind = .tc .waitLd ∨ (∃ a vals sh, e.kind = .tc (.ld a vals sh)) ∨
      ∃ f, e.kind = .ub f
  | .fwl _ _ => e.kind = .tc .waitLd
  | .rst _ _ => (∃ a vals sh, e.kind = .tc (.st a vals sh)) ∨ ∃ f, e.kind = .ub f
  | .rwait _ => e.kind = .tc .waitSt ∨ ∃ f, e.kind = .ub f
  | .fst _ _ _ | .lse _ => (∃ a bs, e.kind = .wr a bs) ∨ ∃ f, e.kind = .ub f
  | .fence _ => ∃ k sc, e.kind = .fenceProxy k sc
  | .exit _ => e.kind = .exit

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem andi3_le (x : BitVec 64) : (andi x 3).toNat ≤ 3 := by
  simp only [andi, r32, i32, BitVec.toNat_and]
  exact (Nat.and_le_right).trans (by decide)

theorem nb_val (x : BitVec 64) (n : Nat) (hn : n ≤ 7) :
    (addi (andi x 3) n).toNat = (andi x 3).toNat + n := by
  have h := andi3_le x
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  generalize (andi x 3).toNat = a at h ⊢
  have : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n := by omega
  rw [this]
  omega

/-- The named barrier ids `%r565`, `%r566` are below 16 and read as themselves. -/
theorem nb_lt (x : BitVec 64) (n : Nat) (hn : n ≤ 7) :
    (truncBits 32 (addi (andi x 3) n)).toNat < 16 := by
  have h := andi3_le x
  have h2 := nb_val x n hn
  generalize addi (andi x 3) n = y at h2 ⊢
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

theorem nb_trunc (x : BitVec 64) (n : Nat) (hn : n ≤ 7) :
    truncBits 32 (addi (andi x 3) n) = addi (andi x 3) n := by
  have h := andi3_le x
  have h2 := nb_val x n hn
  generalize addi (andi x 3) n = y at h2 ⊢
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

theorem nb0_lt : (truncBits 32 (nb0W L g)).toNat < 16 := nb_lt _ 3 (by omega)
theorem nb1_lt : (truncBits 32 (nb1W L g)).toNat < 16 := nb_lt _ 7 (by omega)
theorem nb0_trunc : truncBits 32 (nb0W L g) = nb0W L g := nb_trunc _ 3 (by omega)
theorem nb1_trunc : truncBits 32 (nb1W L g) = nb1W L g := nb_trunc _ 7 (by omega)

/-- A shared address `sb + k` as the code's `add.s32` computes it (for `simp` with `decide`
discharging the bounds). -/
theorem sb_addi' (hp : Pre p L m) {k : Int} (h0 : 0 ≤ k) (hk : k < 1024) :
    addi (BitVec.ofNat 64 L.sharedBase) k = BitVec.ofNat 64 (L.sharedBase + k.toNat) :=
  Epilogue.sb_addi hp h0 hk

/-- A register's value at an address site, as `loc_off` reads it. -/
macro "corr_val" : tactic => `(tactic| (
  simp only [valueOf, values, valuesStart, valuesRole, valuesTile, valuesRound, valuesRescale,
    valuesFinal, Mma.sbi, Mma.sbW, Mma.w32, lookupLit, Option.getD_some, Option.getD_none]
  try simp (disch := decide) only [sb_addi' ‹Pre _ _ _›]
  try rfl))

set_option hygiene false in
/-- The role's side conditions of `site_shape`: the CTA size, the mbarrier addresses, the Tensor
Memory address registers and the assumptions that select no Tensor Memory site. -/
macro "corr_addr" : tactic => `(tactic| first
  | (rw [‹Pre _ _ _›.block]; done)
  | (rw [‹Pre _ _ _›.block]; decide)
  | (rw [hat.1]; ld_wait)
  | (rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
  | exact hat.2.1
  | (refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; corr_val)
  | with_reducible exact truncBits_lt _
  | with_reducible exact ori_lt _ _
  | with_reducible exact nb0_lt
  | with_reducible exact nb1_lt
  | (try simp only [bl, arrOff, pollOff]
     refine' Epilogue.loc_off ‹Pre _ _ _› (by decide) ?hk ?h8 ?hr
     case hr => exact (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by corr_val)
     case hk => omega
     case h8 => have := ‹Pre _ _ _›.shared; omega)
  | (try simp only [bl, arrOff, pollOff]
     refine Epilogue.loc_off (k := 0) ‹Pre _ _ _› (by decide) ?hk ?h8 ?hr
     case hr => exact (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by corr_val)
     case hk => omega
     case h8 => have := ‹Pre _ _ _›.shared; omega))

set_option hygiene false in
/-- The Tensor Memory instructions and the vector stores, through `site_shape`'s hook. -/
scoped macro_rules
  | `(tactic| shape_inv $hf) => `(tactic| first
      | refine PTX.Flow.shape_store rfl $hf ?_ ?_
      | refine PTX.Flow.shape_tcWaitLd $hf ?_ ?_
      | refine PTX.Flow.shape_tcWaitSt $hf ?_ ?_
      | refine' PTX.Flow.shape_tcSt $hf
          (by refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; corr_val)
          (by first | with_reducible exact truncBits_lt _ | with_reducible exact ori_lt _ _)
          (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl) ?_ ?_
      | refine PTX.Flow.shape_tcLd $hf (by intro s hs; cases hs)
          (by rw [hat.1]; ld_wait) ?_ ?_
      | refine' PTX.Flow.shape_tcLdLoad $hf (by intro s hs; cases hs)
          (by rw [hat.1]; ld_wait)
          (hat.2.1.trans rfl)
          (by refine (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans ?_; corr_val)
          (by first | with_reducible exact truncBits_lt _ | with_reducible exact ori_lt _ _) ?_ ?_
      | refine PTX.Flow.shape_tcLdWait $hf
          (by rw [hat.1]; ld_wait)
          (by rw [hat.2.1]; exact Nat.succ_ne_zero 0) ?_ ?_)

/-- A shape alternative that `simp` reduced to `True`. -/
scoped macro_rules | `(tactic| shape_close) => `(tactic| trivial)

/-- A shared-memory load (a statistics word), without its address: a read, or undefined
behaviour (an override of `site_shape`). -/
syntax "corr_shld" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_shld) => `(tactic| (
      intro t ins e o hat hi hc hf
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine PTX.Flow.shape_ldAny hf rfl rfl rfl ?_ ?_
      all_goals (intros; site_clear; simp only [Ev, rdOrUb]; shape_close)))

/-- A store element, without its address or value: a write, or undefined behaviour (an override
of `site_shape`, whose store lemmas need the element's source operand, which the sub-step `k`
selects). -/
syntax "corr_sst" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_sst) => `(tactic| (
      intro t ins e o hat hi hc hf
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine PTX.Flow.shape_store hf rfl ?_ ?_
      all_goals (intros; simp [Ev])))

/-- The shape obligations of the sites of `s` that the theorem's `hs` admits. -/
syntax "corr_shape" (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_shape $[except [$ovs,*]]?) => `(tactic|
  site_shape s $[except [$ovs,*]]? skip_by (simp at hs)
    unfolding [Ev, nb0_trunc, nb1_trunc, arrOff, pollOff, pollPar, nbW, barK, Site.toE, bl, rdOrUb,
      votePredR, Epilogue.Ev, Epilogue.partialAt]
    reg_vals [valueOf, values, valuesStart, valuesRole, valuesScan, valuesSelect, valuesSelect2,
      valuesTile, valuesRound, valuesRescale, valuesFinal, fAddrs, valuesLse, Epilogue.partials,
      loopRegsR, Epilogue.lanePreds, lookupLit]
    addr_by (corr_addr))

/-- The shape obligation of one concrete site (`site_shape`'s step, without its enumeration of
every site: a group file substitutes its sites from its membership hypothesis first). -/
syntax "corr_step" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_step) => `(tactic|
  site_shape_step
    unfolding [Ev, nb0_trunc, nb1_trunc, arrOff, pollOff, pollPar, nbW, barK, Site.toE, bl, rdOrUb,
      votePredR, Epilogue.Ev, Epilogue.partialAt]
    reg_vals [valueOf, values, valuesStart, valuesRole, valuesScan, valuesSelect, valuesSelect2,
      valuesTile, valuesRound, valuesRescale, valuesFinal, fAddrs, valuesLse, Epilogue.partials,
      loopRegsR, Epilogue.lanePreds, lookupLit]
    addr_by (corr_addr))

/-- A state whose sub-step is not one its site has: its shape obligation holds vacuously. -/
theorem shapeAt_junk {d : D} (h : ¬ (d.k = 0 ∨ d.site.midOk d.k)) :
    (code p L g).ShapeAt (Ev p L g) d :=
  fun _ hi => absurd hi h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
