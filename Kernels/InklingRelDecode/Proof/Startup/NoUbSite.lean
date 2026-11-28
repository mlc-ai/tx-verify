-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Startup.Shape
public import Kernels.InklingRelDecode.Proof.Startup.Params
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.SharedSymOk
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.NoUbSites

@[expose] public section

/-! # The startup's sites are not undefined behaviour, and the startup dies only on the base word

The template of a site of the startup is not undefined behaviour at a state that holds its facts
(`safe_site`); the startup does not die on an event that is no undefined behaviour, given the base
word's load read the zero word (`live_site`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat}

/-- A register the site's facts name holds the state's value. -/
private theorem reg_at {d : D} {t : TState} (hat : (code Q L g).AtD d t) {r : Nat}
    (hr : r ∈ Flow.live d.site.pc) : t.regs r = some (valueOf Q L g d r) :=
  by obtain ⟨-, -, -, -, hF⟩ := hat; exact holds_mem hF (Flow.mem_factsFrom hr)

private theorem tcAlloc_imm_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {grp : CtaGroup} {base a : Nat} (hb : L.block % 32 = 0)
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (h4 : a % 4 = 0) (f : Fault) :
    eventTmpl A L g t (.tcAlloc grp base 0 (.imm 512)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, readBits, hb, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 512)).toNat = 512 by decide]
  by_cases hs : t.sub = 0 <;> simp [Tmem.validColumns, h4, hs, ofExec]


private theorem base_reg {d : D} {t : TState} (hS : SharedOk L) (hat : (code Q L g).AtD d t)
    (hr : 534 ∈ Flow.live d.site.pc) : t.regs 534 = some (b32 L.sharedBase) := by
  rw [reg_at hat hr]
  have h := hS.2
  simp only [valueOf, values, Startup.table, PTX.Flow.lookupLit, baseW, trunc32, b32,
    Nat.add_zero, Nat.mod_eq_of_lt (show L.sharedBase < 2 ^ 32 by omega)]
  rfl

/-- **The template of a site of the startup is not undefined behaviour**, at a state that holds
its facts. -/
theorem safe_site (hb : L.block % 32 = 0) (hS : SharedOk L) {d : D} {t : TState}
    {ins : Instr}
    (hat : (code Q L g).AtD d t) (hx : ∀ r, d.site ≠ .enter r)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨s, tm, x, bw⟩ := d
  have hsub : t.sub = Site.sub s := hat.2.1
  have al : L.sharedBase % 4 = 0 := by have := hS.1; omega
  have al' : L.sharedBase < 2 ^ 32 := by have := hS.2; omega
  cases s with
  | alloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_11)
    exact tcAlloc_imm_ok hb (base_reg hS hat (by show 534 ∈ Flow.live 11; decide)) al' al f
  | allocWr =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_11)
    exact tcAlloc_imm_ok hb (base_reg hS hat (by show 534 ∈ Flow.live 11; decide)) al' al f
  | bar0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_12)
    exact barSync_imm_ok (by decide) f
  | bar1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_14)
    exact barSync_imm_ok (by decide) f
  | ld0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_13)
    refine ldSharedSym_ok (o := 0) rfl rfl rfl rfl rfl rfl (by decide) rfl (by decide) ?_ f
    have h1 := hS.1
    have h2 := hS.2
    simp only [wrapAddr, truncBits, DType.width]
    simp
    omega
  | relinq =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_15)
    exact plainOk_tmpl hb rfl f
  | shfl =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_17)
    have h464 : t.regs 464 = some (b32 (warpOf L g)) := by
      rw [reg_at hat (by show 464 ∈ Flow.live 17; decide)]; rfl
    exact shfl_imm_ok (d := 465) (p := none) (b := 0) (c := 31) (Or.inr rfl) hb h464 f
  | enter r => exact absurd rfl (hx r)


/-- **The startup does not die on an event that is no undefined behaviour**: the event has its
site's shape, and the base word's load read the zero word. -/
theorem live_site {d : D} {v : Event} (hx : ∀ r, d.site ≠ .enter r) (hev : Ev L g d v)
    (base : d.site = .ld0 → ∀ ac bs, v = ⟨13, .rd ac bs⟩ → ac.loc = ⟨.shared, g / L.block,
      L.sharedBase⟩ → ac.size = 4 → bs = (b32 0).toBytes.map some) :
    succ L g d v ≠ none := by
  obtain ⟨s, tm, x, bw⟩ := d
  cases s with
  | alloc => simp [succ]
  | allocWr => simp [succ]
  | bar0 => simp [succ]
  | bar1 => simp [succ]
  | relinq => simp [succ]
  | ld0 =>
    simp only [Ev] at hev
    obtain ⟨ac, bs, rfl, hl, hsz, -⟩ := hev
    have hb := base rfl ac bs rfl hl hsz
    subst hb
    simp [succ, rebuild_b32]
    cases word32 (b32 0) <;> simp
  | shfl =>
    simp only [Ev] at hev
    obtain ⟨recv, ok, rfl⟩ := hev
    simp only [succ]
    split <;> simp_all
  | enter r => exact absurd rfl (hx r)


end
end PTX.Kernels.InklingRelDecode.Proof.Startup
