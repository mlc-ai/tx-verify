-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
public import Lemmas.Flow.RegBits
import Kernels.InklingRelDecode.Proof.Dispatch.RoleByte
import Kernels.InklingRelDecode.Gen.StepDispatch
import Lemmas.Flow.NoUbSites
import Lemmas.Flow.UbStop
import Lemmas.Flow.Step.LoadVec
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.LoadShared
import Lemmas.Flow.Final

@[expose] public section

/-! # The sites of dispatch are not undefined behaviour

At a state that holds its site's facts the template of each of the fourteen sites is not
undefined behaviour (`safe_site`), and the machine stops only on the exit (`live_site`): the byte
read at 2340 is the warp's byte of a published role word, which decodes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

private def roleLoad : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 8,
    ext := .zero 32, addr := ⟨.reg 536 32, 213332⟩, dsts := [some 535] }

private theorem role_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {v : Nat}
    (reg : t.regs 536 = some (b32 v)) (small : v + 213332 < 2 ^ 32) (sub : t.sub = 0)
    (f : Fault) : eventTmpl A L g t (.mem roleLoad) ≠ .ub f := by
  have rule : roleLoad.rule = some .threadAccess := rfl
  have space : roleLoad.locSpace? = none := rfl
  have bits := readBits_b32 (L := L) (g := g) reg (show v < 2 ^ 32 by omega)
  have wrap : wrapAddr 32 (BitVec.ofNat 64 v) 213332 = v + 213332 := by
    simp only [wrapAddr, BitVec.ofInt_ofNat, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
    omega
  have bound : v % 2 ^ 64 < 2 ^ 32 := by omega
  simp only [eventTmpl, memTmpl, rule, space, accessTmpl]
  rw [accessAcc_of_weak (a := roleLoad) rfl]
  simp only [roleLoad, accessLoc, readReg, reg, b32, bits, bind, Except.bind, pure, Except.pure,
    BitVec.toNat_ofNat, bound, wrap, elemAcc, sub, Loc.at, DType.width]
  simp only [↓reduceIte, show (false || ({ } : CacheHints).globalOnly || 1 == 8 ||
    1 == 4 && 8 == 64) = false by decide, Bool.false_and, Bool.false_eq_true]
  have ok : ¬(8 / 8 = 0 ∨ (v + 213332) % (8 / 8 * 1) ≠ 0) := by omega
  simp only [ok, ↓reduceIte]
  intro h; cases h

variable {L : Launch} {g first w : Nat} {regs : Nat → Value} {x : BitVec 64}

private theorem reg_at {d : D} {t : TState} (hat : (code L g regs x first).AtD d t) {r : Nat}
    (hr : r ∈ Flow.live d.site.pc) : t.regs r = some (valueOf L g x regs r) := by
  obtain ⟨-, -, -, -, hF⟩ := hat; exact holds_mem hF (Flow.mem_factsFrom hr)

/-- **The template of a site of dispatch is not undefined behaviour**, at a state that holds its
facts, for the warp index `x` of a worker warp and the recorded allocation word's register. -/
theorem safe_site (hb : L.block % 32 = 0) (hr : L.sharedBase + 213340 ≤ 2 ^ 18)
    (hx : x.toNat < 8) (w : ∃ y, (regs 463).regBits = some y) {d : D} {t : TState} {ins : Instr}
    (hat : (code L g regs x first).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨s, rd⟩ := d
  have hsub : t.sub = 0 := hat.2.1
  cases s
  case head =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2337)
    exact plainOk_tmpl hb (by decide) f
  case idleInc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2336)
    exact plainOk_tmpl hb (by decide) f
  case loaderEntry =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2344)
    exact plainOk_tmpl hb (by decide) f
  case mmaEntry =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2422)
    exact plainOk_tmpl hb (by decide) f
  case idleDec =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2333)
    exact plainOk_tmpl hb (by decide) f
  case sync =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2338)
    exact barSync_imm_ok (by decide) f
  case idleSync =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2334)
    exact barSync_imm_ok (by decide) f
  case idleSyncAgain =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2335)
    exact barSync_imm_ok (by decide) f
  case badSync =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2557)
    exact barSync_imm_ok (by decide) f
  case badSyncAgain =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2558)
    exact barSync_imm_ok (by decide) f
  case exitSync =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2853)
    exact barSync_imm_ok (by decide) f
  case ret =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2855)
    exact plainOk_tmpl hb (by decide) f
  case exitDealloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2854)
    obtain ⟨y, hy⟩ := w
    have h := reg_at hat (r := 463) (by show 463 ∈ Flow.live 2854; decide)
    exact tcDealloc_imm_ok hb h hy f
  case read =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2340)
    have h := reg_at hat (r := 536) (by show 536 ∈ Flow.live 2340; decide)
    have hv : valueOf L g x regs 536 = b32 (L.sharedBase + x.toNat) := by
      simp only [valueOf, b32, Nat.add_zero]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
      have := x.isLt
      omega
    rw [hv] at h
    exact role_ok h (by omega) hsub f

/-- **Dispatch stops only on the exit**: the byte read is the warp's byte of a published word,
which decodes, and the return fires the exit. -/
theorem live_site {d : D} {t : TState} {ins : Instr} {o : Option TState} {v : Event}
    (low : 4 ≤ w) (high : w < 8) (initial : Bool) (hu : ∀ f, v.kind ≠ .ub f)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hfi : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (words : d.site = .read → ∀ ac bs, v.kind = .rd ac bs →
      bs = [(b32 (if initial then 16777730 else 50529027)).toBytes[w - 4]?])
    (hn : next L g d v = none) : v.kind = .exit := by
  obtain ⟨s, rd⟩ := d
  cases s
  case read =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2340)
    have h := role_target ⟨w - 4, by omega⟩ initial
    refine absurd hn (shape_cont (P := fun e => (∀ f, e.kind ≠ .ub f) →
      (∀ ac bs, e.kind = .rd ac bs →
        bs = [(b32 (if initial then 16777730 else 50529027)).toBytes[w - 4]?]) →
      next L g ⟨.read, rd⟩ e ≠ none) hfi ⟨nofun, nofun⟩ ?_ (fun f hu' => absurd rfl (hu' f))
      hu (words rfl))
    intro u hf hu' words'
    obtain ⟨a, bs, rfl, -⟩ := Code.fires_accessLoad (by rfl) (by rfl) (by rfl) hf
    simp only [next, words' a bs rfl, h, Option.map_some]
    nofun
  case ret =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2855)
    simp only [eventTmpl, Fires] at hfi
    rw [hfi.1]
  all_goals simp [next] at hn

end
end PTX.Kernels.InklingRelDecode.Proof.Dispatch
