-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Close
public import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Lemmas.Flow.MemAl
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Prologue.Input
import Kernels.InklingRelDecode.Flow.Code.Part000
import Kernels.InklingRelDecode.Flow.Code.Part001
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Kernels.InklingRelDecode.Flow.Code.Part005
import Kernels.InklingRelDecode.Flow.Code.Part006

@[expose] public section

/-! # The global loads of the prologue are not undefined behaviour

The three request-word loads, the six block-table loads and the 64 query loads read a launch
pointer plus multiples of the access size (4 for words, 2 for the 16-bit halves), for any value
of the other operands: the address register is the launch's exact value (`valueOf`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- **A weak global load of an exactly known, aligned address is not undefined behaviour.** -/
theorem gload_u64 {A : List Assumption} {t : TState} {a : MemAccess} {base n : Nat}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .global)
    (hb : a.addr.base = .reg base 64) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = false) (hoff : a.addr.off = 0) (hw : a.elem.width / 8 ≠ 0)
    (hr : t.regs base = some (u64 n)) (hal : n % (a.elem.width / 8 * a.regs.length) = 0)
    (hd : (a.elem.width / 8 * a.regs.length) ∣ 2 ^ 64) (f : Fault) :
    eventTmpl A L g t (.mem a) ≠ .ub f := by
  refine Flow.ldGlobal_ok' hrule hs hb hk hsem hnc hw (x := BitVec.ofNat 64 (n % 2 ^ 64)) hr ?_ f
  have h1 : (n % 2 ^ 64) % (a.elem.width / 8 * a.regs.length) = 0 := by
    rw [Nat.mod_mod_of_dvd _ hd]; exact hal
  rw [hoff]
  simpa [truncBits] using h1

/-- The register the state's control table holds. -/
theorem reg_ctl {d : Data.D} {t : TState} (hat : (Data.code Q L g w).AtD d t) {r : Nat}
    (hr : r ∈ ctlLive d.c.site.pc) : t.regs r = some (valueOf Q L g w d.c r) := by
  obtain ⟨-, -, -, -, regs⟩ := hat
  have h : Holds t.regs (facts Q L g w d.c d.c.site.pc ++ Data.dF Q L g d) := regs
  exact holds_mem ((holds_append _ _ _).mp h).1 (mem_factsFrom hr)

theorem ld_live : ∀ i : Fin 3, 2055 + i.val ∈ ctlLive (Site.ld i).pc := by decide +kernel

/-- **A request-word load is not undefined behaviour.** -/
theorem safe_ld {m} (hp : Pre Q L m) (hg : g < L.threads) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {i : Fin 3} (hs : d.c.site = .ld i)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hr : (L.ctaidOf (g / L.block)).get .z < Q.b := (Lib.coordinate_bounds hp hg).2.2
  have hb := hp.bRange
  have reg := reg_ctl hat (r := 2055 + i.val) (by rw [hs]; exact ld_live i)
  rw [hs] at hc
  have c4 := hp.cuAlign
  have s4 := hp.seqAlign
  fin_cases i
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_34)
    change t.regs 2055 = some (u64 _) at reg
    refine gload_u64 rfl rfl rfl rfl rfl rfl rfl (by decide) reg ?_ (by decide) f
    change (_ : Nat) % 4 = 0; omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_37)
    change t.regs 2056 = some (u64 _) at reg
    refine gload_u64 rfl rfl rfl rfl rfl rfl rfl (by decide) reg ?_ (by decide) f
    change (_ : Nat) % 4 = 0; omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_41)
    change t.regs 2057 = some (u64 _) at reg
    refine gload_u64 rfl rfl rfl rfl rfl rfl rfl (by decide) reg ?_ (by decide) f
    change (_ : Nat) % 4 = 0; omega

/-- The code at `pc` is a plain global load into one register. -/
def gloadOne (pc base w : Nat) : Bool :=
  Lib.globalLoad pc base w && match kernel.code[pc]? with
    | some ⟨_, .mem a⟩ => a.regs.length == 1
    | _ => false

/-- **A plain global load into one register of an aligned address is not undefined behaviour.** -/
theorem safe_gload {pc base w n : Nat} {t : TState} {ins : Instr}
    (hc : kernel.code[pc]? = some ins) (h : gloadOne pc base w = true)
    (hr : t.regs base = some (u64 n)) (hw : w / 8 ≠ 0) (hal : n % (w / 8) = 0)
    (hd : w / 8 ∣ 2 ^ 64) (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  simp only [gloadOne, Bool.and_eq_true] at h
  obtain ⟨hg, h1⟩ := h
  obtain ⟨a, hop, hr', hl, hb, hk, hs, hnc, hoff, hwd⟩ := Lib.global_load_at hc hg
  rw [hc] at h1
  obtain ⟨gd, op⟩ := ins
  change op = .mem a at hop
  subst hop
  have hlen : a.regs.length = 1 := by simpa using h1
  refine gload_u64 hr' hl hb hk hs hnc hoff (by rw [hwd]; exact hw) hr ?_ ?_ f
  · rw [hwd, hlen, Nat.mul_one]; exact hal
  · rw [hwd, hlen, Nat.mul_one]; exact hd

theorem lb_load : ∀ (b : Fin 3) (h : Fin 2),
    gloadOne (Site.lb b h).pc (2071 + 2 * b.val + h.val) 32 = true := by decide +kernel

theorem ldq_load : ∀ j : Fin 64, gloadOne (Site.ldq j).pc (2077 + j.val) 16 = true := by
  decide +kernel

theorem lb_live : ∀ (b : Fin 3) (h : Fin 2),
    2071 + 2 * b.val + h.val ∈ ctlLive (Site.lb b h).pc := by decide +kernel

theorem ldq_live : ∀ j : Fin 64, 2077 + j.val ∈ ctlLive (Site.ldq j).pc := by decide +kernel

/-- **A block-table load is not undefined behaviour.** -/
theorem safe_lb {m} (hp : Pre Q L m) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {b : Fin 3} {h : Fin 2} (hs : d.c.site = .lb b h)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have reg := reg_ctl hat (r := 2071 + 2 * b.val + h.val) (by rw [hs]; exact lb_live b h)
  have val : valueOf Q L g w d.c (2071 + 2 * b.val + h.val) = u64 (blockPtr Q
      ((L.ctaidOf (g / L.block)).get .z % 2 ^ 32) ((L.ctaidOf (g / L.block)).get .x) b.val
      h.val) := by
    fin_cases b <;> fin_cases h <;>
      (rw [valueOf_query (by decide) (by decide)]; rfl)
  rw [val] at reg
  rw [hs] at hc
  have hb4 := hp.btAlign
  refine safe_gload hc (lb_load b h) reg (by decide) ?_ (by decide) f
  unfold blockPtr btRow
  omega

/-- **A query load is not undefined behaviour.** -/
theorem safe_ldq {m} (hp : Pre Q L m) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {j : Fin 64} (hs : d.c.site = .ldq j)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have reg := reg_ctl hat (r := 2077 + j.val) (by rw [hs]; exact ldq_live j)
  have kind : copyReg (2077 + j.val) = false ∧ queryReg (2077 + j.val) = true :=
    (by decide +kernel : ∀ j : Fin 64, copyReg (2077 + j.val) = false ∧
      queryReg (2077 + j.val) = true) j
  have val : valueOf Q L g w d.c (2077 + j.val) = u64 (qLane Q d.c.first (g % L.block)
      ((L.ctaidOf (g / L.block)).get .y) (j.val / 16) (j.val % 16)) := by
    rw [valueOf_query kind.1 kind.2]
    have := j.isLt
    rw [queryValue_lane (by omega) (by omega), Nat.add_sub_cancel_left]
  rw [val] at reg
  rw [hs] at hc
  have hq2 := hp.qAlign
  refine safe_gload hc (ldq_load j) reg (by decide) ?_ (by decide) f
  unfold qLane queryPointer queryOrigin qOff
  omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
