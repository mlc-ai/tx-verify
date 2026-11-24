-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Thread.Sites
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Events
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # The event of each site

At a concrete state of an abstract state, the instruction of its site performs: the 4-byte read
of `A[g]`, the 4-byte write of the input to the thread's shared cell (the source's own bytes, a
wider source truncated to them, and a narrower one a type mismatch: `storeValue`), the CTA
barrier `0` for the whole CTA, the 4-byte read of shared cell `i`, the 4-byte write of the sum
to `B[c]`, and the exit. -/

namespace PTX.Kernels.BlockSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}

/-- The `ld.global.b32 %r8, [%rd21]` of the input site. -/
abbrev ldInput : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
    addr := { base := .reg 21 64 }, dsts := [some 8] }

/-- The `st.shared.b32 [%r11], %r8` of the share site. -/
abbrev stShare : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    addr := { base := .reg 11 32 }, srcs := [.reg 8] }

/-- The `ld.shared.b32 %r12, [%r13]` of the sum site. -/
abbrev ldSum : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    addr := { base := .reg 13 32 }, dsts := [some 12] }

/-- The `st.global.b32 [%rd24], %r15` of the out site. -/
abbrev stOut : MemAccess :=
  { kind := .store, space := some .global, sem := .weak, elem := .int .b 32,
    addr := { base := .reg 24 64 }, srcs := [.reg 15] }

/-- The value of register `r` of a state with the facts of `d` at `pc`, when `r` is live there. -/
theorem reg_of {pc r : Nat} (h : At t pc (factsAt A B L g pc d)) (hr : r ∈ Flow.live pc) :
    t.regs r = some (valueOf A B L g d r) :=
  holds_mem h.2.2.2.2 (mem_factsFrom hr)

theorem tmpl_input (hpre : Pre L A B x mem0) (hg : g < L.threads)
    (h : At t Site.input.pc (factsAt A B L g Site.input.pc d)) :
    eventTmpl Prod L g t (.mem ldInput) =
      .read { loc := gl (A + 4 * g), size := 4 } (afterLoad t [8]) := by
  have hr := hpre.rangeA
  have ha := hpre.alignA
  have hrd : t.regs 21 = some (b64 (A + 4 * g)) := reg_of h (by table_decide)
  show memTmpl Prod L g t ldInput = _
  rw [memTmpl_load rfl rfl rfl rfl (by decide)]
  change loadTmpl Prod L g t .global false 32 [8] 21 0 = _
  rw [loadTmpl_global h.2.1 hrd (by simp only [Launch.threads] at hg hr; omega) (by decide)
    (by omega)]
  rfl

theorem tmpl_share (hpre : Pre L A B x mem0)
    (h : At t Site.share.pc (factsAt A B L g Site.share.pc d)) :
    eventTmpl Prod L g t (.mem stShare) =
      match storeValue 32 d.v with
      | .error f => .ub f
      | .ok v' =>
        .write { loc := sh (g / 256) (L.sharedBase + 4 * (g % 256)), size := 4 } v'.toBytes
          (afterStore t [.reg 8]) := by
  have hs := hpre.sharedRange
  have ha := hpre.sharedAlign
  have hrd : t.regs 11 = some (b32 (L.sharedBase + 4 * (g % 256))) := reg_of h (by table_decide)
  have hv : t.regs 8 = some d.v := reg_of h (by table_decide)
  show memTmpl Prod L g t stShare = _
  rw [memTmpl_store rfl rfl rfl rfl (by decide)]
  change storeTmpl L g t .shared 32 11 0 [.reg 8] = _
  unfold storeTmpl
  rw [effAddr_b32 hrd (by omega)]
  simp only [bind, Except.bind, List.length_singleton, h.2.1]
  rw [elemAcc_ok (by decide) (by simp only; omega)]
  simp only [Loc.at, readValue, readReg, hv, pure, Except.pure, sh, hpre.block,
    List.getElem?_cons_zero]
  cases storeValue 32 d.v <;> rfl

theorem tmpl_bar : eventTmpl Prod L g t (.barSync (.imm 0) true) = .bar 0 (PTX.next t) := rfl

theorem tmpl_sum (hpre : Pre L A B x mem0) (hi : d.i < 256)
    (h : At t Site.sum.pc (factsAt A B L g Site.sum.pc d)) :
    eventTmpl Prod L g t (.mem ldSum) =
      .read { loc := sh (g / 256) (L.sharedBase + 4 * d.i), size := 4 } (afterLoad t [12]) := by
  have hs := hpre.sharedRange
  have ha := hpre.sharedAlign
  have hrd : t.regs 13 = some (b32 (L.sharedBase + 4 * d.i)) := reg_of h (by table_decide)
  show memTmpl Prod L g t ldSum = _
  rw [memTmpl_load rfl rfl rfl rfl (by decide)]
  change loadTmpl Prod L g t .shared false 32 [12] 13 0 = _
  unfold loadTmpl
  rw [effAddr_b32 hrd (by omega)]
  simp only [bind, Except.bind, List.length_singleton, h.2.1]
  rw [elemAcc_ok (by decide) (by simp only; omega)]
  simp [Loc.at, sh, hpre.block]

theorem tmpl_out (hpre : Pre L A B x mem0) (hg : g < L.threads) {s : EReal}
    (hacc : d.acc = Assumption.erealValue .f32 s)
    (h : At t Site.out.pc (factsAt A B L g Site.out.pc d)) :
    eventTmpl Prod L g t (.mem stOut) =
      .write { loc := gl (B + 4 * (g / 256)), size := 4 } (Assumption.erealValue .f32 s).toBytes
        (afterStore t [.reg 15]) := by
  have hrB := hpre.rangeB
  have haB := hpre.alignB
  have hc : g / 256 < L.grid := by
    have := hg; simp only [Launch.threads, hpre.block] at this; omega
  have hrd : t.regs 24 = some (b64 (B + 4 * (g / 256))) := reg_of h (by table_decide)
  have hv : t.regs 15 = some (Assumption.erealValue .f32 s) := by
    rw [← hacc]; exact reg_of h (by table_decide)
  show memTmpl Prod L g t stOut = _
  rw [memTmpl_store rfl rfl rfl rfl (by decide)]
  change storeTmpl L g t .global 32 24 0 [.reg 15] = _
  rw [storeTmpl_global h.2.1 hrd (by omega) (by decide) (by omega) hv,
    storeValue_of_bytes (erealValue_bytes s)]
  rfl

theorem tmpl_exit : eventTmpl Prod L g t .ret = .exit := rfl

end
end PTX.Kernels.BlockSum.Proof
