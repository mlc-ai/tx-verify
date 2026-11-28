-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.SafeA
public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Store
public import Kernels.InklingRelDecode.Gen.TypedLateQt
import Lemmas.Flow.MemAl

@[expose] public section

/-! # The epilogue's global word stores are not undefined behaviour

Each store writes a 32-bit register through a 64-bit register of the control facts: undefined
behaviour only through a misaligned address or a value of another size. `storeShape` is the scan of
the code (the shape of the access, the address register among the facts, the value register tagged
a word of four bytes); the alignment of the address words follows from the 4-aligned bases. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

/-- The instruction at `pc` is a guarded 32-bit global store through a register of `[lo, hi]`
among the facts of `pc`, of a register tagged as a word of four bytes. -/
noncomputable def storeShape (pc lo hi : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (_, false), .mem a⟩ =>
    a.kind == .store && a.sem == .weak && a.locSpace? == some .global &&
      a.rule == some .threadAccess && a.srcs.length == 1 && a.elem.width == 32 &&
      a.addr.off == 0 &&
      match a.addr.base, a.srcs with
      | .reg b 64, [.reg r] => decide (lo ≤ b) && decide (b ≤ hi) && decide (b ∈ ctlLive pc) &&
        ((lateQt pc).lookup r == some (.old (.bits 32)) || (lateQt pc).lookup r == some .dat32)
      | _, _ => false
  | _ => false

theorem shapes_a : ∀ j : Fin 64, storeShape (storePc j) 2380 2443 = true := by
  decide +kernel

theorem shapes_b : storeShape 2682 2379 2379 = true := by decide +kernel

variable {L : Launch} {g : Nat} {t : TState} {ins : Instr}

/-- **A store of the shape is not undefined behaviour** when the address registers hold aligned
words and the value register has the tag. -/
theorem store_ok_of_shape {pc lo hi : Nat} (hc : kernel.code[pc]? = some ins)
    (h : storeShape pc lo hi = true) (hq : TypedF (lateQt pc) t) (hsub : t.sub = 0)
    (hb : ∀ b, lo ≤ b → b ≤ hi → b ∈ ctlLive pc → ∃ x, t.regs b = some (.bits 64 x) ∧
      x.toNat % 4 = 0) (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  unfold storeShape at h
  rw [hc] at h
  split at h
  · rename_i q a hins
    obtain rfl := Option.some.inj hins
    split at h
    · rename_i _ _ b0 r0 hbase hsrcs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hk, hsem⟩, hs⟩, hrule⟩, hlen⟩, hw⟩, ho⟩, ⟨⟨⟨hlo, hhi⟩, hlive⟩, htag⟩⟩ := h
      obtain ⟨x, hx, hx4⟩ := hb b0 hlo hhi hlive
      have hv : ∃ y, t.regs r0 = some y ∧ y.bytes = 4 := by
        rcases htag with h1 | h1
        · obtain ⟨y, hy⟩ := hq r0 _ h1
          exact ⟨_, hy, rfl⟩
        · obtain ⟨y, hy, hd⟩ := hq r0 _ h1
          exact ⟨y, hy, hd.2.1⟩
      obtain ⟨y, hy, hy4⟩ := hv
      refine stGlobal_ok (a := a) (base := b0) (x := x) (n := 4) hrule hs hbase hk hsem
        (by rw [hw, hlen]) (by norm_num) (by decide) hx hx4 (by rw [ho]; rfl) ⟨r0, y, ?_, hy, ?_⟩ f
      · rw [hsub, hsrcs]
        rfl
      · rw [hw]
        exact hy4
    · simp at h
  · cases h

variable {e : Entry} {d : D}

theorem val_addr (v : Value) {b : Nat} (h1 : 2380 ≤ b) (h2 : b ≤ 2443) :
    valueOf e L g v b = u64 (e.rowAddr (g % L.block) + g % L.block / 16 % 2 * 256 +
      4 * (b - 2380)) := by
  have n1 : b ≠ 1827 := by omega
  have n2 : b ≠ 1828 := by omega
  have n3 : b ≠ 1829 := by omega
  have n4 : b ≠ 1830 := by omega
  simp (disch := omega) [valueOf, scalarValue, h1, h2, n1, n2, n3, n4]

/-- **A word store of the epilogue is not undefined behaviour.** -/
theorem safe_store (j : Fin 64) (ho : e.outBase % 4 = 0) (hat : (code e L g).AtD d t)
    (hq : QTF lateQt t) (hs : d.site = .store j) (hc : kernel.code[d.site.pc]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hpc : t.pc = storePc j := by
    have : t.pc = d.site.pc := hat.1
    rw [hs] at this
    exact this
  have hsub : t.sub = 0 := hat.2.1
  have hT : TypedF (lateQt (storePc j)) t := by
    have := hq
    rwa [QTF, hpc] at this
  rw [hs] at hc
  refine store_ok_of_shape (pc := storePc j) hc (shapes_a j) hT hsub ?_ f
  intro b hlo hhi hlive
  have r := reg_epi hat (r := b) (hs ▸ hlive)
  rw [val_addr d.received hlo hhi] at r
  refine ⟨BitVec.ofNat 64 ((e.rowAddr (g % L.block) + g % L.block / 16 % 2 * 256 +
    4 * (b - 2380)) % 2 ^ 64), r, ?_⟩
  simp only [Entry.rowAddr, BitVec.toNat_ofNat]
  omega

/-- **The guarded store of the LSE word is not undefined behaviour.** -/
theorem safe_lse (ho : e.lseBase % 4 = 0) (hat : (code e L g).AtD d t) (hq : QTF lateQt t)
    (hs : d.site = .lse) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hpc : t.pc = 2682 := by
    have : t.pc = d.site.pc := hat.1
    rw [hs] at this
    exact this
  have hsub : t.sub = 0 := hat.2.1
  have hT : TypedF (lateQt 2682) t := by
    have := hq
    rwa [QTF, hpc] at this
  rw [hs] at hc
  refine store_ok_of_shape (pc := 2682) hc shapes_b hT hsub ?_ f
  intro b hlo hhi hlive
  obtain rfl : b = 2379 := by omega
  have r := reg_epi hat (r := 2379) (hs ▸ hlive)
  have hv : valueOf e L g d.received 2379 = u64 (e.lseBase + sx (e.tile (g % L.block)) * 4) := rfl
  rw [hv] at r
  refine ⟨BitVec.ofNat 64 ((e.lseBase + sx (e.tile (g % L.block)) * 4) % 2 ^ 64), r, ?_⟩
  simp only [BitVec.toNat_ofNat]
  omega

/-- **No site of the epilogue but the exit is undefined behaviour**, at a state that holds the
facts of its table and the tags of the lane, whose received word (at the load) names the warp's
lane group. -/
theorem safe_epi (hl : EpiLaunch L) (hb : e.base = b32 0) (ho : e.outBase % 4 = 0)
    (hlse : e.lseBase % 4 = 0) (hat : (code e L g).AtD d t) (hq : QTF lateQt t)
    (hs : d.site ≠ .exit)
    (hx : d.site = .load → ∃ x, d.received = b32 x ∧ x % 4 = g % L.block / 32 % 4)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hbs : e.base.regBits.isSome := by rw [hb]; rfl
  cases hsite : d.site with
  | wait => exact safe_wait hl hat hsite hc f
  | shfl => exact safe_shfl hl hat hsite hc f
  | load => exact safe_load hl hb hat hsite (hx hsite) hc f
  | waitLd => exact safe_plain hl (Or.inr (Or.inr (Or.inr (Or.inr hsite)))) hc f
  | lse => exact safe_lse hlse hat hq hsite hc f
  | store j => exact safe_store j ho hat hq hsite hc f
  | join => exact safe_plain hl (Or.inl hsite) hc f
  | setMax => exact safe_plain hl (Or.inr (Or.inl hsite)) hc f
  | roleWord => exact safe_roleWord hl hat hsite hc f
  | sync1 => exact safe_plain hl (Or.inr (Or.inr (Or.inl hsite))) hc f
  | sync0 => exact safe_plain hl (Or.inr (Or.inr (Or.inr (Or.inl hsite)))) hc f
  | dealloc => exact safe_dealloc hl hbs hat hsite hc f
  | exit => exact absurd hsite hs

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
