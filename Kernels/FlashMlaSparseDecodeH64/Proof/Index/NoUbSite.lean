-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictQt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.NcRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Addr
public import Lemmas.Flow.UbFreeIx
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Mod8

@[expose] public section

/-! # The index warp's states fire no undefined behaviour

-- domain: consistent

One declaration per site family, from the register facts of the site (`AtD`), the tags of the data
registers (`QT ixQt`) and the alignment of the addresses the machine's counters give: the event
is no fault, and a store writes the bytes of a 32-bit value (the coordinates) or an 8-bit one (the
validity byte). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **What a store of the index warp writes**: the bytes of a 32-bit value (a coordinate) or of an
8-bit one (the validity byte). -/
def Bits (d : D) (e : Event) : Prop :=
  match d.site with
  | .stA | .stB => ∃ a z, e.kind = .wr a (Value.bits 32 z).toBytes
  | .bA | .bB => ∃ a z, e.kind = .wr a (Value.bits 8 z).toBytes
  | _ => True

/-- The obligation of a site's state: the event is no fault and its stores write the bytes of
their values. -/
def NoUbQ (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  ∀ (t : TState) (ins : Instr) (e : Event) (o : Option TState), (code P L g).AtD d t →
    (code P L g).inv d → kernel.code[(code P L g).pc d]? = some ins → QT ixQt t →
    Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
    (∀ f, e.kind ≠ .ub f) ∧ Bits d e

set_option hygiene false in
/-- Open the obligation of the state `d` at the site `hs` names. -/
macro "ixn_open" : tactic => `(tactic| (
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  intro t ins e o hat hi hc hq hf
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  dsimp only [Flow.Code.AtD, code, IxSite.pc] at hpc hsub hc hF hf hi ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  dsimp only [Bits]))

set_option hygiene false in
/-- A register's fact at an opened site. -/
macro "rgq " r:num : term => `(regs_of_factsFrom hF (r := $r) (by decide +kernel))

/-- **A butterfly shuffle is no fault.** -/
theorem noUbq_shfl (hp : Pre P L m) (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .sA1 ∨ s = .sA2 ∨ s = .sB1 ∨ s = .sB2) : NoUbQ P L g d := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  rcases hn with rfl | rfl | rfl | rfl <;> ixn_open
  · obtain ⟨y, hy⟩ : ∃ y, t.regs 606 = some (.bits 32 y) := ⟨_, rgq 606⟩
    obtain ⟨bv, cv, recv, ok, rfl⟩ := fires_shflBfly_ok hy hb hf
    exact ⟨fun f h => (by cases h), trivial⟩
  · obtain ⟨y, hy⟩ : ∃ y, t.regs 609 = some (.bits 32 y) := ⟨_, rgq 609⟩
    obtain ⟨bv, cv, recv, ok, rfl⟩ := fires_shflBfly_ok hy hb hf
    exact ⟨fun f h => (by cases h), trivial⟩
  · obtain ⟨y, hy⟩ : ∃ y, t.regs 645 = some (.bits 32 y) := ⟨_, rgq 645⟩
    obtain ⟨bv, cv, recv, ok, rfl⟩ := fires_shflBfly_ok hy hb hf
    exact ⟨fun f h => (by cases h), trivial⟩
  · obtain ⟨y, hy⟩ : ∃ y, t.regs 648 = some (.bits 32 y) := ⟨_, rgq 648⟩
    obtain ⟨bv, cv, recv, ok, rfl⟩ := fires_shflBfly_ok hy hb hf
    exact ⟨fun f h => (by cases h), trivial⟩

/-- The address a pair load reads at. -/
def ldAddr (P : Params) (L : Launch) (g : Nat) (d : D) : BitVec 64 :=
  match d.site with
  | .pre => ixAddr0 P L g
  | .pf => d.c.aptr
  | .xpre => ixAddr1 P L g
  | _ => ixXad P L g d.c.xa

/-- **A pair load at an 8-aligned address is no fault.** -/
theorem noUbq_pairLd (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .pre ∨ s = .pf ∨ s = .xpre ∨ s = .xpf)
    (hal : (truncBits 64 (ldAddr P L g d) + BitVec.ofInt 64 0).toNat % 8 = 0) :
    NoUbQ P L g d := by
  have hA : ∀ pc, (pc = 2403 ∨ pc = 2429 ∨ pc = 2501 ∨ pc = 2517) →
      Assumptions.all.any (·.ncLoads pc) = true := by
    intro pc h; rcases h with rfl | rfl | rfl | rfl <;> decide
  rcases hn with rfl | rfl | rfl | rfl <;> ixn_open <;> dsimp only [ldAddr] at hal
  · change Fires _ (loadTmpl Assumptions.all L g t .global true 32 [2974, 2973] 3033 0) e o at hf
    obtain ⟨a, ha⟩ := ncLoad2_eq (ds := [2974, 2973]) rfl (rgq 3033) hal
      (by rw [hpc]; exact hA _ (by simp))
    rw [ha] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact ⟨fun f h => (by rw [he] at h; cases h), trivial⟩
  · change Fires _ (loadTmpl Assumptions.all L g t .global true 32 [2976, 2975] 4029 0) e o at hf
    obtain ⟨a, ha⟩ := ncLoad2_eq (ds := [2976, 2975]) rfl (rgq 4029) hal
      (by rw [hpc]; exact hA _ (by simp))
    rw [ha] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact ⟨fun f h => (by rw [he] at h; cases h), trivial⟩
  · change Fires _ (loadTmpl Assumptions.all L g t .global true 32 [2982, 2981] 3041 0) e o at hf
    obtain ⟨a, ha⟩ := ncLoad2_eq (ds := [2982, 2981]) rfl (rgq 3041) hal
      (by rw [hpc]; exact hA _ (by simp))
    rw [ha] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact ⟨fun f h => (by rw [he] at h; cases h), trivial⟩
  · change Fires _ (loadTmpl Assumptions.all L g t .global true 32 [2984, 2983] 3043 0) e o at hf
    obtain ⟨a, ha⟩ := ncLoad2_eq (ds := [2984, 2983]) rfl (rgq 3043) hal
      (by rw [hpc]; exact hA _ (by simp))
    rw [ha] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact ⟨fun f h => (by rw [he] at h; cases h), trivial⟩

/-- The slot's `valid_coord_free` word is 8-byte aligned. -/
theorem free_m8 (hp : Pre P L m) (c : IxCtl) :
    (truncBits 32 (truncBits 32 (freeW L c) + BitVec.ofInt 64 0)).toNat % 8 = 0 :=
  trunc_add_mod8 (m8_addi (m8_add32 (m8_sbw hp) (m8_shl3 _)) (by decide)) (by decide)

/-- The coordinate pair's store address is 8-byte aligned. -/
theorem pair_m8 (hp : Pre P L m) (c : IxCtl) :
    (truncBits 32 (truncBits 32 (pairW L g c) + BitVec.ofInt 64 221728)).toNat % 8 = 0 := by
  have h := congrArg Loc.addr (pair_loc (g := g) hp c)
  have hs := hp.sharedAlignment
  have hl := hp.sharedBase
  simp only [smLoc, wsLoc] at h
  rw [h, hl]
  omega

/-- **A poll of a slot's `valid_coord_free` word is no fault.** -/
theorem noUbq_wait (hp : Pre P L m) (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .wA ∨ s = .wB) : NoUbQ P L g d := by
  rcases hn with rfl | rfl <;> ixn_open
  · rcases fires_wait_reg_al (by rw [hpc]; decide) (rgq 585) (rgq 586) hf with ⟨ok, hk⟩ | ⟨f, -, hn⟩
    · exact ⟨fun f h => (by rw [hk] at h; cases h), trivial⟩
    · exact absurd (free_m8 hp c) hn
  · rcases fires_wait_reg_al (by rw [hpc]; decide) (rgq 623) (rgq 624) hf with ⟨ok, hk⟩ | ⟨f, -, hn⟩
    · exact ⟨fun f h => (by rw [hk] at h; cases h), trivial⟩
    · exact absurd (free_m8 hp c) hn

/-- **A coordinate pair's store writes the bytes of its two 32-bit words.** -/
theorem noUbq_pair (hp : Pre P L m) (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .stA ∨ s = .stB) : NoUbQ P L g d := by
  rcases hn with rfl | rfl <;> ixn_open
  · obtain ⟨y0, h0⟩ := (show ∃ y, t.regs 600 = some (.bits 32 y) from ⟨_, rgq 600⟩)
    obtain ⟨y1, h1⟩ := (show ∃ y, t.regs 604 = some (.bits 32 y) from ⟨_, rgq 604⟩)
    change Fires _ (storeTmpl L g t .shared 32 612 221728 [.reg 600, .reg 604]) e o at hf
    have hs2 : t.sub < 2 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stPair_eq (rgq 612) h0 h1 hs2 (pair_m8 (g := g) hp c)
    rw [ha] at hf
    simp only [Fires] at hf
    exact ⟨fun f h => (by rw [hf.1] at h; cases h), a, _, congrArg Event.kind hf.1⟩
  · obtain ⟨y0, h0⟩ := (show ∃ y, t.regs 638 = some (.bits 32 y) from ⟨_, rgq 638⟩)
    obtain ⟨y1, h1⟩ := (show ∃ y, t.regs 643 = some (.bits 32 y) from ⟨_, rgq 643⟩)
    change Fires _ (storeTmpl L g t .shared 32 651 221728 [.reg 638, .reg 643]) e o at hf
    have hs2 : t.sub < 2 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stPair_eq (rgq 651) h0 h1 hs2 (pair_m8 (g := g) hp c)
    rw [ha] at hf
    simp only [Fires] at hf
    exact ⟨fun f h => (by rw [hf.1] at h; cases h), a, _, congrArg Event.kind hf.1⟩

/-- **The validity byte's store writes the low byte of its word.** -/
theorem noUbq_byte (d : D) {s : IxSite} (hs : d.site = s) (hn : s = .bA ∨ s = .bB) :
    NoUbQ P L g d := by
  rcases hn with rfl | rfl <;> ixn_open
  · obtain ⟨y, hy⟩ : ∃ y, t.regs 508 = some (.bits 32 y) := ⟨_, rgq 508⟩
    change Fires _ (storeTmpl L g t .shared 8 613 221696 [.reg 508]) e o at hf
    have hs0 : t.sub = 0 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stByte_eq (rgq 613) hy hs0
    rw [ha] at hf
    simp only [Fires] at hf
    exact ⟨fun f h => (by rw [hf.1] at h; cases h), a, _, congrArg Event.kind hf.1⟩
  · obtain ⟨y, hy⟩ : ∃ y, t.regs 511 = some (.bits 32 y) := ⟨_, rgq 511⟩
    change Fires _ (storeTmpl L g t .shared 8 652 221696 [.reg 511]) e o at hf
    have hs0 : t.sub = 0 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stByte_eq (rgq 652) hy hs0
    rw [ha] at hf
    simp only [Fires] at hf
    exact ⟨fun f h => (by rw [hf.1] at h; cases h), a, _, congrArg Event.kind hf.1⟩

/-- **A length load reads its row's word.** -/
theorem noUbq_len (hp : Pre P L m) (d : D)
    (hA : d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false)
    (hB : d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false)
    (hn : d.site = .lenA ∨ d.site = .lenB) : NoUbQ P L g d := by
  intro t ins e o hat hi hc _ hf
  rcases hn with hs | hs
  · obtain ⟨x, hx⟩ := len_ptr (hA hs)
    obtain ⟨bs, hr⟩ := topk_read hp hx hs hat hi hc hf
    exact ⟨fun f h => (by rw [hr.1] at h; cases h), by simp [Bits, hs]⟩
  · obtain ⟨x, hx⟩ := len_ptr (hB hs)
    obtain ⟨bs, hr⟩ := extra_read hp hx hs hat hi hc hf
    exact ⟨fun f h => (by rw [hr.1] at h; cases h), by simp [Bits, hs]⟩

/-- **The sites with an exact event** (arrival, barrier, exit) fire no fault. -/
theorem noUbq_exact (hp : Pre P L m) (d : D)
    (hn : d.site = .arrA ∨ d.site = .arrB ∨ d.site = .bar ∨ d.site = .exit) :
    NoUbQ P L g d := by
  intro t ins e o hat hi hc _ hf
  have hK := shapeK hp hat hi hc hf
  refine ⟨fun f h => ?_, by rcases hn with h | h | h | h <;> simp [Bits, h]⟩
  rcases hn with h' | h' | h' | h' <;> simp only [EvK, h'] at hK <;> rw [hK] at h <;> cases h

/-- **The index warp's states fire no undefined behaviour**, given the lengths' pointers and the
pair loads' alignment. -/
theorem noUbq_site (hp : Pre P L m) (d : D)
    (hA : d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false)
    (hB : d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false)
    (hal : isLd d.site = true →
      (truncBits 64 (ldAddr P L g d) + BitVec.ofInt 64 0).toNat % 8 = 0) :
    NoUbQ P L g d := by
  have hl : ∀ s, d.site = s → isLd s = true → (truncBits 64 (ldAddr P L g d) +
      BitVec.ofInt 64 0).toNat % 8 = 0 := fun s hs h => hal (by rw [hs]; exact h)
  cases hs : d.site with
  | lenA => exact noUbq_len hp d hA hB (.inl hs)
  | lenB => exact noUbq_len hp d hA hB (.inr hs)
  | pre => exact noUbq_pairLd d hs (.inl rfl) (hl _ hs rfl)
  | pf => exact noUbq_pairLd d hs (.inr (.inl rfl)) (hl _ hs rfl)
  | xpre => exact noUbq_pairLd d hs (.inr (.inr (.inl rfl))) (hl _ hs rfl)
  | xpf => exact noUbq_pairLd d hs (.inr (.inr (.inr rfl))) (hl _ hs rfl)
  | wA => exact noUbq_wait hp d hs (.inl rfl)
  | wB => exact noUbq_wait hp d hs (.inr rfl)
  | sA1 => exact noUbq_shfl hp d hs (.inl rfl)
  | sA2 => exact noUbq_shfl hp d hs (.inr (.inl rfl))
  | sB1 => exact noUbq_shfl hp d hs (.inr (.inr (.inl rfl)))
  | sB2 => exact noUbq_shfl hp d hs (.inr (.inr (.inr rfl)))
  | stA => exact noUbq_pair hp d hs (.inl rfl)
  | stB => exact noUbq_pair hp d hs (.inr rfl)
  | bA => exact noUbq_byte d hs (.inl rfl)
  | bB => exact noUbq_byte d hs (.inr rfl)
  | arrA => exact noUbq_exact hp d (.inl hs)
  | arrB => exact noUbq_exact hp d (.inr (.inl hs))
  | bar => exact noUbq_exact hp d (.inr (.inr (.inl hs)))
  | exit => exact noUbq_exact hp d (.inr (.inr (.inr hs)))

set_option linter.unusedSimpArgs false in
/-- **The machine stops only at the exit**: an event of the site's shape that is no fault and
whose loaded words are 32-bit has a successor, unless it is the exit. -/
theorem succ_exit (d : D) {e : Event} (hK : EvK P L g d e) (hnu : ∀ f, e.kind ≠ .ub f)
    (hw : ∀ a bs, e.kind = .nc a bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y))
    (hs : succ P L g d e = none) : e.kind = .exit := by
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hnu hw ⊢
  cases site <;> simp only [EvK, NcEv, NcAt, PollEv, ShflEv, StoreEv] at hK <;>
    simp only [succ] at hs
  all_goals
    cases kd with
    | nc a bs =>
      obtain ⟨y, hy⟩ := hw a bs rfl
      simp_all [lenNext, ncPair, poll, shflNext, Code.ncNext]
    | _ => simp_all [lenNext, ncPair, poll, shflNext, Code.ncNext]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
