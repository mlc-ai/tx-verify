-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinCanon
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds

@[expose] public section

/-! # What a state of the chain has loaded

`LdOk d`: the words the data machine's block holds at a site of the chain are loaded (differ from
their defaults) as far as the site has gone: the two score halves from the `sldw`, the mask word
after the validity read, each peer pair after its second element, the exchange word after the
exchange load, the accumulator words after the chunk's load, the row-sum word after the
epilogue's read (`LdOk` of the sites, `ldOk_step`). The step needs the typing of the event's word
(`W0EvPayload`) and its kind. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem rec_lo (c : Control.D) (ev : Event) (b : Blk) :
    (record c ev b).lo = b.lo ∨ ∃ x vals sh, ev.kind = .tc (.ld x vals sh) ∧
      (record c ev b).lo = vals ∧ (c.site = .sld false 1 ∨ c.site = .sld true 0) := by
  unfold record
  split <;> first
    | (rename_i a k x vals sh hs hk
       by_cases h : sldLo a k = true
       · right
         refine ⟨x, vals, sh, hk, by simp [h], ?_⟩
         rw [hs]
         revert h
         cases a <;> fin_cases k <;> simp [sldLo]
       · left; simp [h])
    | (left; rfl)
    | (left; split <;> rfl)

theorem rec_hi (c : Control.D) (ev : Event) (b : Blk) :
    (record c ev b).hi = b.hi ∨ ∃ x vals sh, ev.kind = .tc (.ld x vals sh) ∧
      (record c ev b).hi = vals ∧ (c.site = .sld false 0 ∨ c.site = .sld true 1) := by
  unfold record
  split <;> first
    | (rename_i a k x vals sh hs hk
       by_cases h : sldLo a k = true
       · left; simp [h]
       · right
         refine ⟨x, vals, sh, hk, by simp [h], ?_⟩
         rw [hs]
         revert h
         cases a <;> fin_cases k <;> simp [sldLo])
    | (left; rfl)
    | (left; split <;> rfl)

theorem rec_mw (c : Control.D) (ev : Event) (b : Blk) :
    (record c ev b).mw = b.mw ∨ ∃ x bs, ev.kind = .rd x bs ∧
      (record c ev b).mw = loadVal bs ∧ c.site = .vm := by
  unfold record
  split <;> first
    | (right; rename_i x bs hs hk; exact ⟨x, bs, hk, rfl, hs⟩)
    | (left; rfl)
    | (left; split <;> rfl)

theorem rec_pm (c : Control.D) (ev : Event) (b : Blk) :
    (record c ev b).pm = b.pm ∨ ∃ x bs, ev.kind = .rd x bs ∧
      (record c ev b).pm = loadVal bs ∧ c.site = .mld := by
  unfold record
  split <;> first
    | (right; rename_i x bs hs hk; exact ⟨x, bs, hk, rfl, hs⟩)
    | (left; rfl)
    | (left; split <;> rfl)

theorem rec_pe (c : Control.D) (ev : Event) (b : Blk) :
    (record c ev b).pe = b.pe ∨ ∃ x bs, ev.kind = .rd x bs ∧
      (record c ev b).pe = loadVal bs ∧ c.site = .eld := by
  unfold record
  split <;> first
    | (right; rename_i x bs hs hk; exact ⟨x, bs, hk, rfl, hs⟩)
    | (left; rfl)
    | (left; split <;> rfl)

theorem rec_o (c : Control.D) (ev : Event) (b : Blk) :
    (record c ev b).o = b.o ∨ ∃ x vals sh, ev.kind = .tc (.ld x vals sh) ∧
      (record c ev b).o = vals ∧ ((∃ k, c.site = .rld k) ∨ ∃ k, c.site = .old k) := by
  unfold record
  split <;> first
    | (right; rename_i k x vals sh hs hk; exact ⟨x, vals, sh, hk, rfl, Or.inl ⟨k, hs⟩⟩)
    | (right; rename_i k x vals sh hs hk; exact ⟨x, vals, sh, hk, rfl, Or.inr ⟨k, hs⟩⟩)
    | (left; rfl)
    | (left; split <;> rfl)

theorem rec_pw (c : Control.D) (ev : Event) (b : Blk) (j : Nat) :
    (record c ev b).pw j = b.pw j ∨ ∃ k x bs, ev.kind = .rd x bs ∧ c.site = .pld k ∧
      c.el ≠ 0 ∧ k.val = j ∧ (record c ev b).pw j = (c.a0, loadVal bs) := by
  unfold record
  split <;> first
    | (rename_i k x bs hs hk
       by_cases h0 : c.el = 0
       · left; simp [h0]
       · by_cases hj : j = k.val
         · right; exact ⟨k, x, bs, hk, hs, h0, hj.symm, by simp [h0, hj]⟩
         · left; simp [h0, hj])
    | (left; rfl)
    | (left; split <;> rfl)


/-- The pcs from which the accumulator words are loaded. -/
def accPcs : List Nat := [717, 814, 818, 915, 919, 1016, 1020, 1117, 1202, 1362, 1520, 1677,
  1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1491, 1492, 1493, 1494, 1495, 1496, 1497,
  1498, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1806, 1807, 1808, 1809, 1810, 1811,
  1812, 1813]

/-- The sites from which each block field is loaded. -/
def hasLo (s : Site) : Bool := (286 ≤ s.pc && s.pc ≤ 1122) || s == .sld true 1
def hasHi (s : Site) : Bool := (286 ≤ s.pc && s.pc ≤ 1122) || s == .sld false 1
def hasMw (s : Site) : Bool := 289 < s.pc && s.pc ≤ 1122
def hasPw (j : Nat) (s : Site) : Bool := 477 + 5 * j < s.pc && s.pc ≤ 1122
def hasPm (s : Site) : Bool := 572 < s.pc && s.pc ≤ 1122
def hasO (s : Site) : Bool := accPcs.contains s.pc
def hasPe (s : Site) : Bool := 1178 ≤ s.pc && s.pc ≤ 1831

/-- The sites whose event loads a field. -/
def estLo (s : Site) : Bool := s == .sld false 1 || s == .sld true 0
def estHi (s : Site) : Bool := s == .sld false 0 || s == .sld true 1
def estO : Site → Bool | .rld _ => true | .old _ => true | _ => false
def estPw (j : Nat) (s : Site) (el : Nat) : Bool :=
  (match s with | .pld k => k.val == j | _ => false) && el != 0

/-- **The loaded words of a state.** -/
def LdOk (d : D) : Prop :=
  (hasLo d.c.site = true → d.b.lo ≠ []) ∧ (hasHi d.c.site = true → d.b.hi ≠ []) ∧
  (hasMw d.c.site = true → d.b.mw ≠ .pred false) ∧
  (∀ j < 8, hasPw j d.c.site = true → d.b.pw j ≠ (.pred false, .pred false)) ∧
  (hasPm d.c.site = true → d.b.pm ≠ .pred false) ∧
  (hasO d.c.site = true → d.b.o ≠ []) ∧ (hasPe d.c.site = true → d.b.pe ≠ .pred false)

/-- The step of the loaded words along the chain's successors, as one check. -/
def ldChk (s s' : Site) (el : Nat) : Bool :=
  (!hasLo s' || hasLo s || estLo s) && (!hasHi s' || hasHi s || estHi s) &&
  (!hasMw s' || hasMw s || s == .vm) &&
  (List.range 8).all (fun j => !hasPw j s' || hasPw j s || estPw j s el) &&
  (!hasPm s' || hasPm s || s == .mld) && (!hasO s' || hasO s || estO s) &&
  (!hasPe s' || hasPe s || s == .eld)

set_option maxRecDepth 100000 in
theorem ld_tbl0 : ∀ s ∈ allSites, ∀ s' ∈ allSites,
    succOk {site := s, el := 0} {site := s'} = true → ldChk s s' 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ld_tbl1 : ∀ s ∈ allSites, ∀ s' ∈ allSites,
    succOk {site := s, el := 1} {site := s'} = true → ldChk s s' 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ld_tbl4 : ∀ s ∈ allSites, ∀ s' ∈ allSites,
    succOk {site := s, el := 4} {site := s'} = true → ldChk s s' 4 = true := by
  decide +kernel

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
