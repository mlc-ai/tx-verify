-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.AccessRef
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.AsyncDq
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async

@[expose] public section

/-! # The accesses of a dequantized tile, by kind

Every access covering a byte of the dequantized tile `r` of CTA `c` is one of six kinds
(`dq_classify`, from `access_dequant` and `async_dequant`): a dequant lane's chunk store, a staging
store of warpgroup 0 (tile 1), an MMA operand read, a copy's source read (tile 0), a query tensor
load's write (tile 0), an output tensor store's read (tile 1). The index `w` says whether the
access writes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The six kinds of access to the bytes of a dequantized tile.** -/
inductive DqRef (L : Launch) (X : Execution) (c : Nat) (r : Fin 2) (l : Loc) :
    AccessRef → Bool → Prop
  | dq {h k pcw : Nat} {ac : Acc} {bs : List Byte} :
      X.get (h, k) = some ⟨pcw, .wr ac bs⟩ → DequantAt L h pcw → ac.Covers l → h / L.block = c →
      DqRef L X c r l (.thread (h, k)) true
  | stage {y i pc : Nat} {a : Acc} {bs : List Byte} :
      X.get (y, i) = some ⟨pc, .wr a bs⟩ → Wg0At L y pc → r = 1 → MemRow.Wg0Stage L y pc a →
      a.Covers l → y / L.block = c → DqRef L X c r l (.thread (y, i)) true
  | mma {g j pc bb : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {isB : Bool}
      {idx : Nat} :
      X.get (g, j) = some ⟨pc, .tc (.mma bb sp acc mask)⟩ → MmaAt L g pc →
      X.MmaFootprint (g, j) isB idx l → g / L.block = c →
      DqRef L X c r l (.async (g, j) (.mmaRead isB idx)) false
  | cp {g j pc idx : Nat} {cs : TcCopy.Spec} :
      r = 0 → X.get (g, j) = some ⟨pc, .tc (.cp cs)⟩ → MmaAt L g pc →
      X.MmaFootprint (g, j) false idx l → g / L.block = c →
      DqRef L X c r l (.async (g, j) (.mmaRead false idx)) false
  | tload {g i pc al x y j : Nat} {s : TensorCopy.Spec} :
      r = 0 → X.get (g, i) = some ⟨pc, .tensorIssue al s⟩ → MmaAt L g pc →
      TensorCopy.writeLoc s x y j = some l → g / L.block = c →
      DqRef L X c r l (.async (g, i) (.write (.load x y j))) true
  | tstore {g i pc addr x y j : Nat} {s : TensorStore.Spec} :
      r = 1 → X.get (g, i) = some ⟨pc, .tensorStore addr s⟩ → Wg0At L g pc →
      TensorStore.readLoc s x y j = some l → g / L.block = c →
      DqRef L X c r l (.async (g, i) (.read (.store x y j))) false

/-- A copy's footprint is a copy's (not an MMA operand B). -/
private theorem cp_isB {i : EvId} {pc idx : Nat} {cs : TcCopy.Spec} {isB : Bool} {l : Loc}
    (hC : X.get i = some ⟨pc, .tc (.cp cs)⟩) (hf : X.MmaFootprint i isB idx l) : isB = false := by
  rcases hf with ⟨d, s, acc, mk, ⟨pc', hm⟩, -⟩ | ⟨c', k, cta, -, hB, -⟩
  · rw [hC] at hm
    cases hm
  · exact hB

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **An access covering a byte of the dequantized tile `r` of CTA `c` is of one of six kinds.** -/
theorem dq_classify {e : AccessRef} {a : Acc} {w : Bool} {c : Nat} {r : Fin 2} {l : Loc}
    (hI : X.Intent e a w) (hc : a.Covers l) (hl : MemRow.LocIn L c (.dequant r) l) :
    DqRef L X c r l e w := by
  cases e with
  | thread i =>
    obtain ⟨g, k⟩ := i
    have hgc : g / L.block = c := (access_below hp hX hFw hI hc hl.1).1.symm.trans hl.2.1
    obtain ⟨hw, pc, bs, hget, hcls⟩ := access_dequant hp hX hFw hI hc (by rw [hgc]; exact hl)
    subst hw
    rcases hcls with ⟨hat, hr, hst⟩ | hat
    · exact .stage hget hat hr hst hc hgc
    · exact .dq hget hat hc hgc
  | async i p =>
    obtain ⟨g, k⟩ := i
    have hgc : g / L.block = c := (async_below hp hX hFw hI hc hl.1).1.symm.trans hl.2.1
    rcases async_dequant hp hX hFw hI hc (by rw [hgc]; exact hl) with
      ⟨hw, pc, bb, sp, acc, mask, isB, idx, hget, hat, hpp, hf⟩ |
      ⟨hw, hr, pc, cs, isB, idx, hget, hat, hpp, hf⟩ |
      ⟨hw, hr, x, y, j, pc, s, addr, hget, hat, hpp, hrl⟩ |
      ⟨hw, hr, x, y, j, pc, s, addr, hget, hat, hpp, hrl⟩
    · subst hw hpp
      exact .mma hget hat hf hgc
    · subst hw hpp
      obtain rfl := cp_isB hget hf
      exact .cp hr hget hat hf hgc
    · subst hw hpp
      exact .tload hr hget hat hrl hgc
    · subst hw hpp
      exact .tstore hr hget hat hrl hgc

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
