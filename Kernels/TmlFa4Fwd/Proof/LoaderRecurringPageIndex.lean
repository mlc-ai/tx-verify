-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Flow.Code.Part014
public import Kernels.TmlFa4Fwd.Flow.Code.Part021
public import Kernels.TmlFa4Fwd.Flow.Code.Part022

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

structure RecurringPageSite where
  indexPc : Nat
  rowBase : Nat
  slotOffset : Nat
  row : Nat
  wideProduct : Nat
  highWord : Nat
  pageIndex : Nat
  masked : Nat
  physicalPage : Nat

/-- Warm and steady refreshes calculate the same quotient and row guard in different registers. -/
def recurringPageSite : Fin 2 → RecurringPageSite
  | 0 => ⟨929, 1969, 1964, 1120, 7644, 1970, 1121, 167, 7176⟩
  | 1 => ⟨1403, 1148, 2131, 1149, 7759, 2132, 1150, 210, 7183⟩

def recurringPageIndexInput (i : Fin 2) (base length : Nat) (entry : Fin 2) :
    List (Nat × Value) :=
  let s := recurringPageSite i
  [(s.rowBase, b32 base), (s.slotOffset, b32 (64 * entry.val)),
   (7302, b64 1), (1093, b32 1), (1094, b32 3), (1086, b32 length)]

def recurringPageIndexFacts (i : Fin 2) (row length : Nat) : List (Nat × Value) :=
  let s := recurringPageSite i
  [(s.row, b32 row), (s.pageIndex, b32 (row / 16)),
   (s.masked, .pred (decide (length ≤ row))), (s.physicalPage, b32 0)]

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The shared warm and steady page-index arithmetic under local core rules. -/
theorem recurringPageIndexCore {l : Launch} {g base length : Nat}
    (i : Fin 2) (entry : Fin 2) (hRow : base + 64 * entry.val < 2 ^ 31)
    (hLen : length < 2 ^ 31) :
    Seg kernel [] l g 10 (recurringPageSite i).indexPc
      (recurringPageIndexInput i base length entry) ((recurringPageSite i).indexPc + 10)
      (recurringPageIndexFacts i (base + 64 * entry.val) length) := by
  let site := recurringPageSite i
  let row := base + 64 * entry.val
  have hRow31 : row < 2 ^ 31 := hRow
  have hBase : base < 2 ^ 32 := by omega
  have hRow32 : row < 2 ^ 32 := by omega
  have hRow64 : row < 2 ^ 64 := by omega
  have hHalf : row / 2 < 2 ^ 32 := by omega
  have hPage : row / 16 < 2 ^ 32 := by omega
  have hLen32 : length < 2 ^ 32 := by omega
  have hOff : 64 * entry.val < 2 ^ 32 := by omega
  have hHigh : row / 4294967296 = 0 := by omega
  have hPageShift : row / 2 / 8 = row / 16 := by omega
  let frame := [(site.row, b32 row), (1093, b32 1), (1094, b32 3), (1086, b32 length)]
  have prep : Seg kernel [] l g 3 site.indexPc (recurringPageIndexInput i base length entry)
      (site.indexPc + 3) ((site.wideProduct, b64 row) :: frame) := by
    fin_cases i <;> intro t ht <;>
      simp only [site, recurringPageSite, frame, recurringPageIndexInput] at ht ⊢ <;>
      seg_fp ht using norm_bits [row, Nat.add_comm, Nat.mod_eq_of_lt hBase,
        Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64, Nat.mod_eq_of_lt hOff]
  have unpack : Seg kernel [] l g 1 (site.indexPc + 3) ((site.wideProduct, b64 row) :: frame)
      (site.indexPc + 4) ((site.highWord, b32 0) :: frame) := by
    have unpackDecoded : kernel.code[site.indexPc + 3]? = some ⟨none, .move
        ⟨.unpack, .int .b 64, [none, some site.highWord], [.reg site.wideProduct]⟩⟩ := by
      fin_cases i
      · exact Flow.code_932
      · exact Flow.code_1406
    intro t ht
    let u := next (setReg t site.highWord (b32 0))
    have hr : run kernel [] l g 1 t = some u := by
      apply run_local unpackDecoded rfl ht
      rw [execLocalA_nil, execLocal_move rfl]
      simp [execMove, readReg, readValue, ht.2.2.2.2.1, DType.width,
        Value.bytes, b64, splitValue, toNat_ofNat_lt hRow64, hHigh, setDst, b32,
        bind, Except.bind, pure, Except.pure, u]
      rfl
    have hf : site.highWord ∉ frame.map Prod.fst := by
      fin_cases i <;> simp [site, recurringPageSite, frame]
    exact ⟨u, hr, (ht.mono ht.2.2.2.2.2).set
      (fun pair hm he => hf (he ▸ List.mem_map_of_mem hm))⟩
  have page : Seg kernel [] l g 6 (site.indexPc + 4) ((site.highWord, b32 0) :: frame)
      (site.indexPc + 10) (recurringPageIndexFacts i row length) := by
    fin_cases i <;> intro t ht <;>
      simp only [site, recurringPageSite, frame, recurringPageIndexFacts] at ht ⊢ <;>
      seg_fp ht using first
        | rfl
        | norm_bits [hPageShift, Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64,
            Nat.mod_eq_of_lt hHalf, Nat.mod_eq_of_lt hPage]
        | simp only [truncBits_ofNat hRow32 (by decide),
            truncBits_ofNat hLen32 (by decide), compare, Option.getD_some, signedWord hRow31,
            signedWord hLen, ge_iff_le, Int.ofNat_le]
  exact prep.comp (unpack.comp page)

end
end PTX.Kernels.TmlFa4Fwd.Loader
