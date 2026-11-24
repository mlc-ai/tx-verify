-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingStart
public import Kernels.TmlFa4Fwd.Flow.Code.Part006

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def addressPreludeInputs (p : Params) (batch head : Nat) : List (Nat × Value) :=
  [(7169, b32 head), (9534, b64 0), (1059, .bits 16 4),
   (7505, b64 p.pageTableStride), (7297, b64 batch), (7504, b64 p.pageTableBase)]

private theorem addressSigned {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem addressPreludeCore {p : Params} {l : Launch} {g batch head : Nat}
    (hHead : head < 2 ^ 31)
    (hBatch : batch < 18446744073709551616) (hStride : p.pageTableStride < 18446744073709551616)
    (hAddress : p.pageTableBase + 4 * (batch * p.pageTableStride) < 18446744073709551616) :
    Seg kernel [] l g 11 415 (addressPreludeInputs p batch head)
      426 [(108, .pred true), (1044, .bits 16 3), (7520, b64 1),
        (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride))),
        (1808, b32 (head / 6))] := by
  have hHead32 : head < 4294967296 := by omega
  have hQ32 : head / 6 < 4294967296 := by omega
  have hQ64 : head / 6 < 18446744073709551616 := by omega
  have hQMod : ((head / 6 : Nat) : Int) % 18446744073709551616 = (head / 6 : Nat) := by
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hMagic : toSigned 32 715827883#64 = 715827883 := rfl
  have hDiv : (head : Int) * 715827883 / 4294967296 = (head / 6 : Nat) := by omega
  have hZero : head / 6 / 2147483648 = 0 := by omega
  have hBase : p.pageTableBase < 18446744073709551616 := by omega
  have hProd : batch * p.pageTableStride < 18446744073709551616 := by omega
  have hOff : 4 * (batch * p.pageTableStride) < 18446744073709551616 := by omega
  intro t ht
  simp only [addressPreludeInputs] at ht
  seg_fp ht using first
    | decide
    | norm_bits [kind_s_beq_s, ↓reduceIte, addressSigned hHead, hMagic,
        show (2 : Int) ^ 32 = 4294967296 from rfl,
        hDiv, hQMod, Int.toNat_natCast, hZero, Nat.zero_mod, Nat.add_zero,
        Nat.mod_eq_of_lt hHead32, Nat.mod_eq_of_lt hQ32, Nat.mod_eq_of_lt hQ64,
        Nat.mod_eq_of_lt hBatch, Nat.mod_eq_of_lt hStride,
        Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hProd, Nat.mod_eq_of_lt hOff,
        Nat.mod_eq_of_lt hAddress, Nat.mul_comm p.pageTableStride batch,
        Nat.mul_comm (batch * p.pageTableStride) 4]

private theorem nonnegativeHead {l : Launch} {g head : Nat} (hHead : head < 2 ^ 31) :
    Seg kernel [] l g 4 426 [(7169, b32 head), (1808, b32 (head / 6))]
      430 [(111, .pred false)] := by
  have hHead32 : head < 2 ^ 32 := by omega
  have hZero : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hNonnegative : ¬ (head : Int) < 0 := by omega
  intro t ht
  seg_fp ht using simp only [truncBits_ofNat hHead32 (by decide), compare, Option.getD_some,
    addressSigned hHead, hZero, hNonnegative, decide_false, Bool.false_and]

def addressCacheInputs (p : Params) : List (Nat × Value) :=
  [(7494, b64 p.kLayout.headStride), (7492, b64 p.kLayout.base),
   (7498, b64 p.vLayout.headStride), (7496, b64 p.vLayout.base)]

private theorem addressCacheCore {p : Params} {l : Launch} {g head : Nat}
    (hHead : head < 2 ^ 31) :
    Seg kernel [] l g 9 430
      ((111, .pred false) :: (1808, b32 (head / 6)) :: addressCacheInputs p)
      439 [(7300, b64 (p.kLayout.base + 2 * ((head / 6) * p.kLayout.headStride))),
        (7301, b64 (p.vLayout.base + 2 * ((head / 6) * p.vLayout.headStride)))] := by
  have hQ32 : head / 6 < 4294967296 := by omega
  have hQ64 : head / 6 < 18446744073709551616 := by omega
  have hQMod : ((head / 6 : Nat) : Int) % 18446744073709551616 = (head / 6 : Nat) := by
    exact Int.emod_eq_of_lt (by omega) (by omega)
  intro t ht
  simp only [addressCacheInputs] at ht
  seg_fp ht using
    simp only [b64, truncBits_ofNat (w := 32) hQ32 (by decide), ↓reduceIte,
      cvtIntBits, intOf, intSat, intBits, Bool.not_false]
    all_goals nf_simp [Nat.mul_comm (head / 6) _, Nat.mul_comm _ 2, Nat.mul_mod,
      Nat.add_mod, Nat.mod_eq_of_lt hQ32, Nat.mod_eq_of_lt hQ64, Nat.mod_mod, Nat.add_zero,
      addressSigned (show head / 6 < 2 ^ 31 by omega), hQMod, Int.toNat_natCast]

def addressPreludeOutputs (p : Params) (batch head : Nat) : List (Nat × Value) :=
  [(108, .pred true), (1044, .bits 16 3), (7520, b64 1),
   (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride))),
   (7300, b64 (p.kLayout.base + 2 * ((head / 6) * p.kLayout.headStride))),
   (7301, b64 (p.vLayout.base + 2 * ((head / 6) * p.vLayout.headStride)))]

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch head tile : Nat}
    (hb : batch < p.batch) (hh : head < 2 ^ 31) (hTile : 256 * tile < p.qLength batch) {t : TState}
    {F : List (Nat × Value)}
    (hFrame : ((kernel.code.drop 415).take 24).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (ht : At t 415 (addressPreludeInputs p batch head ++ addressCacheInputs p ++ F))
include hp hb hh hTile hFrame ht

/-- The read-only page-table batch base is computed from the actual ABI operands.
The last three shift constants agree with the ensuing page-index calculation. -/
theorem loaderAddressPreludeRun : ∃ u, run kernel Assumptions.all l g 24 t = some u ∧
      At u 439 (addressPreludeOutputs p batch head ++ F) := by
  have hRange := hp.ranges ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩
    (by simp [Params.inputRegions])
  change p.pageTableBase + 4 * p.batch * p.pageTableStride ≤ 2 ^ 64 at hRange
  have hActive : 0 < p.pageTableStride := by
    have := (hp.pageTable batch hb).1
    have := (hp.lengths batch hb).2.1
    by_contra hn
    have hZero : p.pageTableStride = 0 := by omega
    have hK : p.kLength batch = 0 := by omega
    omega
  have hShift := Nat.mul_lt_mul_of_pos_right hb hActive
  have hAddr : p.pageTableBase + 4 * (batch * p.pageTableStride) < 2 ^ 64 := by
    rw [Nat.mul_assoc] at hRange
    omega
  have hBatch64 : batch < 18446744073709551616 := by have := hp.shape.2.1; omega
  have hStride64 : p.pageTableStride < 18446744073709551616 := by
    have hPos := hp.shape.1
    have hMul := Nat.mul_le_mul_right p.pageTableStride (show 1 ≤ p.batch by omega)
    simp only [Nat.one_mul] at hMul
    rw [Nat.mul_assoc] at hRange
    omega
  obtain ⟨hBoth, hF⟩ := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨hArgs, hCache⟩ := (holds_append ..).mp hBoth
  obtain ⟨v, hv, hV⟩ := addressPreludeCore (g := g) hh hBatch64 hStride64 hAddr t (ht.mono hArgs)
  let keep := [(7169, b32 head)] ++ addressCacheInputs p
  obtain ⟨_, hvFrame⟩ := loaderLinear (regs := keep.map Prod.fst) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeepV : Holds v.regs keep := holdsSchedulerFrame ⟨hArgs.1, hCache⟩
    hvFrame (fun _ hm => List.mem_map_of_mem hm)
  have hQuot := hV.2.2.2.2.2.2.2.2.1
  obtain ⟨w, hw, hW⟩ := nonnegativeHead (l := l) (g := g) hh v
    (hV.mono ⟨hKeepV.1, hQuot, trivial⟩)
  let later := (1808, b32 (head / 6)) :: addressCacheInputs p
  obtain ⟨_, hwFrame⟩ := loaderLinear (regs := later.map Prod.fst) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hw
  have hKeepW : Holds w.regs later := holdsSchedulerFrame ⟨hQuot, hKeepV.2⟩
    hwFrame (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨u, hu, hU⟩ := addressCacheCore (l := l) (g := g) hh w
    (hW.mono ⟨hW.2.2.2.2.1, hKeepW⟩)
  let setup := [(108, .pred true), (1044, .bits 16 3), (7520, b64 1),
    (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride)))]
  obtain ⟨_, hsFrame⟩ := loaderLinear (regs := setup.map Prod.fst) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hw hu)
  obtain ⟨huA, huFrame⟩ := loaderLinear (n := 24) (by decide) (by decide) ht.1 hFrame
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hv (run_comp hw hu))
  have hKeep := holdsSchedulerFrame hF huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hvSetup : Holds v.regs setup :=
    ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1, trivial⟩
  have huSetup := holdsSchedulerFrame hvSetup hsFrame (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u, huA, hU.mono ((holds_append ..).mpr ⟨?_, hKeep⟩)⟩
  exact ⟨huSetup.1, huSetup.2.1, huSetup.2.2.1, huSetup.2.2.2.1, hU.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
