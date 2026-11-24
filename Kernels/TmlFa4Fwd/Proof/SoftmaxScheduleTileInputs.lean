-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleRoute
import Kernels.TmlFa4Fwd.Flow.Code.Part050
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

theorem prefixGate (l : Launch) (g : Nat) {batch : Nat} (hb : batch < 31) :
    Seg kernel [] l g 2 3223 [(2727, b32 (2^batch-1))]
      3225 [(467, .pred (decide (batch = 0))), (7245, b32 0)] := by
  intro t ht
  have hp : 2 ^ batch < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hMask : 2 ^ batch - 1 < 2 ^ 32 := by omega
  have hMask64 : 2 ^ batch - 1 < 2 ^ 64 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have hZero : 2 ^ batch - 1 = 0 ↔ batch = 0 := by
    cases batch with
    | zero => decide
    | succ n => have := Nat.one_lt_two_pow (Nat.succ_ne_zero n); omega
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hMask (by decide), toNat_ofNat_lt hMask64,
        compare, Option.getD_some, hz, Int.natCast_eq_zero, hZero]

variable {p : Params} {l : Launch}

theorem prefixIndexOut {m : Mem0} (hp : Pre p l m) {g idx word : Nat} (hIdx : idx < 32) {t : TState}
    (ht : At t 3227 [(2728, b32 idx), (7241, b32 word)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 word) idx 31
      (fun value _ => next (setReg t 2729 value))) := by
  have hb : l.block % 32 = 0 := by rw [hp.block]
  rw [selectionOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3227) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 2729 none (.reg 7241) (.reg 2728)
    (.imm 31) (.imm (-1))) = _
  have hIndex := readBits_b32 (g := g) (L := l) ht.2.2.2.2.1 (show idx < 2 ^ 32 by omega)
  have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hClamp : readBits l g t 32 (.imm 31) = .ok 31#64 := rfl
  simp only [shflTmpl, readValue, readReg, ht.2.2.2.2.2.1, hb, hMask, hClamp, hIndex,
    pure, Except.pure, toNat_ofNat_lt (show idx < 2 ^ 64 by omega)]
  rfl

private theorem scalarLoad {l : Launch} {g pc r word arg : Nat} {t : TState}
    {F : List (Nat × Value)}
    (ht : At t pc F) (hp : l.params (param arg) = some (BitVec.ofNat 64 word))
    (hw : word < 2 ^ 32) (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param arg) false, 0⟩, dsts := [some r] }⟩) :
    run kernel [] l g 1 t = some (next (setReg t r (b32 word))) := by
  apply run_local hc rfl ht
  rw [execLocalA_nil, execLocal_mem rfl]
  simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hp,
    DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hw (by decide)]
  rfl

set_option maxRecDepth 3000 in
theorem coordinateParams {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 3229 F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 7157 ∧ pair.1 ≠ 7150) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 3231 ((7150, b32 p.batch) :: (7157, b32 800) :: F) := by
  obtain ⟨hCap, h22⟩ := hp.values (22, 800) (by simp [Params.scalarWords])
  obtain ⟨hBatch, h19⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  let v := next (setReg t 7157 (b32 800))
  let u := next (setReg v 7150 (b32 p.batch))
  have hv : At v 3230 ((7157, b32 800) :: F) := ht.set fun pair hm => (hFresh pair hm).1
  have hu : At u 3231 ((7150, b32 p.batch) :: (7157, b32 800) :: F) := hv.set (by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hf
    · decide
    · exact (hFresh pair hf).2)
  change l.params (param 22) = some (BitVec.ofNat 64 800) at h22
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at h19
  have decimal22 : toString (22 : Nat) = "22" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (22 / 10 : Nat) = 2 by decide, show (22 % 10 : Nat) = 2 by decide,
      Nat.repr_of_lt (n := 2) (by decide), Nat.digitChar_eq_two.mpr rfl]
    rfl
  have decimal19 : toString (19 : Nat) = "19" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
    rfl
  have hr : run kernel [] l g 2 t = some u := run_comp
    (scalarLoad (r := 7157) ht h22 hCap (by rw [Flow.code_3229, param, decimal22]; rfl))
    (scalarLoad (r := 7150) hv h19 hBatch (by rw [Flow.code_3230, param, decimal19]; rfl))
  exact ⟨u, (selectionLocal (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hr).1, hu⟩

theorem tileCountOut {m : Mem0} (hp : Pre p l m) {g idx count : Nat} (hIdx : idx < 32) {t : TState}
    (ht : At t 3231 [(1222, b32 idx), (7240, b32 count)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 count) idx 31
      (fun value _ => next (setReg t 2730 value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [selectionOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3231) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 2730 none (.reg 7240) (.reg 1222)
    (.imm 31) (.imm (-1))) = _
  have hIndex := readBits_b32 (g := g) (L := l) ht.2.2.2.2.1 (show idx < 2 ^ 32 by omega)
  have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hClamp : readBits l g t 32 (.imm 31) = .ok 31#64 := rfl
  simp only [shflTmpl, readValue, readReg, ht.2.2.2.2.2.1, hBlock, hMask, hClamp, hIndex,
    pure, Except.pure, toNat_ofNat_lt (show idx < 2 ^ 64 by omega)]
  rfl

/-- The request-relative item uses both the previous groups and the selected group's prefix. -/
theorem relativeGroupItem (g : Nat) (l : Launch) {groupWork within cta : Nat}
    (hStart : groupWork + within ≤ cta) (hCta : cta < 2 ^ 31) :
    Seg kernel [] l g 2 3232
      [(1221, b32 groupWork), (7245, b32 within), (1072, b32 cta)] 3234
      [(2732, b32 (cta - (groupWork + within)))] := by
  have hg : groupWork % 4294967296 = groupWork := Nat.mod_eq_of_lt (by omega)
  have hw : within % 4294967296 = within := Nat.mod_eq_of_lt (by omega)
  have hs : (groupWork + within) % 4294967296 = groupWork + within :=
    Nat.mod_eq_of_lt (by omega)
  have hc : cta % 4294967296 = cta := Nat.mod_eq_of_lt (by omega)
  intro t ht
  seg_fp ht using norm_bits [hg, hw, hs, hc]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
