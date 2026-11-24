-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbCons
public import Kernels.Fp16Gemm8192.Proof.Support.Addresses
public import Kernels.Fp16Gemm8192.Proof.Thread.GlobalWrites

@[expose] public section

/-! # The kernel's tensor copies stay inside their maps

A tensor load of the loader reads the A or B map's 64 x 128 box at coordinates that the loader's
tile and K block fix, and a TMA store of a consumer writes the output map's 32 x 128 box at its
tile's coordinates: every slot of the box is inside the 8192 x 8192 matrix (`Loader.load_bounds`,
`Consumer.tma_bounds`), whatever the map's allocation class. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow TensorDescriptor

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The origin a two-coordinate tensor instruction records from 32-bit integer coordinates below
`2 ^ 31`. -/
theorem origin_b32 {x1 x2 : Nat} (h1 : x1 < 2 ^ 31) (h2 : x2 < 2 ^ 31) :
    (fun axis : Fin 2 => (BitVec.ofNat 32 ([truncBits 32 (BitVec.ofNat 64 x1),
      truncBits 32 (BitVec.ofNat 64 x2)].getD axis.val 0).toNat).toInt) = tensorOrigin x1 x2 := by
  have e : ∀ x : Nat, x < 2 ^ 31 →
      (BitVec.ofNat 32 (truncBits 32 (BitVec.ofNat 64 x)).toNat).toInt = x := by
    intro x hx
    have h64 : x < 18446744073709551616 := by omega
    have h32 : x < 4294967296 := by omega
    simp [truncBits, BitVec.toInt_eq_toNat_cond, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]
    omega
  funext axis
  fin_cases axis
  · exact e x1 h1
  · exact e x2 h2

/-- Every slot of a tiled FP16 box of an 8192 x 8192 matrix whose origin leaves room for the box is
inside the matrix. -/
theorem tile_in_bounds {base bi bo ox oy : Nat} {sw : TensorSwizzle.Mode} {cls : AllocationClass}
    (hx : ox + bi ≤ 8192) (hy : oy + bo ≤ 8192) :
    ¬ TensorHasOob (encodeTiled .f16 base 8192 8192 16384 bi bo sw cls) (tensorOrigin ox oy)
      none := by
  rintro ⟨slot, hn⟩
  apply hn
  have hcolumn : slot.1.val < bi := by
    simpa [encodeTiled, TensorTile.count, TensorTile.step] using slot.1.isLt
  have hrow : slot.2.1.val < bo := by
    simpa [encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step] using
      slot.2.1.isLt
  have hindex : TensorTransfer.index slot = (fun axis : Fin 2 =>
      if axis.val = 0 then slot.1.val else slot.2.1.val) := by
    funext axis
    fin_cases axis <;> rfl
  intro axis
  simp only [TensorTransfer.coord, hindex]
  fin_cases axis <;>
    simp [geometry, encodeTiled, TensorTile.coord, TensorTile.step, tensorOrigin]
  all_goals omega

namespace Loader

/-- The loader's loads read the map's box inside the matrix. -/
theorem copy_bounds (hpre : Pre P L mem0) (hg : g < L.threads) {dst mb r c1 c2 : Nat}
    {name : String} (hr0 : t.regs r = some (.ptr 64 true (.param name) 0))
    (hn : name = "gemm_kernel_param_0" ∨ name = "gemm_kernel_param_1")
    {st a x1 x2 : Nat} (hd : t.regs dst = some (b32 st)) (hst : st < 2 ^ 32) (h128 : st % 128 = 0)
    (hmb : t.regs mb = some (.ptr 32 false (.shared (g / L.block) (2 *
      (g / L.block / 2))) (BitVec.ofNat 64 a)))
    (ha : a < 2 ^ 32) (h8 : a % 8 = 0)
    (hc1 : t.regs c1 = some (b32 x1)) (hc2 : t.regs c2 = some (b32 x2))
    (hx1 : x1 + 64 ≤ 8192) (hx2 : x2 + 128 ≤ 8192) (hx18 : x1 % 8 = 0)
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Prod L g t
      (.cpTensor true true dst 0 (.reg r) [.reg c1, .reg c2] mb 0 none .tile)) e o)
    {a' : Nat} {sp : TensorCopy.Spec} (hk : e.kind = .tensorIssue a' sp) :
    ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  obtain ⟨M, base, cls, -, h⟩ := copy_tmpl hpre hg hr0 hn hd hst h128 hmb ha h8 hc1 hc2 hx18
    (by omega)
  rw [h] at hf
  obtain ⟨rfl, -⟩ := hf
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  dsimp only
  rw [origin_b32 (by omega) (by omega)]
  exact tile_in_bounds hx1 hx2

set_option maxHeartbeats 8000000 in
/-- **The loader's loads read their map's box inside the matrix.** -/
theorem load_bounds (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (b : Fin 8)
    (j : Fin 3) (hs : d.site = .load b j) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) {e : Event} {o : Option TState}
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {a : Nat} {sp : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a sp) : ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hm := hi.m
  have hn := hi.n
  have hq := hi.q
  have hq8 := hi.q8
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf hm hn hq hq8 ⊢
  subst hs
  fin_cases b <;> fin_cases j
  all_goals
    code_at hc
    subst hc
    refine copy_bounds hpre hg ((reg_at h.2.2.2.2 (by lit_mem)).trans
      (congrArg some (by loader_values; rfl))) (by simp)
      (reg_b32 h.2.2.2.2 (by lit_mem) (by loader_values; rfl)) (by omega) (by omega)
      ((reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by loader_values; rfl)))
      (by omega) (by omega) (reg_b32 h.2.2.2.2 (by lit_mem) (by loader_values; rfl))
      (reg_b32 h.2.2.2.2 (by lit_mem) (by loader_values; rfl)) ?_ ?_ ?_ hf hk
    all_goals first | omega | (simp only [outputRow]; omega)

end Loader

namespace Consumer

/-- A TMA store of the output map writes its box inside the matrix. -/
theorem tmaStore_bounds (hpre : Pre P L mem0) {r src c1 c2 p : Nat}
    (hr0 : t.regs r = some (.ptr 64 true (.param "gemm_kernel_param_2") 0))
    {st x1 x2 y : Nat} (hs : t.regs src = some (b32 st)) (hst : st < 2 ^ 32) (h128 : st % 128 = 0)
    (hc1 : t.regs c1 = some (b32 x1)) (hc2 : t.regs c2 = some (b32 x2))
    (hx1 : x1 + 32 ≤ 8192) (hx2 : x2 + 128 ≤ 8192) (hp : t.regs p = some (b64 y))
    (hx18 : x1 % 8 = 0) {pc : Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Prod L g t
      (.cpTensorStore (.reg r) [.reg c1, .reg c2] src 0 (some (.reg p)) .tile none)) e o)
    {a : Nat} {sp : TensorStore.Spec} (hk : e.kind = .tensorStore a sp) :
    ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  rw [tmaStore_tmpl hpre hr0 hs hst h128 hc1 (by omega) hc2 (by omega) hp hx18] at hf
  obtain ⟨rfl, -⟩ := hf
  simp only [Kind.tensorStore.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  dsimp only
  rw [origin_b32 (by omega) (by omega)]
  exact tile_in_bounds hx1 hx2

set_option maxHeartbeats 8000000 in
/-- **The epilogue's TMA stores write their map's box inside the matrix.** -/
theorem tma_bounds (hpre : Pre P L mem0) {d : D} {ins : Instr} (hi : Inv d) (htid : tidOf L g < 256)
    {k : Fin 8} (hs : d.site = .tma k) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins) {e : Event} {o : Option TState}
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {a : Nat} {sp : TensorStore.Spec}
    (hk : e.kind = .tensorStore a sp) : ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hm := hi.m
  have hn := hi.n
  have hw : tidOf L g / 32 / 4 < 2 := by omega
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hat hf hm hn ⊢
  subst hs
  fin_cases k
  all_goals
    code_at hc
    subst hc
    exact tmaStore_bounds hpre ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values)))
      (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl)) (by omega) (by omega)
      (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl))
      (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl)) (by omega) (by omega)
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; rfl))) (by omega) hf hk

end Consumer

variable {X : Execution}

/-- **A tensor load reads its map's box inside the matrix.** -/
theorem tensor_bounds_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorCopy.Spec} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tensorIssue a sp) : ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hop : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact absurd hk (fires_notTensor (eventTmpl_notTensor h) hfire a sp)
    · rfl
  obtain ⟨l, b, j, rfl, hs⟩ := load_state (OpPcsFast.mem kernel_load_pcs hc hop)
  exact Loader.load_bounds hpre hg b j hs hinv.1 hat hc hfire hk

/-- **A tensor store writes its map's box inside the matrix.** -/
theorem store_bounds_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorStore.Spec} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tensorStore a sp) : ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨c, s, rfl, hs⟩ := store_state
    (OpPcsFast.mem kernel_store_pcs hc (fires_tensorStore_op hfire hk))
  exact Consumer.tma_bounds hpre hinv.1 hinv.2.1 hs hat hc hfire hk

end

end PTX.Kernels.Fp16Gemm8192.Proof
