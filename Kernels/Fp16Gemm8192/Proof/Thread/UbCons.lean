-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbLoader
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOut
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutEvents

@[expose] public section

/-! # The consumer's sites are not undefined behaviour

At every site of a consumer thread, the instruction's event is not undefined behaviour
(`Consumer.tmpl_ok`): the Tensor Memory loads address the warp's lanes of its accumulator, the
staging stores write packed halves at aligned staging addresses, the TMA stores read a 128-aligned
staging buffer through the output map at nonnegative coordinates, the base word is an aligned
word, the deallocation frees the 512 columns at the base the thread read, and the queries hold a
response, a cancelling one for the first-CTA query (`Consumer.Held`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

namespace Consumer

/-- The values a state holds for its queries and its deallocation: any response at the status
query, a cancelling one at the first-CTA query, an integer base at the deallocation. -/
def Held (d : D) : Prop :=
  (d.site = .clcStatus → ∃ r, d.resp = .clc r) ∧
    (d.site = .clcFirst → ∃ r, d.resp = .clc r ∧ r.firstCta.isSome) ∧
    (d.site = .dealloc → ∃ w x, d.base = .bits w x)

/-- The store sources of the epilogue are packed registers. -/
def storeSrcsOk (k : Fin 8) (i : Fin 4) : Bool :=
  (kernel.code[(Site.store k i 0).pc]?).any fun ins => match ins.op with
    | .mem { kind := .store, space := some (.shared .cta), elem := .int _ 32,
             addr := ⟨_, 0⟩, srcs := srcs, .. } =>
      srcs.length == 4 && srcs.all fun o => match o with
      | .reg r => (dataTable.lookup r).isNone && (packTable.lookup r).isSome &&
          (Flow.live (Site.store k i 0).pc).contains r
      | _ => false
    | _ => false

theorem store_srcs : ∀ k : Fin 8, ∀ i : Fin 4, storeSrcsOk k i = true := by
  decide +kernel

/-- A packed register holds four bytes. -/
theorem pack_bytes {L : Launch} {g : Nat} {d : D} {r : Nat} (h0 : dataTable.lookup r = none)
    (h : (packTable.lookup r).isSome = true) : (valueOf L g d r).bytes = 4 := by
  obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp h
  rw [valueOf_pack h0 hab]
  exact Flow.cvtPairV_bytes _ _

set_option maxHeartbeats 8000000 in
/-- The epilogue's staging stores are not undefined behaviour. -/
theorem store_ok (hpre : Pre P L mem0) {d : D} {ins : Instr} (htid : tidOf L g < 256) {k : Fin 8}
    {i el : Fin 4} (hs : d.site = .store k i el) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) : eventTmpl Prod L g t ins.op ≠ .ub f :=
      by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hst := setup_stageLt (tidOf L g) htid i i.isLt
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hat ⊢
  subst hs
  have hsub : t.sub = el.val := hat.2.1
  obtain ⟨srcs, hlen4, hop⟩ : ∃ srcs, srcs.length = 4 ∧ ins.op = .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
        vec := srcs.length, addr := ⟨.reg (storeBase (k.val % 2) i) 32, 0⟩,
        srcs := srcs } := by
    fin_cases k <;> fin_cases i <;> code_at hc <;> subst hc <;> exact ⟨[_, _, _, _], rfl, rfl⟩
  have hreg : t.regs (storeBase (k.val % 2) i) =
      some (b32 (L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i 0)) := by
    fin_cases k <;> fin_cases i <;> simp only [storeBase] <;>
      exact (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; simp only [stagingOff]; congr 1; omega))
  have hlt : L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i 0 < 2 ^ 32 := by
    simp only [stagingOff]; omega
  have hck := store_srcs k i
  have hpc : (Site.store k i el).pc = (Site.store k i 0).pc := rfl
  simp only [storeSrcsOk, ← hpc, hc, hop, Option.any_some] at hck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hck
  obtain ⟨hlen, hall⟩ := hck
  have hel : el.val < srcs.length := by rw [hlen]; exact el.isLt
  have hsrc := hall srcs[el.val] (List.getElem_mem hel)
  rw [hop]
  revert hsrc
  cases hsr : srcs[el.val] with
  | reg r =>
    intro hsrc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.contains_iff_mem] at hsrc
    obtain ⟨⟨h0, hp⟩, hl⟩ := hsrc
    refine stv_ok hreg hlt (.inr (.inr hlen4)) ?_
      (by rw [hsub, List.getElem?_eq_getElem hel, hsr])
      (reg_at hat.2.2.2.2 (by rw [hpc]; exact hl)) (pack_bytes h0 hp) f
    rw [hlen]
    simp only [stagingOff, stage]
    omega
  | _ => intro hsrc; simp at hsrc

/-- A tile store of the output map, through its parameter, from a 128-aligned shared buffer of the
CTA, at coordinates below `2 ^ 31`, with a 64-bit cache policy: the store of the map's box at the
coordinates' origin. -/
theorem tmaStore_tmpl (hpre : Pre P L mem0) {r src c1 c2 p : Nat}
    (hr0 : t.regs r = some (.ptr 64 true (.param "gemm_kernel_param_2") 0))
    {st x1 x2 y : Nat} (hs : t.regs src = some (b32 st)) (hst : st < 2 ^ 32) (h128 : st % 128 = 0)
    (hc1 : t.regs c1 = some (b32 x1)) (hx1 : x1 < 2 ^ 31) (hc2 : t.regs c2 = some (b32 x2))
    (hx2 : x2 < 2 ^ 31) (hp : t.regs p = some (b64 y)) (hx18 : x1 % 8 = 0) :
    eventTmpl Prod L g t (.cpTensorStore (.reg r) [.reg c1, .reg c2] src 0 (some (.reg p)) .tile
      none) = .tensorStore P.dMap ⟨⟨1, Fp16Gemm8192.mapD P.dBase P.dClass, fun axis =>
        (BitVec.ofNat 32 ([truncBits 32 (BitVec.ofNat 64 x1),
          truncBits 32 (BitVec.ofNat 64 x2)].getD
          axis.val 0).toNat).toInt, ⟨.shared, g / L.block, st⟩, none⟩, none⟩ (PTX.next t) := by
  have h1 := hpre.mapAlignment.2.2
  have h2 := hpre.mapRange.2.2
  have hm : tensorMap L g t (.reg r) [.reg c1, .reg c2] .tile =
      .ok (P.dMap, ⟨1, Fp16Gemm8192.mapD P.dBase P.dClass⟩) := by
    have h64 : P.dMap % 64 = 0 := by omega
    have h2' : P.dMap ≤ 18446744073709551488 := by omega
    simp [tensorMap, tensorMapAddress, readValue, readReg, hr0, hpre.paramD, mapParam,
      ParamObjectDecl.bytes, h1, h2', h64, hpre.mapD,
      Fp16Gemm8192.mapD_valid hpre.inputAlignment.2.2, TensorMode.coordinates, bind, Except.bind,
      pure, Except.pure]
  refine cpTensorStore_tmpl hm (effAddr_b32 hs hst) h128
    (vs := [truncBits 32 (BitVec.ofNat 64 x1), truncBits 32 (BitVec.ofNat 64 x2)]) ?_ ?_
    (x := truncBits 64 (BitVec.ofNat 64 y)) ?_ ?_
  · simp [readBits, readReg, hc1, hc2, b32, bind, Except.bind, pure, Except.pure]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> simp [truncBits, BitVec.toNat_ofNat] <;> omega
  · exact boxAligned_coords (by simp [Fp16Gemm8192.mapD, encodeTiled]; rfl) hx18 hx1
  · simp [readBits, readReg, hp, b64, bind, Except.bind, pure, Except.pure]

/-- A tile store of the output map, through its parameter, from a 128-aligned shared buffer of the
CTA, at coordinates below `2 ^ 31`, with a 64-bit cache policy, is not undefined behaviour. -/
theorem tmaStore_ok (hpre : Pre P L mem0) {r src c1 c2 p : Nat}
    (hr0 : t.regs r = some (.ptr 64 true (.param "gemm_kernel_param_2") 0))
    {st x1 x2 y : Nat} (hs : t.regs src = some (b32 st)) (hst : st < 2 ^ 32) (h128 : st % 128 = 0)
    (hc1 : t.regs c1 = some (b32 x1)) (hx1 : x1 < 2 ^ 31) (hc2 : t.regs c2 = some (b32 x2))
    (hx2 : x2 < 2 ^ 31) (hp : t.regs p = some (b64 y)) (hx18 : x1 % 8 = 0) (f : Fault) :
    eventTmpl Prod L g t (.cpTensorStore (.reg r) [.reg c1, .reg c2] src 0 (some (.reg p)) .tile
      none) ≠ .ub f := by
  rw [tmaStore_tmpl hpre hr0 hs hst h128 hc1 hx1 hc2 hx2 hp hx18]
  simp

set_option maxHeartbeats 8000000 in
/-- The epilogue's TMA stores are not undefined behaviour. -/
theorem tma_ok (hpre : Pre P L mem0) {d : D} {ins : Instr} (hi : Inv d) (htid : tidOf L g < 256)
    {k : Fin 8} (hs : d.site = .tma k) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) : eventTmpl Prod L g t ins.op ≠ .ub f :=
      by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hm := hi.m
  have hn := hi.n
  have hw : tidOf L g / 32 / 4 < 2 := by omega
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hat hm hn ⊢
  subst hs
  fin_cases k
  all_goals
    code_at hc
    subst hc
    exact tmaStore_ok hpre ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values)))
      (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl)) (by omega) (by omega)
      (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl)) (by omega)
      (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl)) (by omega)
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; rfl))) (by omega) f

set_option maxHeartbeats 8000000 in
/-- The Tensor Memory loads are not undefined behaviour. -/
theorem load_ok (hpre : Pre P L mem0) {d : D} {ins : Instr} (htid : tidOf L g < 256) {j : Fin 16}
    (hs : d.site = .load j) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) : eventTmpl Prod L g t ins.op ≠ .ub f :=
      by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hw : tidOf L g / 32 / 4 < 2 := by omega
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hat ⊢
  subst hs
  fin_cases j
  all_goals
    code_at hc
    subst hc
    refine tcLd_ok hb (by decide) (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl))
      (by omega) ?_ f
    exact tcDataAddressOk_of_row_zero rfl (by omega)

end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
