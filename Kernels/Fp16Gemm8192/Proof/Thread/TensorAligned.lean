-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.GlobalWrites
public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Lemmas.Flow.TensorOrigin

@[expose] public section

/-! # The boxes of the kernel's tensor copies are aligned

A slice's TMA store starts its box at the slice's column `256 n + 32 k`, and the loader's load of
block `b` at the K coordinate `64 (q + b)`, so the box's first coordinate, in bytes, is a multiple
of sixteen (`Consumer.tma_aligned`, `Loader.load_aligned`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The register holding slice `k`'s column, the first coordinate of its TMA store. -/
def tmaCol (k : Nat) : Nat :=
  [453, 475, 498, 521, 544, 567, 594, 622].getD k 0

/-- The first coordinate of an origin read from a register holding a multiple of eight. -/
theorem origin_mod8 {v : Nat} (h8 : v % 8 = 0) {bits : BitVec 64}
    (hb : bits = truncBits 32 (BitVec.ofNat 64 v)) :
    ((BitVec.ofNat 32 bits.toNat).toInt) % 8 = 0 := by
  subst hb
  have h1 : (truncBits 32 (BitVec.ofNat 64 v)).toNat = v % 2 ^ 32 := by
    simp only [truncBits, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
  rw [h1]
  unfold BitVec.toInt
  simp only [BitVec.toNat_ofNat]
  have h2 : v % 2 ^ 32 % 2 ^ 32 = v % 2 ^ 32 := Nat.mod_mod _ _
  rw [h2]
  split_ifs <;> omega

/-- **A slice's TMA store has an aligned box.** -/
theorem tma_aligned (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t) (hinv : Inv d)
    (htid : tidOf L g < 256) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} (hs : d.site = .tma k) :
    ∀ a s, e.kind = .tensorStore a s → TensorDescriptor.BoxAligned s.descriptor s.origin := by
  intro a s hk
  obtain ⟨-, hdesc, -⟩ := tma_event hpre hat htid hc hf hs a s hk
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := s
  simp only at hdesc
  cases hdesc
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat hinv ⊢
  subst hs
  have hn : n < 32 := hinv.n
  have hcol : t.regs (tmaCol k.val) = some (b32 (256 * n + 32 * k.val)) := by
    fin_cases k <;> simp only [tmaCol] <;>
      exact (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))
  unfold TensorDescriptor.BoxAligned
  simp only [Fp16Gemm8192.mapD, Fp16Gemm8192.encodeTiled]
  have hk8 := k.isLt
  fin_cases k <;> code_at hc <;> subst hc <;> simp only [tmaCol, List.getD_cons_zero,
    List.getD_cons_succ] at hcol <;>
  (obtain ⟨bits, hb, hor⟩ := fires_cpTensorStore_origin hf a _ hk
   simp only [readBits, readReg, hcol, b32, bind, Except.bind, pure, Except.pure,
     Except.ok.injEq] at hb
   have h8 := origin_mod8 (by omega) hb.symm
   dsimp only at hor
   simp only [TensorDescriptor.Format.bytes]
   rw [hor]
   omega)

end Consumer

namespace Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event} {ins : Instr}

/-- The register holding block `b`'s K coordinate, the first coordinate of its loads. -/
def kCol (b : Nat) : Nat :=
  [661, 680, 699, 718, 737, 757, 777, 797].getD b 0

/-- At a load, the register of its block's K coordinate holds `64 (q + b)`. -/
theorem kCol_value {d : D} (b : Fin 8) (j : Fin 3) (hs : d.site = .load b j)
    (h : At t d.site.pc (facts L g d)) : t.regs (kCol b.val) = some (b32 (64 * (d.q + b.val))) := by
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h ⊢
  subst hs
  fin_cases b <;> fin_cases j <;> simp only [kCol] <;>
    exact (reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by loader_values))

/-- **A load's box is aligned.** -/
theorem load_aligned (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} (b : Fin 8) (j : Fin 3)
    (hs : d.site = .load b j) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∀ a sp, e.kind = .tensorIssue a sp → TensorDescriptor.BoxAligned sp.descriptor sp.origin := by
  intro a sp hk
  obtain ⟨a', sp', he, -, base, cls, origin, hsp, -⟩ := load_stage hpre hg b j hs h hc hf
  rw [he] at hk
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  have hcol := kCol_value b j hs h
  have hbytes : sp'.descriptor.format.bytes = 2 := by
    rw [hsp]
    rfl
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf he hcol ⊢
  subst hs
  unfold TensorDescriptor.BoxAligned
  rw [hbytes]
  have hb8 := b.isLt
  fin_cases b <;> fin_cases j <;> code_at hc <;> subst hc <;>
    simp only [kCol, List.getD_cons_zero, List.getD_cons_succ] at hcol <;>
  (obtain ⟨bits, hb, hor⟩ := fires_cpTensor_origin hf a' _ (by rw [he])
   simp only [readBits, readReg, hcol, b32, bind, Except.bind, pure, Except.pure,
     Except.ok.injEq] at hb
   have h8 := Consumer.origin_mod8 (by omega) hb.symm
   rw [hor]
   simp only [Nat.cast_ofNat]
   omega)

end Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The boxes of the tensor loads are aligned.** -/
theorem tensor_aligned_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorCopy.Spec} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tensorIssue a sp) : TensorDescriptor.BoxAligned sp.descriptor sp.origin := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hop : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact absurd hk (fires_notTensor (eventTmpl_notTensor h) hfire a sp)
    · rfl
  obtain ⟨l, b, j, rfl, hs⟩ := load_state (OpPcsFast.mem kernel_load_pcs hc hop)
  cases o with
  | none => exact absurd hk (fires_none_notTensor hfire a sp)
  | some u => exact Loader.load_aligned hpre hg b j hs hat hc hfire a sp hk

/-- **The TMA stores read their CTA's staging buffer, with aligned boxes.** -/
theorem store_box_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorStore.Spec} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tensorStore a sp) :
    sp.sharedBase.cta = g / L.block ∧ TensorDescriptor.BoxAligned sp.descriptor sp.origin := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨c, s, rfl, hs⟩ :=
    store_state (OpPcsFast.mem kernel_store_pcs hc (fires_tensorStore_op hfire hk))
  refine ⟨?_, Consumer.tma_aligned hpre hat hinv.1 hinv.2.1 hc hfire hs a sp hk⟩
  obtain ⟨-, -, hsh⟩ := Consumer.tma_event hpre hat hinv.2.1 hc hfire hs a sp hk
  rw [hsh]

end
end PTX.Kernels.Fp16Gemm8192.Proof
