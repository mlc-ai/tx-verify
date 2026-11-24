-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputValues
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputPayload

@[expose] public section

/-! # Decode a performed output byte as a normalized Tensor Memory word -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputPayload

open PTX Wg0

private theorem pair_byte (f : Nat → ℝ) (n : Nat) (pos : Fin 4) :
    (Value.pair (.float .bf16 (f (2 * n))) (.float .bf16 (f (2 * n + 1)))).toBytes[pos.val]? =
      some (.float .bf16 (f (2 * n + pos.val / 2)), pos.val % 2) := by
  fin_cases pos <;> norm_num [Value.toBytes, Value.bytes, Value.byteAt, FloatFmt.bytes]

/-- A performed output byte is the selected byte
of the BF16 normalization of the indicated word of an actual 64-word Tensor Memory load. -/
theorem of_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {address : Nat} {sp : TensorStore.Spec} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomplete : Complete L X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorStoreIssue (g, i) address sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .tmaStore j) (s : OutputSlot) {dst : Acc} {out : Byte}
    (hw : X.MemWrites (.async (g, i) (.write (.store s.1.val s.2.1.val s.2.2.val))) dst [out]) :
    ∃ (w p : Nat) (d0 : D) (e : Event) (words : List Value),
      ctaOf L w = ctaOf L g ∧ head L w = s.2.1.val ∧ Wg0.half L w = warpOf L g ∧
      Frame.stateAt (Machine.code P L) X w p = some (some (.wg0 d0)) ∧ d0.site = .oLoad j ∧
      X.get (w, p) = some e ∧ e.kind = .tc (.ld (64 * j.val) words .s32x32b) ∧
      words.length = 64 ∧
      out = (.float .bf16 (oScale P L w d0 * outputReal words s.1.val), s.2.2.val) := by
  obtain ⟨w, b, ds, a, k, sub, pos, hst, hsite, hsub, hh, hwr, hloc, hval⟩ :=
    Protocol.OutputValues.of_write hpre hX hcomplete hs ht hi hd hj s hw
  have hwg := Frame.lt_of_get hX hwr.choose_spec
  obtain ⟨hhalf, _, hwloc⟩ :=
    Wg0StageUnique.writeByteAddress hpre hX (hs w hwg).machine hwr hst hsite pos
  rw [hsub] at hwloc
  have hread := hi.choose_spec
  have hg := Frame.lt_of_get hX hread
  have hwarp := Wg0OutputControl.outputWarp hX (hs g hg).machine hread hd hj
  let x := 8 * k.val + 2 * sub.val + pos.val / 2
  have hx : x < 64 := by
    have hk := k.isLt
    have hsb := sub.isLt
    have hp := pos.isLt
    unfold x
    omega
  have hcta := congrArg Loc.cta (hwloc.symm.trans hloc)
  have haddr := congrArg Loc.addr (hwloc.symm.trans hloc)
  change L.sharedBase + (stageOff (head L w) (tmaX j.val (Wg0.half L w) + x) + pos.val % 2) =
    L.sharedBase + (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val) at haddr
  obtain ⟨_, hc, hp⟩ := stageByte_injective (head_lt L w) s.2.1.isLt
    (by omega) s.2.2.isLt (Nat.add_left_cancel haddr)
  have hwarpEq : Wg0.half L w = warpOf L g := by
    have hslot := s.1.isLt
    unfold tmaX at hc
    omega
  have hindex : 2 * (4 * k.val + sub.val) + pos.val / 2 = s.1.val := by
    rw [hwarpEq] at hc
    have he := Nat.add_left_cancel hc
    unfold x at he
    omega
  obtain ⟨p, _, d0, e, words, h0, hload, he, hekind, hlen, hfields⟩ :=
    Wg0OutputPayload.at_stage hpre hX hwg (hs w hwg).machine hst hsite
  refine ⟨w, p, d0, e, words, hcta, hh, hwarpEq, h0, hload, he, hekind, hlen, ?_⟩
  unfold stagePair at hval
  rw [pair_byte (fun n => oScale P L w ds * outputReal ds.oWords n), hindex, hp] at hval
  rw [hfields] at hval
  exact Option.some.inj hval

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputPayload
