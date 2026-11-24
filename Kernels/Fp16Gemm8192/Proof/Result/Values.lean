-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Result.ValuesMma

@[expose] public section

/-! # The values the output's TMA stores write

A consumer's TMA store of slice `s` writes at slot `(x, y, z)` the byte it read there
(`TensorStore.CopyOk`), the byte its group's thread of row `y` wrote in the slice
(`StagingValues`): byte `z` of the half of accumulator entry `32 s + x` (`storeWord_byte`,
`ThreadFacts.cons_slice_values`), since the load of the entry's chunk returned single-precision
floats (`LoadWords`). That entry is a word of the thread's load of its tile, which
reads the producer's last MMA of the task of the tile (`LoadSources`,
`ThreadFacts.acc_commit_last`): the output barrier counts make the load's tile the TMA store's task
(`ThreadFacts.cons_tma_epoch`), whose tile the TMA store's thread holds (`ThreadFacts.store_tile`).
The last MMA of a task leaves the full dot product (`mma_value`), a single-precision float the load
returns as it is (`TcMma.LoadReadOk`), and its half is the half-precision dot product
(`output_values`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Flow TcMma

noncomputable section

namespace Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Byte `2 (x % 2) + z` of the word a staging store of element `(x / 8, x / 2 % 4)` of slice `s`
writes is byte `z` of the half of accumulator entry `32 s + x`, when that entry and the other one of
its pair are single-precision floats. -/
theorem storeWord_byte (acc : Nat → Value) (s : Nat) {x z : Nat} (hz : z < 2)
    (hf : ∀ i, i / 2 = x / 2 → ∃ r, acc (32 * s + i) = .float .f32 r) :
    (Consumer.storeWord acc s (x / 8) (x / 2 % 4)).toBytes[2 * (x % 2) + z]? =
      some ((Flow.half (acc (32 * s + x))).byteAt z) := by
  have hv : ∀ i, i / 2 = x / 2 → ∃ r, valFloat .f32 (acc (32 * s + i)) = .ok r := fun i hi => by
    obtain ⟨r, hr⟩ := hf i hi
    exact ⟨r, by rw [hr]; simp [valFloat, pure, Except.pure]⟩
  obtain ⟨r0, h0⟩ := hv (8 * (x / 8) + 2 * (x / 2 % 4)) (by omega)
  obtain ⟨r1, h1⟩ := hv (8 * (x / 8) + 2 * (x / 2 % 4) + 1) (by omega)
  have hw : Consumer.storeWord acc s (x / 8) (x / 2 % 4) =
      .pair (Flow.half (acc (32 * s + 8 * (x / 8) + 2 * (x / 2 % 4))))
        (Flow.half (acc (32 * s + 8 * (x / 8) + 2 * (x / 2 % 4) + 1))) := by
    rw [show 32 * s + (8 * (x / 8) + 2 * (x / 2 % 4)) =
      32 * s + 8 * (x / 8) + 2 * (x / 2 % 4) by omega] at h0
    rw [show 32 * s + (8 * (x / 8) + 2 * (x / 2 % 4) + 1) =
      32 * s + 8 * (x / 8) + 2 * (x / 2 % 4) + 1 by omega] at h1
    exact Flow.cvtPairV_of_valFloat h1 h0
  have h2 : ∀ v : Value, (Flow.half v).bytes = 2 := fun v => rfl
  have hlen : (Consumer.storeWord acc s (x / 8) (x / 2 % 4)).bytes = 4 := by
    rw [hw]; simp only [Value.bytes, h2]
  rw [Value.toBytes, List.getElem?_map, hlen, List.getElem?_range (by omega), hw]
  simp only [Option.map_some, Option.some.injEq, Value.byteAt, h2]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp only [h] <;> split_ifs with hc
  · congr 3 <;> omega
  · omega
  · omega
  · congr 3 <;> omega

/-- A single-precision word contains only itself. -/
theorem word_f32 {r : ℝ} {w : Value} (h : WordContains (.float .f32 r) w) : w = .float .f32 r := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · simp [Value.bytes, FloatFmt.bytes] at h

set_option maxHeartbeats 8000000 in
/-- **The output values.** Every byte a consumer's TMA store writes is its element's byte of the
half-precision dot product. -/
theorem output_values (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X)
    (hub : ∀ g j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) (hsv : StagingValues L X)
    (hls : LoadSources L X) (hacs : MmaAccSources L X) (hov : OperandValues P L X)
    (hag : AllResponsesAgree L X) (hw : TmemWords L X) (hsg : SyncGuarded L kernel X)
    (hlw : LoadWords X) :
    OutputValues P L X := by
  intro h k pc a sp c s x y z o b he hσ hs hx hy hz ho hwb
  have hh := Frame.lt_of_get hX he
  -- the store writes the byte it read
  obtain ⟨⟨addr, pci, hiss⟩, -, hcopy⟩ := hX.store (h, k) o ho
  have hosp : o.spec = sp := by
    have h1 := Option.some.inj (he.symm.trans hiss)
    simp only [Event.mk.injEq, Kind.tensorStore.injEq] at h1
    exact h1.2.2.symm
  obtain ⟨s0, hs0, -, hcm, hcn, -, hred, -, htile⟩ := ht.store_tile hh he hσ
  rw [hs] at hs0
  cases hs0
  have hrb : TensorStore.readByte o x y z = some b := by
    unfold TensorStore.writeByte at hwb
    unfold TensorStore.readByte
    obtain ⟨slot, hsl, hw'⟩ := Option.bind_eq_some_iff.mp hwb
    obtain ⟨-, src, hrd, hbs⟩ := hcopy.writes slot b hw'
    rw [hsl]
    simp only [Option.bind_some, hrd, hbs (by rw [hosp]; exact hred)]
  -- the staging store of the row's thread
  obtain ⟨g', i', c', pc', a', bs, hg', hi', hσ', hs', hob, hwr, hbyte⟩ :=
    hsv h k pc a sp c s x y z o b he hσ hs hx hy hz ho hrb
  have hg'l := Frame.lt_of_get hX hwr
  obtain ⟨hbytes, hloads, hO'⟩ := ht.cons_slice_values hg'l (hub g') hi' hσ' hs'
  obtain ⟨pcw, aw, bsw, hwget, hbsw⟩ := hbytes (4 * (x / 8) + x / 2 % 4) (by omega)
  rw [hwr] at hwget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hwget
  obtain ⟨-, -, rfl⟩ := hwget
  -- the entry and the other one of its pair are words of the load of their chunk
  have hf : ∀ i, i / 2 = x / 2 → ∃ r, c'.acc (32 * s.val + i) = .float .f32 r := by
    intro i hi
    obtain ⟨_, pcl, vals, -, hld, hvals, -⟩ := hloads ((32 * s.val + x) / 16) (by omega)
    have hv := hvals ((32 * s.val + i) % 16) (by omega)
    rw [show 16 * ((32 * s.val + x) / 16) + (32 * s.val + i) % 16 = 32 * s.val + i by omega]
      at hv
    exact hlw _ _ _ _ ⟨pcl, hld⟩ _ (List.mem_of_getElem? hv)
  rw [hbsw, show (4 * (x / 8) + x / 2 % 4) / 4 = x / 8 by omega,
    show (4 * (x / 8) + x / 2 % 4) % 4 = x / 2 % 4 by omega, storeWord_byte _ _ hz hf] at hbyte
  obtain rfl := (Option.some.inj hbyte).symm
  -- the load of the entry's chunk
  obtain ⟨kl, pcl, vals, hkl, hld, hvals, harr⟩ := hloads ((32 * s.val + x) / 16) (by omega)
  have hw16 : (32 * s.val + x) % 16 < vals.length := by
    have := hvals ((32 * s.val + x) % 16) (by omega)
    exact (List.getElem?_eq_some_iff.mp this).1
  obtain ⟨g, jc, mm, pcm, dst, sp2, acc2, mask2, cell, value, hgl, hgc, hgw, hjc, hσc, hsc, hcnt,
    hem, hwc, hdone, hrs⟩ := hls g' kl _ vals .s32x32b _ ⟨pcl, hld⟩ hw16
  obtain ⟨hj2, ⟨m2, hσ2, hs2⟩, -, -, hMc⟩ := ht.acc_commit_last hgl hjc hσc hsc
  -- the load's tile is the TMA store's task
  obtain ⟨hOh, hPh⟩ := ht.cons_tma_epoch hh hσ hs
  have hblock := hpre.block
  simp only [Consumer.tidOf] at hO' harr hld hOh hPh hg' hwc
  have hcta : g' / L.block = h / L.block := by rw [hg', hblock]; omega
  have htid' : g' % L.block = 128 * (h % L.block / 32 / 4) + y := by
    rw [hg', hblock]; omega
  -- the task of the load's tile
  have hE : mmaCount L g ((X.tr g).take (jc - 2)) / 128 =
      okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take k) - 1 ∧
      mmaCount L g ((X.tr g).take (jc - 2)) % 128 = 127 := by
    constructor <;> omega
  have htt : TaskTile L X (g / L.block / 2) (mmaCount L g ((X.tr g).take (jc - 2)) / 128)
      c.m c.n :=
    ⟨h, k, hh, by omega, (List.getElem?_eq_some_iff.mp he).1.le, by rw [hE.1]; exact htile⟩
  -- the last MMA's value
  have hcol : 256 * (g' % L.block / 32 / 4) + 16 * ((32 * s.val + x) / 16) -
      256 * (g' % L.block / 32 / 4) + (32 * s.val + x) % 16 = 32 * s.val + x := by omega
  rw [hcol] at hwc
  have hres := mma_value hX ht hov hag hacs (jc - 2) g pcm dst sp2 acc2 mask2 m2 3 3 hem hσ2 hs2
    hdone c.m c.n htt (128 * (g' / L.block % 2) + g' % L.block % 128) (32 * s.val + x) cell
    (by omega) (by omega) hwc
  have hrow' : accRow c.m (g % L.block / 32) (128 * (g' / L.block % 2) + g' % L.block % 128) =
      Consumer.outRow L h c y := by
    have hrw := ht.role_warp hh (List.getElem?_eq_some_iff.mp he).1.le hσ
    simp only [roleWarp] at hrw
    simp only [accRow, Consumer.outRow, Consumer.tidOf, outputRow]
    omega
  have hcol' : 256 * c.n + (32 * s.val + x) = Consumer.outCol c s x := by
    simp only [Consumer.outCol, outputCol]
    omega
  have hn : 16 * (4 * (mmaCount L g ((X.tr g).take (jc - 2)) % 128) + (3 : Fin 4).val + 1) =
      8192 := by
    rw [hE.2]; rfl
  rw [hrow', hcol', hn] at hres
  have hV := wrote_functional hX hsg hw.1 (.inl hres) hrs.2.2
  obtain ⟨word, hword, hcont⟩ := hX.tcRead.1 _ _ _ _ _ _ _ _ ⟨pcl, hld⟩ hrs.1 hrs.2.1 hrs.2.2
  rw [← hV] at hcont
  have hw1 := word_f32 hcont
  have hacc := hvals ((32 * s.val + x) % 16) (by omega)
  rw [hword, hw1] at hacc
  have hidx : 16 * ((32 * s.val + x) / 16) + (32 * s.val + x) % 16 = 32 * s.val + x := by omega
  rw [hidx] at hacc
  rw [← Option.some.inj hacc, Flow.half_of (x := prefixDot P _ _ _) rfl]
  rfl

end Result

end
end PTX.Kernels.Fp16Gemm8192.Proof
