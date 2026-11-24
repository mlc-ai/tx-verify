-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueSelect
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads
public import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0}

theorem previousPrefixTemplate (hp : Pre p l m) (g : Nat) (t : TState) (lane sum : Nat)
    (hl : lane < 32) (hpc : t.pc = 2894) (hf : t.fault = none)
    (hLane : t.regs 2353 = some (b32 lane)) (hv : t.regs 7221 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) lane 31
      (fun value _ => next (setReg t 2354 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2894) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 2354 none (.reg 7221) (.reg 2353)
    (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  simp [shflTmpl, readValue, readReg, hv, hLane, hBlock, Value.bytes, b32, readBits,
    bind, Except.bind, pure, Except.pure, truncBits_ofNat h32 (by decide), toNat_ofNat_lt h64]
  rfl

theorem scalePreviousPrefix (l : Launch) (g : Nat) {sum heads : Nat}
    (hs : sum < 2 ^ 32) (hh : heads < 2 ^ 32) (hwork : sum * heads < 2 ^ 32) :
    Seg kernel [] l g 1 2895 [(2354, b32 sum), (7138, b32 heads)] 2896
      [(7225, b32 (sum * heads))] := by
  intro t ht
  seg_fp ht using
    simp only [b32, truncBits_ofNat hs (by decide), truncBits_ofNat hh (by decide),
      ← BitVec.ofNat_mul, truncBits_ofNat hwork (by decide)]

private theorem kernelName : kernel.name =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at_\
    _tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o\
    1i64div8_0" := rfl

private theorem decimal19 : toString (19 : Nat) = "19" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
    Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
    Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
  rfl

private theorem decimal22 : toString (22 : Nat) = "22" := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
  simp only [show (22 / 10 : Nat) = 2 by decide, show (22 % 10 : Nat) = 2 by decide,
    Nat.repr_of_lt (n := 2) (by decide), Nat.digitChar_eq_two.mpr rfl]
  rfl

private theorem rawScalarLoad {l : Launch} {g pc r n : Nat} {t : TState}
    {F : List (Nat × Value)} {name : String}
    (ht : At t pc F) (hp : l.params name = some (BitVec.ofNat 64 n)) (hn : n < 2 ^ 32)
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load
        space := some .param
        sem := .weak
        elem := .int .b 32
        addr := ⟨.param name false, 0⟩
        dsts := [some r] }⟩) :
    run kernel [] l g 1 t = some (next (setReg t r (b32 n))) := by
  apply run_local hc rfl ht
  rw [execLocalA_nil, execLocal_mem rfl]
  simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hp,
    DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hn (by decide)]
  rfl

set_option maxRecDepth 3000 in
private theorem loadScalar19 {l : Launch} {g pc r n : Nat} {t : TState}
    {F : List (Nat × Value)}
    (ht : At t pc F) (hp : l.params (param 19) = some (BitVec.ofNat 64 n)) (hn : n < 2 ^ 32)
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load
        space := some .param
        sem := .weak
        elem := .int .b 32
        addr := ⟨.param
          ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_obje\
          ct_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf\
          16gmemalign16o1i64div8_0_param_19") false, 0⟩
        dsts := [some r] }⟩) :
    run kernel [] l g 1 t = some (next (setReg t r (b32 n))) := by
  unfold param at hp
  rw [kernelName, decimal19] at hp
  exact rawScalarLoad (l := l) (g := g) (pc := pc) (r := r) ht hp hn hc

set_option maxRecDepth 3000 in
/-- Load the cache and batch parameters before the selected request's tile-count shuffle. -/
theorem selectionParameters (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    (ht : At t 2896 F) (hF : ∀ pair ∈ F, pair.1 ≠ 7155 ∧ pair.1 ≠ 7146) :
    ∃ u, run kernel [] l g 2 t = some u ∧
      At u 2898 ((7146, b32 p.batch) :: (7155, b32 800) :: F) := by
  let v := next (setReg t 7155 (b32 800))
  let u := next (setReg v 7146 (b32 p.batch))
  obtain ⟨hBatch, h19⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  obtain ⟨hCap, h22⟩ := hp.values (22, 800) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at h19
  change l.params (param 22) = some (BitVec.ofNat 64 800) at h22
  unfold param at h22
  rw [kernelName, decimal22] at h22
  have hRun1 : run kernel [] l g 1 t = some v :=
    rawScalarLoad (r := 7155) ht h22 hCap Flow.code_2896
  have hv : At v 2897 ((7155, b32 800) :: F) := ht.set (fun pair hm => (hF pair hm).1)
  have hRun2 : run kernel [] l g 1 v = some u :=
    loadScalar19 (r := 7146) hv h19 hBatch Flow.code_2897
  have hRemain : ∀ pair ∈ ((7155, b32 800) :: F), pair.1 ≠ 7146 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | he
    · omega
    · exact (hF pair he).2
  exact ⟨u, run_comp hRun1 hRun2, hv.set hRemain⟩

theorem writebackBatchInput (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    {lane : Nat} (hLane : lane < 32) (ht : At t 2949 F)
    (hF : ∀ pair ∈ F, pair.1 ≠ 7147 ∧ pair.1 ≠ 307) (hMember : (1201, b32 lane) ∈ F) :
    ∃ u, run kernel [] l g 2 t = some u ∧
      At u 2951 ((307, .pred (decide (p.batch < lane))) :: (7147, b32 p.batch) :: F) := by
  let v := next (setReg t 7147 (b32 p.batch))
  let pred : Value := .pred (decide (p.batch < lane))
  let u := next (setReg v 307 pred)
  obtain ⟨hBatch, h19⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  have hRun1 : run kernel [] l g 1 t = some v :=
    loadScalar19 (r := 7147) ht h19 hBatch Flow.code_2949
  have hv : At v 2950 ((7147, b32 p.batch) :: F) := ht.set (fun pair hm => (hF pair hm).1)
  have hrB : v.regs 7147 = some (b32 p.batch) := holds_mem hv.2.2.2.2 (by simp)
  have hrL : v.regs 1201 = some (b32 lane) := holds_mem hv.2.2.2.2 (by simp [hMember])
  have h32 : lane < 2 ^ 32 := by omega
  have h31 : lane < 2 ^ 31 := by omega
  have hb31 := hp.shape.2.1
  have hSigned (n : Nat) (hn : n < 2 ^ 31) : toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    have hN64 : n < 2 ^ 64 := by omega
    have hN32 : n < 2 ^ 32 := by omega
    simp only [toSigned, toNat_ofNat_lt hN64, Nat.mod_eq_of_lt hN32, ite_eq_left hn]
  have hRun2 : run kernel [] l g 1 v = some u := by
    apply run_local Flow.code_2950 rfl hv
    rw [execLocalA_nil, execLocal_int rfl]
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, hrB, hrL, b32, compare,
      Option.getD_some, truncBits_ofNat h32 (by decide), truncBits_ofNat hBatch (by decide),
      hSigned lane h31, hSigned p.batch hb31, Int.ofNat_lt, gt_iff_lt,
      bind, Except.bind, pure, Except.pure, pred, u]
  have hRemain : ∀ pair ∈ ((7147, b32 p.batch) :: F), pair.1 ≠ 307 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | he
    · omega
    · exact (hF pair he).2
  exact ⟨u, run_comp hRun1 hRun2, hv.set hRemain⟩

/-- The selected-request address calculation preserves the scheduler frame. -/
theorem selectedCuQAddress (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    {batch : Nat} (hb : batch < p.batch) (ht : At t 2951 F)
    (hF : ∀ pair ∈ F, pair.1 ≠ 7866 ∧ pair.1 ≠ 7867) (hi : (7228, b32 batch) ∈ F)
    (ha : (7502, b64 p.cuQBase) ∈ F) :
    ∃ u, run kernel [] l g 2 t = some u ∧
      At u 2953 ((7867, b64 (p.cuQBase + 4 * batch)) :: F) := by
  let v := next (setReg t 7866 (b64 (4 * batch)))
  let u := next (setReg v 7867 (b64 (p.cuQBase + 4 * batch)))
  have hv : At v 2952 ((7866, b64 (4 * batch)) :: F) := ht.set (fun pair hm => (hF pair hm).1)
  have hu : At u 2953 ((7867, b64 (p.cuQBase + 4 * batch)) :: F) := by
    have hv' : At v 2952 F := hv.mono hv.2.2.2.2.2
    exact hv'.set (fun pair hm => (hF pair hm).2)
  exact ⟨u, prepareCuQAddress hp g t hb ht.1 ht.2.2.2.1
    (holds_mem ht.2.2.2.2 hi) (holds_mem ht.2.2.2.2 ha), hu⟩

/-- Each selected-request endpoint load accepts the bytes of that cuQ word and frames the other
registers. -/
theorem selectedCuQLoad (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    {batch : Nat} (hb : batch < p.batch) (endpoint : Fin 2) (ht : At t (2953 + endpoint.val) F)
    (hF : ∀ pair ∈ F, pair.1 ≠ 2392 + endpoint.val) (ha : (7867, b64 (p.cuQBase + 4 * batch)) ∈ F) :
    let v := b32 (p.qOffset (batch + endpoint.val))
    let a : Acc := { loc := globalLoc (p.cuQBase + 4 * (batch + endpoint.val)), size := 4 }
    let bs := v.toBytes.map some
    ∃ u, EStep kernel [] l g t ⟨2953 + endpoint.val, .rd a bs⟩ (some u) ∧
      At u (2953 + endpoint.val + 1) ((2392 + endpoint.val, v) :: F) := by
  dsimp only
  let v := b32 (p.qOffset (batch + endpoint.val))
  let u := next (setReg t (2392 + endpoint.val) v)
  have hRebuild := rebuild_scalar (v := v) (show 0 < 4 by decide) rfl
  have hLoad : afterLoad t [2392 + endpoint.val] (v.toBytes.map some) = u := by
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild]
    simp [next, u, ht.2.1, ht.2.2.1, setReg]
  refine ⟨u, ?_, ht.set hF⟩
  refine ⟨_, cuQTemplate hp g t hb endpoint ht.1 ht.2.2.2.1 ht.2.1
    (holds_mem ht.2.2.2.2 ha), ?_⟩
  exact ⟨v.toBytes.map some, by simp [Value.toBytes, v, b32, Value.bytes],
    by rw [ht.1], congrArg some hLoad.symm⟩

/-- The two endpoint words determine the row origin and the first parity without touching the
drain-scan frame. -/
theorem selectedWritebackRow (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    {batch tile : Nat} (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (ht : At t 2955 F) (hF : ∀ pair ∈ F, pair.1 ≠ 2394 ∧ pair.1 ≠ 2395 ∧ pair.1 ≠ 7229)
    (hi : (7226, b32 (2 ^ 30 + 256 * tile)) ∈ F) (ha : (2392, b32 (p.qOffset batch)) ∈ F)
    (he : (2393, b32 (p.qOffset (batch + 1))) ∈ F) :
    ∃ u, run kernel [] l g 3 t = some u ∧
      At u 2958 ((7229, b32 0) :: (2395, b32 (2 ^ 30 - p.qLength batch + 256 * tile)) :: F) := by
  let u₁ := next (setReg t 2394 (b32 (2 ^ 30 + 256 * tile + p.qOffset batch)))
  let u₂ := next (setReg u₁ 2395 (b32 (2 ^ 30 - p.qLength batch + 256 * tile)))
  let u₃ := next (setReg u₂ 7229 (b32 0))
  have h₁ : At u₁ 2956 ((2394, b32 (2 ^ 30 + 256 * tile + p.qOffset batch)) :: F) :=
    ht.set (fun pair hm => (hF pair hm).1)
  have h₂ : At u₂ 2957 ((2395, b32 (2 ^ 30 - p.qLength batch + 256 * tile)) :: F) := by
    exact (h₁.mono h₁.2.2.2.2.2).set (fun pair hm => (hF pair hm).2.1)
  have h₃ : At u₃ 2958 _ := h₂.set (by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · exact (hF pair hm).2.2)
  exact ⟨u₃, prepareFirstRow hp g t hb hTile ht.1 ht.2.2.2.1
      (holds_mem ht.2.2.2.2 hi) (holds_mem ht.2.2.2.2 ha) (holds_mem ht.2.2.2.2 he), h₃⟩

/-- The selected cuQ read observes its launch word when no global write covers it. -/
theorem selectedCuQBytes {X : Execution} {A : List Assumption} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) {g i batch : Nat} (hb : batch < p.batch) (endpoint : Fin 2)
    (bs : List (Option Byte))
    (he : X.get (g, i) = some ⟨2953 + endpoint.val,
      .rd { loc := globalLoc (p.cuQBase + 4 * (batch + endpoint.val)), size := 4 } bs⟩)
    (hNoWrite : ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((globalLoc (p.cuQBase + 4 * (batch + endpoint.val))).at k)) :
    bs = (b32 (p.qOffset (batch + endpoint.val))).toBytes.map some := by
  let a : Acc := { loc := globalLoc (p.cuQBase + 4 * (batch + endpoint.val)), size := 4 }
  have hread : X.MemReads (.thread (g, i)) a bs := Or.inl ⟨_, he⟩
  have hindex : batch + endpoint.val ≤ p.batch :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_of_lt_succ endpoint.isLt) _) hb
  have hValue := hp.cuQ (batch + endpoint.val) hindex
  exact hX.launch_value hread rfl hNoWrite hValue

def selectScratch : List Nat :=
  [7147, 307, 7866, 7867, 2392, 2393, 2394, 2395, 7229]

/-- From a selected tile, the two cuQ reads and the row arithmetic reach the first ready poll.
The scheduler facts that are outside the scratch registers are retained for the drain scan. -/
theorem selectedTileToReady (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    {batch tile lane : Nat} (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (hLane : lane < 32) (ht : At t 2949 F) (hF : ∀ pair ∈ F, pair.1 ∉ selectScratch)
    (hl : (1201, b32 lane) ∈ F) (hi : (7228, b32 batch) ∈ F) (ha : (7502, b64 p.cuQBase) ∈ F)
    (hr : (7226, b32 (2 ^ 30 + 256 * tile)) ∈ F) :
    ∃ u v w z, run kernel [] l g 4 t = some u ∧
      EStep kernel [] l g u
        ⟨2953, .rd { loc := globalLoc (p.cuQBase + 4 * batch), size := 4 }
          ((b32 (p.qOffset batch)).toBytes.map some)⟩ (some v) ∧
      EStep kernel [] l g v
        ⟨2954, .rd { loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4 }
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ (some w) ∧
      w.pc = 2955 ∧ run kernel [] l g 3 w = some z ∧
      At z 2958 ([(7229, b32 0), (2395, b32 (2 ^ 30 - p.qLength batch + 256 * tile)),
        (2393, b32 (p.qOffset (batch + 1))), (307, .pred (decide (p.batch < lane))),
        (7147, b32 p.batch)] ++ F) := by
  let F₁ := (307, Value.pred (decide (p.batch < lane))) :: (7147, b32 p.batch) :: F
  let F₂ := (7867, b64 (p.cuQBase + 4 * batch)) :: F₁
  let F₃ := (2392, b32 (p.qOffset batch)) :: F₂
  let F₄ := (2393, b32 (p.qOffset (batch + 1))) :: F₃
  have hApart {pair : Nat × Value} (hm : pair ∈ F) {r : Nat} (hR : r ∈ selectScratch) :
      pair.1 ≠ r := fun e => hF pair hm (e ▸ hR)
  obtain ⟨s, hs, hS⟩ := writebackBatchInput hp g hLane ht
    (fun pair hm => ⟨hApart hm (by decide), hApart hm (by decide)⟩) hl
  have hAddressFrame : ∀ pair ∈ F₁, pair.1 ≠ 7866 ∧ pair.1 ≠ 7867 := by
    intro pair hm
    simp only [F₁, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm <;>
      first | exact ⟨hApart hm (by decide), hApart hm (by decide)⟩ | simp
  obtain ⟨u, hu, hU⟩ := selectedCuQAddress hp g hb hS hAddressFrame
    (by simp [hi]) (by simp [ha])
  have hStartFrame : ∀ pair ∈ F₂, pair.1 ≠ 2392 := by
    intro pair hm
    simp only [F₂, F₁, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | hm <;> first | exact hApart hm (by decide) | simp
  obtain ⟨v, hv, hV⟩ := selectedCuQLoad hp g hb 0 hU hStartFrame (by simp)
  have hEndFrame : ∀ pair ∈ F₃, pair.1 ≠ 2393 := by
    intro pair hm
    simp only [F₃, F₂, F₁, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | hm <;> first | exact hApart hm (by decide) | simp
  obtain ⟨w, hw, hW⟩ := selectedCuQLoad hp g hb 1 hV hEndFrame (by simp)
  have hRowFrame : ∀ pair ∈ F₄, pair.1 ≠ 2394 ∧ pair.1 ≠ 2395 ∧ pair.1 ≠ 7229 := by
    intro pair hm
    simp only [F₄, F₃, F₂, F₁, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | hm <;> first
      | exact ⟨hApart hm (by decide), hApart hm (by decide), hApart hm (by decide)⟩
      | simp
  obtain ⟨z, hz, hZ⟩ := selectedWritebackRow hp g hb hTile hW hRowFrame
    (by
      repeat' apply List.mem_cons_of_mem
      exact hr) (by simp) (by simp)
  refine ⟨u, v, w, z, run_comp hs hu, ?_, hw, hW.1, hz, ?_⟩
  · simpa only [Fin.val_zero, Nat.add_zero] using hv
  have h := hZ.2.2.2.2
  exact hZ.mono ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
