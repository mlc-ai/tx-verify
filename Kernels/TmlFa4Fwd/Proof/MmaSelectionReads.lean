-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaTileCoordinates
import Kernels.TmlFa4Fwd.Proof.MmaModel
import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations
import Kernels.TmlFa4Fwd.Flow.Code.Part032
import Lemmas.Flow.ParamObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

/-- Only nonfirst requests need the preceding lane's inclusive prefix. -/
theorem selectedPrefixBranch {l : Launch} {g n : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t 2055 F)
    (hPred : t.regs 363 = some (.pred (decide (n = 0)))) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (if n = 0 then 2059 else 2056) F := by
  obtain ⟨u, hRun, hAt⟩ :=
    run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_2055 (decide (n = 0)) ht hPred (by simp)
  exact ⟨u, localRun (by decide) (by decide) ht.1 (by decide) hRun,
    by simpa only [decide_eq_true_eq] using hAt⟩

variable {p : Params} {l : Launch} {m : Mem0}

private theorem selectionShuffle (hp : Pre p l m) {g pc dst src idx lane count : Nat} {t : TState}
    (hpc : t.pc = pc) (hf : t.fault = none) (hLane : lane < 32)
    (hIndex : t.regs idx = some (b32 lane)) (hSource : t.regs src = some (b32 count))
    (hCode : kernel.code[pc]? = some ⟨none, .warp
      { kind := .shfl .idx, ty := some (.int .b 32), dsts := [some dst],
        srcs := [.reg src, .reg idx, .imm 31], mask := some (.imm (-1)) }⟩) (hLo : 1904 ≤ pc)
    (hHi : pc < 2768) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 count) lane 31
      (fun value _ => next (setReg t dst value))) := by
  rw [out_eq_core (by simpa only [hpc] using hLo) (by simpa only [hpc] using hHi),
    out_event hf (by simpa only [hpc] using hCode) rfl rfl]
  change Out.ev (shflTmpl l g t .idx dst none (.reg src) (.reg idx) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  simp [shflTmpl, readValue, readReg, hSource, hIndex, hBlock, Value.bytes, b32, readBits,
    bind, Except.bind, pure, Except.pure, truncBits_ofNat h32 (by decide), toNat_ofNat_lt h64]
  rfl

/-- The preceding lane's inclusive prefix is the selected request's exclusive group prefix. -/
theorem selectedPreviousPrefixShuffle (hp : Pre p l m) {g lane count : Nat} {t : TState}
    (hpc : t.pc = 2057) (hf : t.fault = none) (hLane : lane < 32)
    (hIndex : t.regs 2501 = some (b32 lane)) (hSource : t.regs 7197 = some (b32 count)) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 count) lane 31
      (fun value _ => next (setReg t 2502 value))) :=
  selectionShuffle hp hpc hf hLane hIndex hSource Flow.code_2057 (by decide) (by decide)

/-- The selected lane broadcasts its query tile count to the MMA warp. -/
theorem selectedRequestTilesShuffle (hp : Pre p l m) {g lane count : Nat} {t : TState}
    (hpc : t.pc = 2061) (hf : t.fault = none) (hLane : lane < 32)
    (hIndex : t.regs 1187 = some (b32 lane)) (hSource : t.regs 7196 = some (b32 count)) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 count) lane 31
      (fun value _ => next (setReg t 2503 value))) :=
  selectionShuffle hp hpc hf hLane hIndex hSource Flow.code_2061 (by decide) (by decide)

private theorem selectionShuffleStep {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j pc ordinal lane peerIndex dst : Nat} {t : TState} {F : List (Nat × Value)}
    {src source recv peerRecv : Value} {ok peerOk : Bool}
    (ht : At t pc F) (hFresh : ∀ pair ∈ F, pair.1 ≠ dst) (hLane : lane < 32)
    (hOut : out kernel Assumptions.all l g t =
      .ev (.shfl .idx src lane 31 (fun value _ => next (setReg t dst value))))
    (he : X.get (g, i) = some ⟨pc, .shfl .idx src lane 31 recv ok⟩)
    (hk : X.ShflK (g, i) ordinal)
    (hPeer : X.get (g - laneOf l g + lane, j) =
      some ⟨pc, .shfl .idx source peerIndex 31 peerRecv peerOk⟩)
    (hPeerK : X.ShflK (g - laneOf l g + lane, j) ordinal)
    (hLive : ¬ ShflExited X (g - laneOf l g + lane) ordinal) :
    ∃ u, EStep kernel Assumptions.all l g t ⟨pc, .shfl .idx src lane 31 recv ok⟩ (some u) ∧
      At u (pc + 1) ((dst, source) :: F) := by
  have hRecv := (selectedIndexValue hX hLane he hk hPeer hPeerK hLive).1
  refine ⟨next (setReg t dst recv), ⟨_, hOut, recv, ok, by rw [ht.1], rfl⟩, ?_⟩
  rw [hRecv]
  exact ht.set hFresh

/-- An observed preceding-prefix shuffle returns the exclusive prefix of the selected request. -/
theorem selectedPreviousPrefixStep {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i j ordinal first batch peerIndex : Nat}
    {t : TState} {F : List (Nat × Value)} {recv peerRecv : Value} {ok peerOk : Bool}
    (hFirst : first < batch) (hGroup : batch < first + 31) :
    let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
    let lane := batch - first - 1
    let ev := ⟨2057, .shfl .idx (b32 (part (laneOf l g))) lane 31 recv ok⟩
    At t 2057 F → t.regs 2501 = some (b32 lane) →
    t.regs 7197 = some (b32 (part (laneOf l g))) →
    (∀ pair ∈ F, pair.1 ≠ 2502) →
    X.get (g, i) = some ev → X.ShflK (g, i) ordinal →
    X.get (g - laneOf l g + lane, j) =
      some ⟨2057, .shfl .idx (b32 (part lane)) peerIndex 31 peerRecv peerOk⟩ →
    X.ShflK (g - laneOf l g + lane, j) ordinal →
    ¬ ShflExited X (g - laneOf l g + lane) ordinal →
    ∃ u, EStep kernel Assumptions.all l g t ev (some u) ∧
      At u 2058 ((2502,
        b32 (∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane)) :: F) := by
  dsimp only
  intro ht hIdx hSource hFresh he hk hPeer hPeerK hLive
  have hLane : batch - first - 1 < 32 := by omega
  have hCount : batch - first - 1 + 1 = batch - first := by omega
  have hOut := selectedPreviousPrefixShuffle hp (g := g) ht.1 ht.2.2.2.1 hLane hIdx hSource
  simpa only [hCount] using selectionShuffleStep hX ht hFresh hLane hOut he hk hPeer hPeerK hLive

/-- An observed request shuffle supplies the tile count for the real MMA coordinate segment. -/
theorem selectedRequestTilesStep {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i j ordinal first batch peerIndex : Nat}
    {t : TState} {F : List (Nat × Value)} {recv peerRecv : Value} {ok peerOk : Bool}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch) :
    let lane := batch - first
    let ev := ⟨2061, .shfl .idx (b32 (groupLaneTiles p first (laneOf l g))) lane 31 recv ok⟩
    At t 2061 F → t.regs 1187 = some (b32 lane) →
    t.regs 7196 = some (b32 (groupLaneTiles p first (laneOf l g))) →
    (∀ pair ∈ F, pair.1 ≠ 2503) →
    X.get (g, i) = some ev → X.ShflK (g, i) ordinal →
    X.get (g - laneOf l g + lane, j) =
      some ⟨2061, .shfl .idx (b32 (groupLaneTiles p first lane)) peerIndex 31 peerRecv peerOk⟩ →
    X.ShflK (g - laneOf l g + lane, j) ordinal →
    ¬ ShflExited X (g - laneOf l g + lane) ordinal →
    ∃ u, EStep kernel Assumptions.all l g t ev (some u) ∧
      At u 2062 ((2503, b32 (requestTiles p batch)) :: F) := by
  dsimp only
  intro ht hIdx hSource hFresh he hk hPeer hPeerK hLive
  have hLane : batch - first < 32 := by omega
  have hCount : groupLaneTiles p first (batch - first) = requestTiles p batch := by
    simp [groupLaneTiles, Nat.add_sub_of_le hFirst, hBatch, show batch - first < 31 by omega]
  have hOut := selectedRequestTilesShuffle hp (g := g) ht.1 ht.2.2.2.1 hLane hIdx hSource
  simpa only [hCount] using selectionShuffleStep hX ht hFresh hLane hOut he hk hPeer hPeerK hLive

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

private theorem selectionScalarLoad {l : Launch} {g pc r n : Nat} {t : TState}
    {F : List (Nat × Value)} {name : String}
    (ht : At t pc F) (hp : l.params name = some (BitVec.ofNat 64 n)) (hn : n < 2 ^ 32)
    (hCode : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param name false, 0⟩, dsts := [some r] }⟩) :
    run kernel [] l g 1 t = some (next (setReg t r (b32 n))) := by
  apply run_local hCode rfl ht
  rw [exec_ldParam (w := 32) hp (hL := by simp)]
  simp only [truncBits_ofNat hn (by decide), b32]

set_option maxRecDepth 3000 in
/-- Keep the scheduler frame while loading the cache capacity and batch count. -/
theorem selectedTileParameters (hp : Pre p l m) (g : Nat) {t : TState} {F : List (Nat × Value)}
    (ht : At t 2059 F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 7156 ∧ pair.1 ≠ 7148) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 2061 ((7148, b32 p.batch) :: (7156, b32 800) :: F) := by
  obtain ⟨hBatch, h19⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  obtain ⟨hCap, h22⟩ := hp.values (22, 800) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at h19
  change l.params (param 22) = some (BitVec.ofNat 64 800) at h22
  have hCode19 : kernel.code[2060]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param 19) false, 0⟩, dsts := [some 7148] }⟩ := by
    rw [Flow.code_2060, param, kernelName, decimal19]
    rfl
  have hCode22 : kernel.code[2059]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param 22) false, 0⟩, dsts := [some 7156] }⟩ := by
    rw [Flow.code_2059, param, kernelName, decimal22]
    rfl
  let v := next (setReg t 7156 (b32 800))
  have hv : At v 2060 ((7156, b32 800) :: F) := ht.set (fun pair hm => (hFresh pair hm).1)
  have hFirst := selectionScalarLoad (g := g) ht h22 hCap hCode22
  have hSecond := selectionScalarLoad (g := g) hv h19 hBatch hCode19
  have hRemain : ∀ pair ∈ ((7156, b32 800) :: F), pair.1 ≠ 7148 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hOld
    · decide
    · exact (hFresh pair hOld).2
  exact ⟨_, localRun (by decide) (by decide) ht.1 (by decide +kernel) (run_comp hFirst hSecond),
    hv.set hRemain⟩

end PTX.Kernels.TmlFa4Fwd.Mma
