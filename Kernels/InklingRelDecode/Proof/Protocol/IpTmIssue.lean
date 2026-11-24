-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingKvMma
public import Kernels.InklingRelDecode.Proof.Result.MmaScore
public import Kernels.InklingRelDecode.Proof.Result.MmaO
public import Kernels.InklingRelDecode.Proof.Interface.MmaFacts
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Kernels.InklingRelDecode.Proof.Protocol.TmemTc
public import Lemmas.Execution.NoTcCp

@[expose] public section

/-!
# The MMA instruction branch: no copy, no collector reuse, the issue shape

The premises of `Safety.Protocol.tcInstr` (`TcMma.InstructionUnsafe`) that are statements about the
program and the MMA warp's issues:

* `no_cp`: the kernel issues no `tcgen05.cp` (`kernel.NoTcCp`, `decide +kernel`);
* `mma_cases`: an MMA event fires from the MMA warp's QK or PV site and is the decoded issue of
  the site (`EvW.QkIssue`, `PvIssue`: the `kind::f16` descriptor, the two shared descriptors, the
  accumulator column, the zero masks);
* `collector_noReuse`: no MMA names a collector buffer, so none reuses one;
* `issueShape`: `TcMma.IssueShape` of every MMA, given that the Tensor Memory base is 0
  (`Interface.mma_tm`, from `BaseWordRead` and `NumWordRead`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX PTX.Proof PTX.Flow PTX.TcMma PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc qkDesc_eq pvDesc_eq qkDesc_valid
  pvDesc_valid decode_k decode_v)
open PTX.Kernels.InklingRelDecode.Proof.EvW (QkIssue PvIssue MmShape mmQkALo mmQkBLo mmPvBLo
  MmEnv mmEnv_of_pre)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem kernel_noTcCp : kernel.NoTcCp = true := by decide +kernel

/-- **The kernel issues no `tcgen05.cp`.** -/
theorem no_cp (hX : Consistent L kernel asms mem0 X) : ∀ i c, ¬ X.CpIssue i c :=
  noCp_of_consistent kernel_noTcCp hX

/-- **An MMA event is the decoded issue of the MMA warp's QK or PV site.** -/
theorem mma_cases (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {m : EvId} {pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get m = some ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    m.1 < L.threads ∧ ∃ (d : Mma.D) (P : Loader.Pro),
      St Q L X m.1 m.2 = some (some (.w (.mma d P))) ∧
      mask = [0, 0, 0, 0] ∧
      ((∃ j : Fin 8, d.site = .qk j ∧ ∃ da db dsc, TcMma.decode .one false .f16 Mma.qkIdesc =
          some dsc ∧ TcShared.decode (mmQkALo L j + Mma.descHi * 2 ^ 32) = some da ∧
          TcShared.decode (mmQkBLo L (d.i % 3) j + Mma.descHi * 2 ^ 32) = some db ∧
          dst = d.tm + 128 * (d.i % 2) ∧
          sp = ⟨dsc, da, db, m.1 / L.block, m.1 / L.block, none, {}⟩) ∨
       (∃ j : Fin 8, d.site = .pv j ∧ ∃ db dsc, TcMma.decode .one false .f16 Mma.pvIdesc =
          some dsc ∧ TcShared.decode (mmPvBLo L ((d.i - 1) % 3) j + 2 ^ 26 +
            Mma.descHi * 2 ^ 32) = some db ∧ dst = d.tm + 256 ∧
          sp = ⟨dsc, db, db, m.1 / L.block, m.1 / L.block,
            some (d.tm + 128 * ((d.i - 1) % 2) + 8 * j), {}⟩)) := by
  have hg : m.1 < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
    (.inl ⟨dst, sp, acc, mask, rfl⟩)
  refine ⟨hg, d, P, hσ, ?_⟩
  rcases Ring.mma_site d hsh with ⟨j, hs⟩ | ⟨j, hs⟩
  · simp only [MmShape, hs] at hsh
    obtain ⟨da, db, dsc, h1, h2, h3, h4⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h4
    obtain ⟨-, h5, h6, h7, h8⟩ := h4
    exact ⟨h8, .inl ⟨j, hs, da, db, dsc, h1, h2, h3, h5, h6⟩⟩
  · simp only [MmShape, hs] at hsh
    obtain ⟨db, dsc, h1, h2, h4⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h4
    obtain ⟨-, h5, h6, h7, h8⟩ := h4
    exact ⟨h8, .inr ⟨j, hs, db, dsc, h1, h2, h5, h6⟩⟩

/-- **No MMA reuses a collector buffer**: every issue's collector usage is the default
(`collector::a::discard`, `collector::b::discard`). -/
theorem collector_noReuse (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    s.collector.a.reuses = false ∧ s.collector.b.reuses = false := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨-, d', P, -, -, h⟩ := mma_cases hpre hX hf he
  rcases h with ⟨j, -, da, db, dsc, -, -, -, -, rfl⟩ | ⟨j, -, db, dsc, -, -, -, rfl⟩ <;>
    exact ⟨rfl, rfl⟩

/-! ### The issue shape -/

theorem q14 {L : Launch} (hE : MmEnv L) (j : Nat) (hj : j < 8) :
    Mma.qLo L + 2 * (j % 4) + 512 * (j / 4) < 2 ^ 14 := by
  have := hE.sb
  unfold Mma.qLo
  omega

theorem k14 {L : Launch} (hE : MmEnv L) (s j : Nat) (hs : s < 3) (hj : j < 8) :
    Mma.kLo L s + 2 * (j % 4) + 1024 * (j / 4) < 2 ^ 14 := by
  have := hE.sb
  unfold Mma.kLo
  omega

theorem v14 {L : Launch} (hE : MmEnv L) (s j : Nat) (hs : s < 3) (hj : j < 8) :
    Mma.vLo L s + 128 * j < 2 ^ 14 := by
  have := hE.sb
  unfold Mma.vLo
  omega

theorem sharedEncoded_k {lo : Nat} (h : lo < 2 ^ 14) :
    SharedEncoded ⟨lo * 16, 0, 1024, 0, false, false, .b128⟩ := by
  show lo * 16 < 2 ^ 18 ∧ 0 < 2 ^ 18 ∧ 1024 < 2 ^ 18 ∧ lo * 16 % 16 = 0 ∧ 0 % 16 = 0 ∧
    1024 % 16 = 0
  omega

theorem sharedEncoded_v {lo : Nat} (h : lo < 2 ^ 14) :
    SharedEncoded ⟨lo * 16, 16384, 1024, 0, false, false, .b128⟩ := by
  show lo * 16 < 2 ^ 18 ∧ 16384 < 2 ^ 18 ∧ 1024 < 2 ^ 18 ∧ lo * 16 % 16 = 0 ∧ 16384 % 16 = 0 ∧
    1024 % 16 = 0
  omega

/-- The A operand of a PV MMA, read from Tensor Memory, has a cell for every byte. -/
theorem pv_aCell {s : OperandSpec} (hD : s.descriptor = pvDesc) {addr idx : Nat}
    (haT : s.aTmem = some addr) (hadd : addr < 400) (hidx : idx < 2048) :
    ∃ c, aCell s idx = some c := by
  unfold aCell
  simp only [haT, hD, Option.bind_some]
  have hv := pvDesc_valid
  split
  · exact ⟨_, rfl⟩
  · rename_i hn
    exfalso
    refine hn ⟨hv, ?_, ?_, Or.inr (Or.inl ⟨by decide, Or.inl ?_⟩)⟩
    · simp [pvDesc, Operand.rows, Operand.extent, Kind.k, Kind.width]
      omega
    · simp [pvDesc, Kind.k, Kind.width]
      omega
    · omega

theorem matchesLaunch (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) (dsc : Descriptor)
    (da db : TcShared.Descriptor) (a : Option Nat) (hd : dsc.group = .one) :
    OperandSpec.MatchesLaunch ⟨dsc, da, db, g / L.block, g / L.block, a, {}⟩ L (g / L.block) := by
  refine ⟨[g / L.block], ?_, rfl, rfl⟩
  simp only [hd]
  rw [Launch.ctaGroup_one, EvW.peer_self (EvW.unitCta_of_pre hpre hg)]
  rfl

/-- The operand bytes of a QK MMA are all located. -/
theorem qk_loc {s : OperandSpec} (hD : s.descriptor = qkDesc) {sa sb : Nat}
    (ha : s.a = ⟨sa, 0, 1024, 0, false, false, .b128⟩)
    (hb : s.b = ⟨sb, 0, 1024, 0, false, false, .b128⟩) (haT : s.aTmem = none) :
    ∀ (op : Operand) (idx : Nat), idx < op.bytes s.descriptor →
      (∃ loc, s.byteLoc op idx = some loc) ∨ (op = .a ∧ ∃ c, aCell s idx = some c) := by
  intro op idx hidx
  rw [hD] at hidx
  cases op
  · have hba : Operand.bytes .a qkDesc = 2048 := by decide
    rw [hba] at hidx
    have := Result.Mma.qk_a_loc hD ha haT (r := idx / 32) (kk := idx / 2 % 16) (z := idx % 2)
      (by omega) (by omega) (by omega)
    rw [show 32 * (idx / 32) + 2 * (idx / 2 % 16) + idx % 2 = idx by omega] at this
    exact Or.inl ⟨_, this⟩
  · have hbb : Operand.bytes .b qkDesc = 4096 := by decide
    rw [hbb] at hidx
    have := Result.Mma.qk_b_loc hD hb (n := idx / 32) (kk := idx / 2 % 16) (z := idx % 2)
      (by omega) (by omega) (by omega)
    rw [show 32 * (idx / 32) + 2 * (idx / 2 % 16) + idx % 2 = idx by omega] at this
    exact Or.inl ⟨_, this⟩

/-- The operand bytes of a PV MMA are all located (B in shared memory, A in Tensor Memory). -/
theorem pv_loc {s : OperandSpec} (hD : s.descriptor = pvDesc) {sb : Nat}
    (hb : s.b = ⟨sb, 16384, 1024, 0, false, false, .b128⟩) {addr : Nat}
    (haT : s.aTmem = some addr) (hadd : addr < 400) :
    ∀ (op : Operand) (idx : Nat), idx < op.bytes s.descriptor →
      (∃ loc, s.byteLoc op idx = some loc) ∨ (op = .a ∧ ∃ c, aCell s idx = some c) := by
  intro op idx hidx
  rw [hD] at hidx
  cases op
  · have hba : Operand.bytes .a pvDesc = 2048 := by decide
    rw [hba] at hidx
    exact Or.inr ⟨rfl, pv_aCell hD haT hadd hidx⟩
  · have hbb : Operand.bytes .b pvDesc = 4096 := by decide
    rw [hbb] at hidx
    have := Result.Mma.pv_b_loc hD hb (n := idx / 32) (kk := idx / 2 % 16) (z := idx % 2)
      (by omega) (by omega) (by omega)
    rw [show 32 * (idx / 32) + 2 * (idx / 2 % 16) + idx % 2 = idx by omega] at this
    exact Or.inl ⟨_, this⟩

/-- **`TcMma.IssueShape` of every MMA**, given the premises of the Tensor Memory base word (every
MMA state's base is 0: `Interface.mma_tm`). -/
theorem issueShape (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) : IssueShape L i d s mask := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hg, dm, P, hσ, hmask, h⟩ := mma_cases hpre hX hf he
  have htm : dm.tm = 0 := mma_tm hpre hX hf hb hn ⟨P, hσ⟩
  have hE := mmEnv_of_pre hpre
  have hmk : OutputMaskValid CtaGroup.one mask := by
    rw [hmask]
    decide
  rcases h with ⟨j, hs, da, db, dsc, h1, h2, h3, hd, rfl⟩ | ⟨j, hs, db, dsc, h1, h2, hd, rfl⟩
  · -- a QK MMA
    obtain rfl := qkDesc_eq h1
    have hj := j.isLt
    have hla := Ring.lo_lt_q hE j hj
    have hlb := Ring.lo_lt_k hE (dm.i % 3) j (Nat.mod_lt _ (by omega)) hj
    have h2' : TcShared.decode (Mma.qLo L + 2 * (j % 4) + 512 * (j / 4) +
        Mma.descHi * 2 ^ 32) = some da := h2
    have h3' : TcShared.decode (Mma.kLo L (dm.i % 3) + 2 * (j % 4) + 1024 * (j / 4) +
        Mma.descHi * 2 ^ 32) = some db := h3
    rw [decode_k hla] at h2'
    rw [decode_k hlb] at h3'
    obtain rfl := Option.some.inj h2'
    obtain rfl := Option.some.inj h3'
    have hlay := Result.Mma.qkDesc_facts
    refine ⟨hg, qkDesc_valid, hmk, matchesLaunch hpre hg qkDesc _ _ _ rfl,
      sharedEncoded_k (q14 hE j hj), sharedEncoded_k (k14 hE (dm.i % 3) j (Nat.mod_lt _ (by omega))
        hj), ?_, fun a ha => by simp at ha, ?_, ?_⟩
    · rw [hd, htm]
      have : (0 + 128 * (dm.i % 2)) / 2 ^ 16 = 0 := by omega
      rw [this]
      exact hlay.1
    · rw [hd, htm]
      have : (0 + 128 * (dm.i % 2)) % 2 ^ 16 = 128 * (dm.i % 2) := by omega
      rw [this, hlay.2.1]
      omega
    · exact qk_loc rfl rfl rfl rfl
  · -- a PV MMA
    obtain rfl := pvDesc_eq h1
    have hj := j.isLt
    have hlv := Ring.lo_lt_v hE ((dm.i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj
    rw [show mmPvBLo L ((dm.i - 1) % 3) j = Mma.vLo L ((dm.i - 1) % 3) + 128 * j from rfl,
      decode_v hlv] at h2
    obtain rfl := Option.some.inj h2
    have hlay := Result.Mma.pvDesc_facts
    refine ⟨hg, pvDesc_valid, hmk, matchesLaunch hpre hg pvDesc _ _ _ rfl,
      sharedEncoded_v (v14 hE ((dm.i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj),
      sharedEncoded_v (v14 hE ((dm.i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj), ?_, ?_, ?_, ?_⟩
    · rw [hd, htm]
      have : (0 + 256) / 2 ^ 16 = 0 := by omega
      rw [this]
      exact hlay.1
    · intro a ha _
      simp only [Option.some.injEq] at ha
      rw [← ha, hd, htm]
      omega
    · rw [hd, htm]
      have : (0 + 256) % 2 ^ 16 = 256 := by omega
      rw [this, hlay.2.1]
      omega
    · exact pv_loc rfl rfl rfl (by rw [htm]; omega)

/-- **`Safety.Protocol.tcInstr`**: the issue shape (from the base word's read), no copy, no
collector reuse, and the one premise that is not about the program: every completed MMA's unmasked
results have derived values (`TcMma.CompletedValues`, the result layer's `Result`). -/
theorem tcInstr_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    (hmv : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → CompletedValues L asms X i) :
    ¬ InstructionUnsafe L asms X :=
  no_instruction_unsafe (fun hi => ⟨issueShape hpre hX hf hb hn hi, hmv hi⟩) (no_cp hX)
    (fun hi => collector_noReuse hpre hX hf hi)

end
end PTX.Kernels.InklingRelDecode.Proof.Tmem1
