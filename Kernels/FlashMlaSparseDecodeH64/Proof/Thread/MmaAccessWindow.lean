-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Tensor.TensorSwizzle

public section

/-! # Each pending operand byte lies in its issuing CTA's shared allocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaAccessWindow

open PTX PTX.Flow MmaDataTrace Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i index : Nat} {l : Loc}

private def InWindow (L : Launch) (g : Nat) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = ctaOf L g ∧
    L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 221184

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- Every issued Tensor Core copy is one of the query copies. -/
theorem copy_state {c : TcCopy.Spec} (hi : X.CpIssue (g, i) c) :
    ∃ q k, Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qCopy k ∧ c = queryCopySpec L g k := by
  obtain ⟨tag, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hState, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  have h := Wg0ScoreSources.writer_fields hpre hg hf (.inr (.inl ⟨c, rfl⟩))
  rcases h with ⟨_, _, _, _, hk⟩ | ⟨q, j, rfl, hsite, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
  · cases hk
  · exact ⟨q, j, hState, hsite, TcKind.cp.inj (Kind.tc.inj hk)⟩
  · cases hk
  · cases hk

/-- The actual copy uses the query descriptor of its chunk. -/
theorem copy_spec {c : TcCopy.Spec} (hi : X.CpIssue (g, i) c) :
    ∃ k, c = queryCopySpec L g k := by
  obtain ⟨_, k, _, _, hSpec⟩ := copy_state hpre hX hs ht hi
  exact ⟨k, hSpec⟩

/-- An actual MMA issue has the destination, operand, accumulate, and mask of its role site. -/
theorem mma_spec {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue (g, i) d s acc mask) :
    mask = [0, 0, 0, 0] ∧
      ((∃ block k, d = tmemP ∧ s = qkOperands L g block k ∧ acc = qkAccum k ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma k, block⟩))) ∨
      ∃ block k, d = pvDest k ∧ s = pvOperands L g block k ∧ acc = pvAccum block k ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩))) := by
  obtain ⟨tag, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hState, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  have h := Wg0ScoreSources.writer_fields hpre hg hf (.inl ⟨d, s, acc, mask, rfl⟩)
  rcases h with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ |
    ⟨d', j, hRole, hSite, hk⟩ | ⟨d', j, hRole, hSite, hk⟩
  · cases hk
  · cases hk
  · obtain ⟨ha, hs, hAcc, hMask⟩ := TcKind.mma.inj (Kind.tc.inj hk)
    refine ⟨hMask, .inl ⟨d'.i, j, ha, hs, hAcc, ?_⟩⟩
    rw [hState, hRole]
    cases d'
    cases hSite
    rfl
  · obtain ⟨ha, hs, hAcc, hMask⟩ := TcKind.mma.inj (Kind.tc.inj hk)
    refine ⟨hMask, .inr ⟨d'.i, j, ha, hs, hAcc, ?_⟩⟩
    rw [hState, hRole]
    cases d'
    cases hSite
    rfl

omit hpre hX hs ht in
/-- The byte of a BF16 contraction operand has a row, feature and subword coordinate. -/
theorem operand_slot {rows : Nat} (h : index < rows * 32) :
    ∃ (row : Fin rows) (k : Fin 16) (byte : Fin 2),
      index = 2 * (row.val * 16 + k.val) + byte.val :=
  ⟨⟨index / 32, (Nat.div_lt_iff_lt_mul (by decide)).mpr h⟩,
    ⟨index / 2 % 16, Nat.mod_lt _ (by decide)⟩,
    ⟨index % 2, Nat.mod_lt _ (by decide)⟩, by
      change index = 2 * (index / 32 * 16 + index / 2 % 16) + index % 2
      omega⟩

omit hpre hX hs ht in
private theorem kv_window (hpre : Pre P L mem0) {block slot feature byte : Nat}
    (hslot : slot < 64) (hfeature : feature < 512) (hbyte : byte < 2) :
    InWindow L g ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
      (kvLinearByte L block slot feature byte)⟩ := by
  let addr := kvLinearByte L block slot feature byte
  have ha : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
  have hmod : L.sharedBase % 128 = 0 := by omega
  have hlo : L.sharedBase ≤ addr := by dsimp [addr, kvLinearByte, kvBase]; omega
  have hhi : addr < L.sharedBase + 131072 := by
    dsimp [addr, kvLinearByte, kvBase]
    omega
  have hrow := TensorSwizzle.offset_row .b128 0 addr
  change InWindow L g ⟨.shared, ctaOf L g, TensorSwizzle.offset .b128 0 addr⟩
  refine ⟨rfl, rfl, ?_, ?_⟩
  · dsimp only
    omega
  · dsimp only
    omega

omit hpre hX hs ht in
private theorem qk_feature_lt (issue : Fin 16) (row : Fin 128) (k : Fin 16) :
    qkFeature issue row k < 512 := by
  have hi := issue.isLt
  have hr := row.isLt
  have hk := k.isLt
  dsimp only [qkFeature]
  omega

omit hpre hX hs ht in
private theorem copy_window (hpre : Pre P L mem0) (j : Fin 16) {cta : Nat}
    (hc : (queryCopySpec L g j).ctas[i]? = some cta)
    (hl : TcCopy.byteLoc (queryCopySpec L g j).shape (queryCopySpec L g j).src cta index =
      some l) : InWindow L g l := by
  change [ctaOf L g][i]? = some cta at hc
  have hc' := List.getElem?_eq_some_iff.mp hc
  have hz : i = 0 := by simpa using hc'.1
  subst i
  have ht : cta = ctaOf L g := (Option.some.inj hc).symm
  subst cta
  have hn : index < 128 * 32 := by
    unfold TcCopy.byteLoc at hl
    split at hl
    · assumption
    · cases hl
  obtain ⟨row, k, b, rfl⟩ := operand_slot hn
  rw [queryCopyByteLoc L g j row k b] at hl
  obtain rfl := (Option.some.inj hl).symm
  exact kv_window hpre (Nat.mod_lt _ (by decide)) (qk_feature_lt j row k) b.isLt

omit hpre hX hs ht in
private theorem qk_window (hpre : Pre P L mem0) (block : Nat) (j : Fin 16) (isB : Bool)
    (hl : (qkOperands L g block j).byteLoc (if isB then .b else .a) index = some l) :
    InWindow L g l := by
  cases isB
  · change (qkOperands L g block j).byteLoc .a index = some l at hl
    have hn := TcMma.byteLoc_a_tmem (s := qkOperands L g block j) rfl index
    rw [hn] at hl
    cases hl
  · change (qkOperands L g block j).byteLoc .b index = some l at hl
    have hn := TcMma.OperandSpec.byteLoc_index_lt (s := qkOperands L g block j) (op := .b) hl
    norm_num [qkOperands, qkDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
      TcMma.Kind.k, TcMma.Kind.width] at hn
    obtain ⟨row, k, b, rfl⟩ := operand_slot (rows := 128) hn
    rw [qkKeyByte L g block j row k b] at hl
    obtain rfl := (Option.some.inj hl).symm
    exact kv_window hpre (Nat.mod_lt _ (by decide)) (qk_feature_lt j row k) b.isLt

omit hpre hX hs ht in
private theorem pv_slot_lt (issue : Fin 8) (k : Fin 16) : pvSlot issue k < 64 := by
  have hi := issue.isLt
  have hk := k.isLt
  simp only [pvSlot]
  omega

omit hpre hX hs ht in
private theorem pv_window (hpre : Pre P L mem0) (block : Nat) (j : Fin 8) (isB : Bool)
    (hl : (pvOperands L g block j).byteLoc (if isB then .b else .a) index = some l) :
    InWindow L g l := by
  cases isB
  · change (pvOperands L g block j).byteLoc .a index = some l at hl
    have hn := TcMma.OperandSpec.byteLoc_index_lt (s := pvOperands L g block j) (op := .a) hl
    norm_num [pvOperands, pvDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
      TcMma.Kind.k, TcMma.Kind.width] at hn
    obtain ⟨row, k, b, rfl⟩ := operand_slot (rows := 128) hn
    rw [pvProbabilityByte L g block j row k b] at hl
    obtain rfl := (Option.some.inj hl).symm
    have hSlot := pv_slot_lt j k
    have hb := b.isLt
    refine ⟨rfl, rfl, ?_, ?_⟩
    all_goals dsimp only [pLinearByte]; omega
  · change (pvOperands L g block j).byteLoc .b index = some l at hl
    have hn := TcMma.OperandSpec.byteLoc_index_lt (s := pvOperands L g block j) (op := .b) hl
    norm_num [pvOperands, pvDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
      TcMma.Kind.k, TcMma.Kind.width] at hn
    obtain ⟨col, k, b, rfl⟩ := operand_slot (rows := 256) hn
    rw [pvValueByte L g block j col k b] at hl
    obtain rfl := (Option.some.inj hl).symm
    have hFeature : pvFeature j col < 512 := by
      have hc := col.isLt
      dsimp only [pvFeature]
      omega
    exact kv_window hpre (pv_slot_lt j k) hFeature b.isLt

/-- Every byte read by a pending or performed Tensor Core issue lies below the row area. -/
theorem operand_regions {isB : Bool} (hf : X.MmaFootprint (g, i) isB index l) :
    g < L.threads ∧ l.space = .shared ∧ l.cta = ctaOf L g ∧
      L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 221184 := by
  change g < L.threads ∧ InWindow L g l
  rcases hf with ⟨_, _, _, _, hi, hl⟩ | ⟨_, _, _, hi, _, hc, _, hl⟩
  · refine ⟨Frame.lt_of_get hX hi.choose_spec, ?_⟩
    rcases (mma_spec hpre hX hs ht hi).2 with ⟨block, k, _, rfl, _⟩ | ⟨block, k, _, rfl, _⟩
    · exact qk_window hpre block k isB hl
    · exact pv_window hpre block k isB hl
  · obtain ⟨k, rfl⟩ := copy_spec hpre hX hs ht hi
    exact ⟨Frame.lt_of_get hX hi.choose_spec, copy_window hpre k hc hl⟩

/-- Every shared byte read by a pending or performed Tensor Core issue lies in the CTA window. -/
theorem footprint {isB : Bool} (hf : X.MmaFootprint (g, i) isB index l) :
    g < L.threads ∧ l.space = .shared ∧ l.cta = ctaOf L g ∧
      L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes := by
  obtain ⟨hg, hSpace, hCta, hLo, hHi⟩ := operand_regions hpre hX hs ht hf
  exact ⟨hg, hSpace, hCta, hLo, by simp only [sharedBytes]; omega⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaAccessWindow
