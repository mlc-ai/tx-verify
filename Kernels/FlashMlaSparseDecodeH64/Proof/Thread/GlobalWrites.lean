-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.NotBulk
import Lemmas.Flow.WriteSpace

public section

/-! # The global writers of the frozen sparse-decode kernel -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GlobalWrites
open PTX PTX.Flow PTX.EventFrame Wg0

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def mayWriteGlobal (op : Op) : Bool :=
  writeOp op && (decide (storeSpace op = some .global) || dynamicAccess op)

private def stagedSites : List Nat :=
  (List.finRange 4).flatMap fun j => (List.finRange 8).map fun k => (Site.oStage j k).pc

set_option maxRecDepth 100000 in
private theorem global_sites :
    OpPcsFast kernel.code mayWriteGlobal (1178 :: stagedSites) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem output_sites : OpPcsFast kernel.code tensorStoreOp tensorStores = true := by
  decide +kernel

/-- Ordinary global writes can only be issued in the softmax body. -/
theorem global_write_candidate {i : EvId} {e : Event} {a : Acc} {bs : List Byte}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get i = some e)
    (hk : e.kind = .wr a bs) (hsp : a.loc.space = .global) : e.pc < 1842 := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hc, hf⟩
  · rw [hBad] at hk
    cases hk
  · have hop : mayWriteGlobal ins.op = true := by
      have hwr := fires_write_op hf hk
      have hspace := fires_write_space hf hk
      rw [hsp] at hspace
      rcases hspace with h | h <;> simp [mayWriteGlobal, hwr, h]
    have hAudit : (1178 :: stagedSites).all (fun pc => decide (pc < 1842)) = true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (OpPcsFast.mem global_sites hc hop))

private inductive OutputSite where
  | lse | stage (j : Fin 4) (k : Fin 8) | tensor (j : Fin 4)

private def OutputSite.site : OutputSite → Wg0.Site
  | .lse => .lseStore
  | .stage j k => .oStage j k
  | .tensor j => .tmaStore j

private def outputSites : List Nat := (1178 :: stagedSites) ++ tensorStores

private theorem output_site_match (s : Wg0.Site) (hs : s.pc ∈ outputSites) :
    ∃ k : OutputSite, s = k.site := by
  generalize s = a at hs ⊢
  clear s
  cases a with
  | lseStore => exact ⟨.lse, rfl⟩
  | oStage j k => exact ⟨.stage j k, rfl⟩
  | tmaStore j => exact ⟨.tensor j, rfl⟩
  | _ =>
    all_goals exact False.elim (by
      revert hs
      first | decide | (rename_i a; revert a; decide) | (rename_i a b; revert a b; decide))

private theorem output_role {g : Nat} {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d ∈ outputSites) :
    ∃ w, d = .wg0 w ∧ w.site.pc ∈ outputSites := by
  cases d with
  | wg0 s => exact ⟨s, rfl, h⟩
  | head => exact absurd h (by change 1843 ∉ outputSites; decide)
  | done => exact absurd h (by change 3611 ∉ outputSites; decide)
  | prologue d =>
    change d.pc ∈ outputSites at h
    exfalso
    cases d <;> revert h <;>
      first | decide | (rename_i a; revert a; decide)
  | idle s =>
    change s.pc ∈ outputSites at h
    exfalso
    cases s <;> revert h <;> decide
  | mma d =>
    change d.site.pc ∈ outputSites at h
    exfalso
    generalize d.site = site at h
    clear d
    cases site <;> revert h <;> first | decide | (rename_i a; revert a; decide)
  | tma d =>
    change d.site.pc ∈ outputSites at h
    exfalso
    generalize d.site = site at h
    clear d
    cases site <;> revert h <;>
      first | decide | (rename_i a; revert a; decide) | (rename_i a b; revert a b; decide)
  | index d =>
    change d.site.pc ∈ outputSites at h
    exfalso
    generalize d.site = site at h
    clear d
    cases site <;> revert h <;> first | decide | (rename_i a; revert a; decide) |
        (rename_i a b; revert a b; decide) | (rename_i a b c; revert a b c; decide)
  | wg2 d =>
    change d.site.pc ∈ outputSites at h
    exfalso
    generalize d.site = site at h
    clear d
    cases site <;> revert h <;> first | decide | (rename_i a b; revert a b; decide)

private theorem non_tensor_pc (s : OutputSite) (hs : s.site.pc ∈ tensorStores) :
    ∃ j, s = .tensor j := by
  cases s with
  | tensor j => exact ⟨j, rfl⟩
  | lse => exact absurd hs (by decide)
  | stage j k => exact absurd hs ((by decide +kernel :
      ∀ j k, (Site.oStage j k).pc ∉ tensorStores) j k)

/-- Every bulk tensor store comes from an output tile of the softmax role. -/
theorem outputTile_site_at_followed (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {a : Nat} {sp : TensorStore.Spec}
    (hFollowed : Frame.stateAt (Machine.code P L) X i.1 i.2 ≠ some none)
    (hi : X.TensorStoreIssue i a sp) :
    ∃ d j, Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .tmaStore j := by
  obtain ⟨site, he⟩ := hi
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, _⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hFollowed he (by simp)
  obtain ⟨_, _, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  have hx := OpPcsFast.mem output_sites hc (fires_tensorStore_op hf rfl)
  obtain ⟨w, rfl, hw⟩ := output_role (List.mem_append_right (1178 :: stagedSites) hx)
  obtain ⟨k, hk⟩ := output_site_match w.site hw
  have hm : k.site.pc ∈ tensorStores := by rw [← hk]; exact hx
  obtain ⟨j, rfl⟩ := non_tensor_pc k hm
  exact ⟨w, j, hd, hk⟩

/-- Every bulk tensor store comes from an output tile of the softmax role. -/
theorem outputTile_site (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {a : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i a sp) :
    ∃ d j, Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .tmaStore j :=
  outputTile_site_at_followed hs hX (ht i.1 i.2 (Frame.lt_of_get hX hi.choose_spec)) hi

/-- A direct global write is the four actual bytes of the row's LSE store. -/
theorem lse_write_at_followed (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {a : Acc} {bs : List Byte}
    (hFollowed : Frame.stateAt (Machine.code P L) X i.1 i.2 ≠ some none)
    (hwr : X.Writes i a bs) (hsp : a.loc.space = .global) :
    ∃ d : Wg0.D,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .lseStore ∧ a.loc = lseLocOf P L i.1 ∧ a.size = 4 ∧ bs = (lseReg d).toBytes := by
  obtain ⟨site, he⟩ := hwr
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, _⟩ :=
    RingSourceSites.fired_at_followed hX (hs i.1 hg).machine hFollowed he (by simp)
  obtain ⟨t, ins, o, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  have hop : mayWriteGlobal ins.op = true := by
    have hw := fires_write_op hf rfl
    have hspace := fires_write_space hf rfl
    rw [hsp] at hspace
    rcases hspace with h | h <;> simp [mayWriteGlobal, hw, h]
  have hm := OpPcsFast.mem global_sites hc hop
  obtain ⟨w, rfl, hw⟩ := output_role (List.mem_append_left tensorStores hm)
  obtain ⟨k, hk⟩ := output_site_match w.site hw
  cases k with
  | tensor j =>
    have hn : (Site.tmaStore j).pc ∉ 1178 :: stagedSites :=
      (by decide +kernel : ∀ a, (Site.tmaStore a).pc ∉ 1178 :: stagedSites) j
    change w.site = .tmaStore j at hk
    rw [show (Machine.code P L i.1).pc (.wg0 w) = w.site.pc from rfl, hk] at hm
    exact (hn hm).elim
  | stage j k =>
    have hs : w.site = .oStage j k := hk
    have hc' : kernel.code[(Site.oStage j k).pc]? = some ins := by
      rw [← hs]
      exact hc
    obtain rfl := Option.some.inj (hc'.symm.trans (stage_code j k))
    have htmpl := event_oStage hpre hg ha hi hs
    rw [htmpl] at hf
    have hac : a = {
        loc := shLoc L i.1 (stageWrite L i.1 j.val k.val t.sub), size := 4, elem := t.sub } :=
      (Kind.wr.inj (congrArg Event.kind hf.1)).1
    simp [hac, shLoc] at hsp
  | lse =>
    have ho : o.isSome := by
      generalize eventTmpl Assumptions.all L i.1 t ins.op = tm at hf
      cases tm <;> simp only [Fires] at hf <;> aesop
    obtain ⟨u, rfl⟩ := Option.isSome_iff_exists.mp ho
    obtain ⟨a', hecode, ha', hsize, -⟩ :=
      fires_lseStore hpre (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg) hk ha hi hc hf
    obtain ⟨rfl, hbs⟩ := Kind.wr.inj hecode
    exact ⟨w, hd, hk, ha', hsize, hbs⟩

/-- A tracked global write is the four bytes of the corresponding row's LSE. -/
theorem lse_write (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {a : Acc} {bs : List Byte} (hwr : X.Writes i a bs) (hsp : a.loc.space = .global) :
    ∃ d : Wg0.D,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .lseStore ∧ a.loc = lseLocOf P L i.1 ∧ a.size = 4 ∧ bs = (lseReg d).toBytes :=
  lse_write_at_followed hpre hs hX (ht i.1 i.2 (Frame.lt_of_get hX hwr.choose_spec)) hwr hsp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GlobalWrites
