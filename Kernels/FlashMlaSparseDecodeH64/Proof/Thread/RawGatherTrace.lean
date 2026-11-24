-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmRawGather
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Lemmas.Protocol.NamedBarSources

public section

/-! # The launch descriptor behind each recorded gather4 -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RawGatherTrace
open PTX PTX.Flow

private theorem gather_fired {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g j : Nat} {e : Event} {d : Wg1Tma.D} {k : Fin 16}
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hst : Frame.stateAt (Machine.code P L) X g j = some (some (.tma d)))
    (hsite : d.site = .issue k) (he : X.get (g, j) = some e) :
    ∃ t o, (Wg1Tma.code P L g).AtD d t ∧ Wg1Tma.Inv P L g d ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t (Wg1Tma.issueInstr k).op) e o := by
  obtain ⟨t, ins, o, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hst
  change kernel.code[d.site.pc]? = some ins at hc
  have hcode : kernel.code[d.site.pc]? = some (Wg1Tma.issueInstr k) := by
    rw [hsite]
    exact Wg1Tma.issueInstr_code k
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  exact ⟨t, o, ha, hi, hf⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g j addr : Nat} {e : Event}
    {s : TensorCopy.Spec} {d : Wg1Tma.D} {k : Fin 16} (hpre : Pre P L mem0)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hs hX

/-- The observed gather's four signed coordinates are the recorded words of its positions. -/
theorem gather_coordinates (hst : Frame.stateAt (Machine.code P L) X g j = some (some (.tma d)))
    (hsite : d.site = .issue k) (he : X.get (g, j) = some e) (hk : e.kind = .tensorIssue addr s)
    (hw : GemmRawGather.Words P L g d k) :
    Wg1Tma.Inv P L g d ∧
      (∃ desc : TensorDescriptor.Descriptor s.outer,
        L.tensorMaps (P.param1Base + Wg1Tma.kvOff d) = some ⟨s.outer, desc⟩ ∧
        s.descriptor = desc.fourRows) ∧
      s.origin ⟨0, Nat.zero_lt_succ _⟩ = 0 ∧
      s.rows = some (fun j : Fin 4 =>
        (BitVec.ofNat 32 (Wg1Tma.coordAt P L g d.block (Wg1Tma.coordPos k.val j.val))).toInt) := by
  obtain ⟨_, _, ha, hi, hf⟩ := gather_fired hs hX hst hsite he
  obtain ⟨hdesc, horigin, _⟩ := GemmRawGather.gather_layout hpre k hsite ha hi hf hk
  exact ⟨hi, hdesc, horigin, GemmRawGather.gather_coordinates k hsite ha hf hk hw⟩

/-- An executed gather names a valid local transfer layout from the main or enabled extra map. -/
theorem gather_operands (hst : Frame.stateAt (Machine.code P L) X g j = some (some (.tma d)))
    (hsite : d.site = .issue k) (he : X.get (g, j) = some e) (hk : e.kind = .tensorIssue addr s) :
    TensorCopy.RoutingOk L (g / L.block) s ∧ TensorTransfer.bytes s.descriptor = 2304 ∧
      ∃ rows, s.origin ⟨0, Nat.zero_lt_succ _⟩ = 0 ∧ s.rows = some rows ∧
        ((⟨s.outer, s.descriptor⟩ : Σ outer, TensorDescriptor.Descriptor outer) =
            ⟨1, (encodeKv P.kvBase P.numBlocks P.blockStride P.kvClass).fourRows⟩ ∨
          P.extra_topk ≠ 0 ∧
            (⟨s.outer, s.descriptor⟩ : Σ outer, TensorDescriptor.Descriptor outer) =
              ⟨1, (encodeKv P.extraKvBase P.extraNumBlocks
                P.extraBlockStride P.extraKvClass).fourRows⟩) := by
  obtain ⟨_, _, ha, hi, hf⟩ := gather_fired hs hX hst hsite he
  have hfields := Wg1Tma.gather_issue_fields hpre hsite ha hi hf hk
  obtain ⟨⟨desc, hbind, hdesc⟩, hfirst, _, hrows⟩ :=
    GemmRawGather.gather_layout hpre k hsite ha hi hf hk
  have hcta : ctaOf L g < L.grid := PTX.NamedBar.cta_lt (Frame.lt_of_get hX he)
  have hself : CtaInCluster L (ctaOf L g) (ctaOf L g) := ⟨hcta, hcta, rfl⟩
  have hroute : TensorCopy.RoutingOk L (g / L.block) s := by
    change TensorRoute L (g / L.block) s.clusterAddress s.group s.sharedBase s.mbar
    rw [hfields.2.1, hfields.2.2.1]
    exact ⟨hX.cluster.1, rfl, rfl, hself, hself, fun _ => ⟨rfl, rfl⟩,
      (sameCtaGroup_iff ..).mpr ⟨hself, rfl⟩⟩
  refine ⟨hroute, hfields.2.2.2, _, hfirst, hrows, ?_⟩
  have htransfer : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨s.outer, desc.fourRows⟩ := by rw [hdesc]
  rw [htransfer]
  let four (x : Σ n, TensorDescriptor.Descriptor n) : Σ n, TensorDescriptor.Descriptor n :=
    ⟨x.1, x.2.fourRows⟩
  by_cases hmain : d.block < numOrigBlocks d.len0
  · rw [Wg1Tma.kvOff, ite_eq_left hmain, hpre.mapKVBind] at hbind
    left
    exact congrArg four (Option.some.inj hbind).symm
  · have hnonzero := Wg1Tma.extra_active hpre hi (by simp [hsite]) (by simp [hsite]) hmain
    rw [Wg1Tma.kvOff, ite_eq_right hmain, hpre.mapExtraKvBind.resolve_left hnonzero] at hbind
    right
    exact ⟨hnonzero, congrArg four (Option.some.inj hbind).symm⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RawGatherTrace
