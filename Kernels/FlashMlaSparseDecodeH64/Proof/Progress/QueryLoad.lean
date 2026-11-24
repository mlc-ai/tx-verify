-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressTensor
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQueryValues
import Kernels.FlashMlaSparseDecodeH64.Proof.Geometry.Maps
import Lemmas.Protocol.NamedBarSources

public section

/-! # Progress of the eight issued query loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow MmaDataTrace Wg1Mma Result

/-- The fixed launch source and destination of an actual query tile provide its progress inputs. -/
theorem query_tensor_input {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} (hpre : Pre P L mem0) (tile : Fin 8)
    (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (_ht : Frame.Tracked (Machine.code P L) X)
    (he : X.TensorIssue (g, i) (P.param1Base + qMapOff) (queryTmaSpec P L g tile)) :
    TensorInput L mem0 X (g, i) (queryTmaSpec P L g tile) := by
  have hg := Frame.lt_of_get hX he.choose_spec
  have hcta : ctaOf L g < L.grid := PTX.NamedBar.cta_lt hg
  have hself : CtaInCluster L (ctaOf L g) (ctaOf L g) := ⟨hcta, hcta, rfl⟩
  have hgroup : SameCtaGroup L .one (ctaOf L g) (ctaOf L g) :=
    (sameCtaGroup_iff ..).mpr ⟨hself, rfl⟩
  have hroute : TensorCopy.RoutingOk L (g / L.block) (queryTmaSpec P L g tile) := by
    refine ⟨hX.cluster.1, rfl, rfl, hself, hself, ?_, hgroup⟩
    simp [queryTmaSpec]
  obtain ⟨hx, hy, hb⟩ := queryTile_shape P L g tile
  refine ⟨hroute, Geometry.mapQ_valid_of_pre hpre, ?_, ?_⟩
  · simp only [TensorTransfer.bytes, hx, hy, hb]; decide
  intro slot address ha
  obtain ⟨x, y, b⟩ := slot
  let u : Fin 64 := ⟨x.val, hx ▸ x.isLt⟩
  let v : Fin 64 := ⟨y.val, hy ▸ y.isLt⟩
  let w : Fin 2 := ⟨b.val, hb ▸ b.isLt⟩
  change TensorCopy.source (queryTmaSpec P L g tile) (queryTileSlot P L g tile u v w) =
    .global address at ha
  obtain ⟨address', hsource, hbyte⟩ := queryTile_initial hpre hg tile u v w
  obtain rfl := TensorTransfer.Source.global.inj (ha.symm.trans hsource)
  refine ⟨_, hbyte, queryTile_globalNoWrite hpre hg hs hX tile u v w ?_⟩
  have haddress := queryTile_global hpre hg tile u v w
  rw [TensorCopy.source, haddress] at ha
  obtain rfl := TensorTransfer.Source.global.inj ha
  exact haddress

/-- An unnotified query TMA load can read, write or signal one more counted effect. -/
theorem query_tensor_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} (hpre : Pre P L mem0) (tile : Fin 8)
    (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.TensorIssue (g, i) (P.param1Base + qMapOff) (queryTmaSpec P L g tile))
    (hn : (X.tensor (g, i)).any (fun old => old.effects.notified) = false) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  pending_tensor_extension hX he (query_tensor_input hpre tile hs hX ht he) hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
