-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Async.Tma
public import Core.Async.Tensor.TensorThread
public import Core.Async.AsyncCopy

/-! Decoding, thread events and effect validity of `cp.async.bulk` in every direction, of the
linear prefetch `cp.async.bulk.prefetch`, and of the tensor prefetch with `.L2::evict_last`. Each
accepted form has its exact result, next to the rejected neighbours. -/
namespace PTX.Tests.AsyncLinearCopy
noncomputable section
open PTX.Syntax

/-! ## Decoding -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 8, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%p".toList, 1, 1⟩,
      ⟨"%h".toList, 2, 16⟩], labels := [], params := [] }
private def at' (n : String) : Operand := .address [.register n]
private def isOk : Except String Op → Bool
  | .ok _ => true
  | .error _ => false
private def unmodeled : Except String Op → Bool
  | .ok (.unmodeled _) => true
  | _ => false

private def cta := "cp.async.bulk.shared::cta.global.mbarrier::complete_tx::bytes"
private def cluster := "cp.async.bulk.shared::cluster.global.mbarrier::complete_tx::bytes"

-- Registers: `%r0`-`%r7` are 0-7, `%rd0` and `%rd1` are 8 and 9, `%p0` is 10, `%h0` is 11.
example : Decode.op env cta [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"] =
    .ok (.cpBulk ⟨.globalToCta, 0, 0, 8, 0, .reg 1, some (2, 0), none, none, none, none, none,
        none⟩) := rfl
example : Decode.op env cluster [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"] =
    .ok (.cpBulk ⟨.globalToCluster, 0, 0, 8, 0, .reg 1, some (2, 0), none, none, none, none, none,
        none⟩) := rfl
-- The size may be an immediate.
example : Decode.op env cta [at' "%r0", at' "%rd0", .literal "64", at' "%r2"] =
    .ok (.cpBulk ⟨.globalToCta, 0, 0, 8, 0, .imm 64, some (2, 0), none, none, none, none, none,
        none⟩) := rfl
-- `.multicast::cluster` has a 16-bit mask, `.multicast::cluster::32b` a 32-bit mask.
example : Decode.op env (cluster ++ ".multicast::cluster")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2", .register "%h0"] =
    .ok (.cpBulk ⟨.globalToCluster, 0, 0, 8, 0, .reg 1, some (2, 0), some (16, .reg 11), none,
      none, none, none, none⟩) := rfl
example : Decode.op env (cluster ++ ".multicast::cluster::32b")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2", .register "%r3"] =
    .ok (.cpBulk ⟨.globalToCluster, 0, 0, 8, 0, .reg 1, some (2, 0), some (32, .reg 3), none,
      none, none, none, none⟩) := rfl
example : isOk (Decode.op env (cluster ++ ".multicast::cluster")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2", .register "%r3"]) = false := rfl
example : isOk (Decode.op env (cluster ++ ".multicast::cluster::32b")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2", .register "%h0"]) = false := rfl
-- Shared to shared across CTAs of a cluster, and shared to global with a bulk group.
example : Decode.op env
    "cp.async.bulk.shared::cluster.shared::cta.mbarrier::complete_tx::bytes"
    [at' "%r0", at' "%r1", .register "%r2", at' "%r3"] =
    .ok (.cpBulk ⟨.ctaToCluster, 0, 0, 1, 0, .reg 2, some (3, 0), none, none, none, none, none,
        none⟩) := rfl
example : Decode.op env "cp.async.bulk.global.shared::cta.bulk_group"
    [at' "%rd0", at' "%r0", .register "%r1"] =
    .ok (.cpBulk ⟨.ctaToGlobal, 8, 0, 0, 0, .reg 1, none, none, none, none, none, none,
        none⟩) := rfl
-- `.relaxed.cta` with `.b128` is accepted and decodes like the weak form.
example : Decode.op env (
    "cp.async.bulk.relaxed.cta.shared::cta.global.mbarrier::complete_tx::bytes.b128")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"] =
    .ok (.cpBulk ⟨.globalToCta, 0, 0, 8, 0, .reg 1, some (2, 0), none, none, none, none, none,
        none⟩) := rfl
-- `.L2::cache_hint` takes its 64-bit policy operand after the mbarrier or the size.
example : Decode.op env (cta ++ ".L2::cache_hint")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2", .register "%rd1"] =
    .ok (.cpBulk ⟨.globalToCta, 0, 0, 8, 0, .reg 1, some (2, 0), none, none, some (.reg 9), none,
        none, none⟩) :=
  rfl
example : Decode.op env "cp.async.bulk.global.shared::cta.bulk_group.L2::cache_hint"
    [at' "%rd0", at' "%r0", .register "%r1", .register "%rd1"] =
    .ok (.cpBulk ⟨.ctaToGlobal, 8, 0, 0, 0, .reg 1, none, none, none, some (.reg 9), none, none,
        none⟩) := rfl
example : isOk (Decode.op env (cta ++ ".L2::cache_hint")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"]) = false := rfl
-- `.ignore_oob` carries `ignoreBytesLeft` and `ignoreBytesRight` after the size.
example : Decode.op env (cta ++ ".ignore_oob")
    [at' "%r0", at' "%rd0", .register "%r1", .register "%r3", .register "%r4", at' "%r2"] =
    .ok (.cpBulk ⟨.globalToCta, 0, 0, 8, 0, .reg 1, some (2, 0), none,
      some (.reg 3, .reg 4), none, none, none, none⟩) := rfl
example : isOk (Decode.op env (cta ++ ".ignore_oob")
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"]) = false := rfl
-- The `.cp_mask` form carries its 16-bit byte mask.
example : Decode.op env "cp.async.bulk.global.shared::cta.bulk_group.cp_mask"
    [at' "%rd0", at' "%r0", .register "%r1", .register "%h0"] =
    .ok (.cpBulk (BulkCopy.mk .ctaToGlobal 8 0 0 0 (.reg 1) none none none none (some (.reg 11))
      none none)) := rfl
-- A completion mechanism that does not belong to the direction has no instruction entry.
example : isOk (Decode.op env "cp.async.bulk.global.shared::cta.mbarrier::complete_tx::bytes"
    [at' "%rd0", at' "%r0", .register "%r1", at' "%r2"]) = false := rfl
example : isOk (Decode.op env "cp.async.bulk.shared::cta.global.bulk_group"
    [at' "%r0", at' "%rd0", .register "%r1"]) = false := rfl
-- Linear prefetch, with and without cache policy, and the tensor prefetch with `.evict_last`.
example : Decode.op env "cp.async.bulk.prefetch.L2.global" [at' "%rd0", .register "%r1"] =
    .ok (.prefetchBulk 8 0 (.reg 1) none) := rfl
example : Decode.op env "cp.async.bulk.prefetch.L2.global.L2::cache_hint"
    [at' "%rd0", .register "%r1", .register "%rd1"] =
    .ok (.prefetchBulk 8 0 (.reg 1) (some (.reg 9))) := rfl
example : Decode.op env "cp.async.bulk.prefetch.L2.global.L2::evict_last"
    [at' "%rd0", .register "%r1"] = .ok (.prefetchBulk 8 0 (.reg 1) none) := rfl
example : Decode.op env "cp.async.bulk.prefetch.tensor.2d.L2.global.L2::evict_last"
    [.address [.register "%rd0", .vector [.literal "0", .literal "1"]]] =
    .ok (.prefetchTensor (.reg 8) [.imm 0, .imm 1] .tile none) := rfl

/-! ## Thread events -/

private def L : Launch := { grid := 2, block := 32, params := fun _ => none, clusterSize := 2 }
-- Thread 0 is in CTA 0 of the cluster of CTAs 0 and 1.
private def t : TState := { regs := fun
  | 0 => some (.bits 32 64)
  | 1 => some (.bits 64 4096)
  | 2 => some (.bits 32 64)
  | 3 => some (.bits 32 128)
  | 4 => some (.ptr 32 false (.shared 0 1) 64)
  | 5 => some (.ptr 32 false (.shared 0 1) 128)
  | 6 => some (.bits 16 3)
  | 7 => some (.bits 32 0)
  | 8 => some (.bits 32 3)
  | 9 => some (.bits 64 7)
  | 10 => some (.bits 32 40)
  | 11 => some (.bits 32 72)
  | 12 => some (.bits 16 0)
  | 13 => some (.bits 16 4)
  | 14 => some (.bits 32 256)
  | 15 => some (.bits 64 4104)
  | 16 => some (.bits 16 1)
  | 17 => some (.bits 16 2)
  | 18 => some (.bits 32 132)
  | _ => none }

private def acc (l : Loc) (n : Nat) : Acc := { loc := l, size := n }
private def sh (c a : Nat) : Loc := ⟨.shared, c, a⟩
private def gl (a : Nat) : Loc := ⟨.global, 0, a⟩
private def eff (r w : Option (List Byte)) (n : Bool) : AsyncCopy.Effects :=
  { readBytes := r, writeBytes := w, notified := n }
private def sp (s d : Acc) (c : AsyncCopy.Completion) : AsyncCopy.Spec :=
  { src := s, dst := d, completion := c }

/-- The copy spec and continuation (pc, sub) of an issue event, or the fault. -/
private def issued : Tmpl → Option (AsyncCopy.Spec × Nat × Nat)
  | .copy s u => some (s, u.pc, u.sub)
  | _ => none
private def fault : Tmpl → Option Fault
  | .ub f => some f
  | _ => none
private def bc (dir : BulkDir) (d s : Nat) (size : Opnd) (mbar : Option (Nat × Int))
    (mc : Option (Nat × Opnd) := none) (oob : Option (Opnd × Opnd) := none) : Op :=
  .cpBulk ⟨dir, d, 0, s, 0, size, mbar, mc, oob, none, none, none, none⟩

-- Global to the executing CTA: 64 bytes, completed on the mbarrier at shared address 128.
example : issued (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)))) =
    some ((sp (acc (gl 4096) 64) (acc (sh 0 64) 64) (.mbarrier (sh 0 128))), 1, 0) := rfl
example : issued (tmaTmpl L 0 t (bc .globalToCta 0 1 (.imm 32) (some (3, 0)))) =
    some ((sp (acc (gl 4096) 32) (acc (sh 0 64) 32) (.mbarrier (sh 0 128))), 1, 0) := rfl
-- Global to a destination in the cluster: the destination and mbarrier lie in one CTA.
example : issued (tmaTmpl L 0 t (bc .globalToCluster 4 1 (.reg 2) (some (5, 0)))) =
    some ((sp (acc (gl 4096) 64) (acc (sh 1 64) 64) (.mbarrier (sh 1 128))), 1, 0) := rfl
example : issued (tmaTmpl L 0 t (bc .globalToCluster 0 1 (.reg 2) (some (3, 0)))) =
    some ((sp (acc (gl 4096) 64) (acc (sh 0 64) 64) (.mbarrier (sh 0 128))), 1, 0) := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCluster 0 1 (.reg 2) (some (5, 0)))) =
    some .badValue := rfl
-- Shared to a different CTA of the cluster, with the mbarrier in that CTA.
example : issued (tmaTmpl L 0 t (bc .ctaToCluster 4 14 (.reg 2) (some (5, 0)))) =
    some ((sp (acc (sh 0 256) 64) (acc (sh 1 64) 64) (.mbarrier (sh 1 128))), 1, 0) := rfl
example : fault (tmaTmpl L 0 t (bc .ctaToCluster 0 14 (.reg 2) (some (3, 0)))) =
    some .badValue := rfl
example : fault (tmaTmpl L 0 t (bc .ctaToCluster 4 14 (.reg 2) (some (3, 0)))) =
    some .badValue := rfl
-- Shared to global completes through the bulk group of the issuing thread.
example : issued (tmaTmpl L 0 t (bc .ctaToGlobal 1 14 (.reg 2) none)) =
    some ((sp (acc (sh 0 256) 64) (acc (gl 4096) 64) (.bulkGroup)), 1, 0) := rfl
-- The size is a positive multiple of 16 and both addresses are 16-byte aligned.
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 10) (some (3, 0)))) =
    some .misaligned := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 7) (some (3, 0)))) =
    some .misaligned := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 11 1 (.reg 2) (some (3, 0)))) =
    some .misaligned := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 15 (.reg 2) (some (3, 0)))) =
    some .misaligned := rfl
example : fault (tmaTmpl L 0 t (bc .ctaToGlobal 1 11 (.reg 2) none)) = some .misaligned := rfl
example : fault (tmaTmpl L 0 t (bc .ctaToCluster 4 11 (.reg 2) (some (5, 0)))) =
    some .misaligned := rfl
-- A mbarrier address must be 8-byte aligned.
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (18, 0)))) =
    some .misaligned := rfl
-- A form whose mbarrier does not match the direction has no rule.
example : fault (tmaTmpl L 0 t (bc .ctaToGlobal 1 14 (.reg 2) (some (3, 0)))) = some .noRule :=
  rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) none)) = some .noRule := rfl
example : fault (tmaTmpl L 0 t (bc .ctaToCluster 4 14 (.reg 2) none)) = some .noRule := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)) (some (16, .reg 6))))
    = some .noRule := rfl
-- `.ignore_oob` with both operands zero is the plain copy; any other value is undefined.
example : issued (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)) none
    (some (.reg 7, .reg 7)))) = issued (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0))))
    := rfl
example : issued (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)) none
    (some (.imm 0, .imm 0)))) =
    some ((sp (acc (gl 4096) 64) (acc (sh 0 64) 64) (.mbarrier (sh 0 128))), 1, 0) := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)) none
    (some (.reg 7, .reg 8)))) = some .badValue := rfl
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)) none
    (some (.reg 8, .reg 7)))) = some .badValue := rfl
-- The cache policy must be a defined 64-bit value and has no other effect.
example : issued (tmaTmpl L 0 t (.cpBulk ⟨.globalToCta, 0, 0, 1, 0, .reg 2, some (3, 0), none, none,
    some (.reg 9), none, none,
        none⟩)) = issued (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)))) := rfl
example : fault (tmaTmpl L 0 t (.cpBulk ⟨.globalToCta, 0, 0, 1, 0, .reg 2, some (3, 0), none, none,
    some (.reg 20), none, none, none⟩)) = some .uninitialized := rfl

/-! ## Multicast: one copy per destination CTA of the mask, in rank order -/

private def mc (mask : Nat) (sub : Nat := 0) : Tmpl :=
  tmaTmpl L 0 { t with sub := sub } (bc .globalToCluster 0 1 (.reg 2) (some (3, 0))
    (some (16, .reg mask)))
-- Mask 0b11 reaches ranks 0 and 1: sub-step 0 stays on the instruction, sub-step 1 leaves it.
example : issued (mc 6) = some ((sp (acc (gl 4096) 64) (acc (sh 0 64) 64) (.mbarrier (sh 0 128))),
    0, 1)
  := rfl
example : issued (mc 6 1) =
    some ((sp (acc (gl 4096) 64) (acc (sh 1 64) 64) (.mbarrier (sh 1 128))), 1, 0) := rfl
-- A mask of rank 1 alone is one copy to CTA 1, and rank 0 alone one copy to CTA 0.
example : issued (mc 16) = some ((sp (acc (gl 4096) 64) (acc (sh 0 64) 64) (.mbarrier (sh 0 128))),
    1, 0)
  := rfl
example : issued (mc 17) = some ((sp (acc (gl 4096) 64) (acc (sh 1 64) 64) (.mbarrier (sh 1 128))),
    1, 0)
  := rfl
-- A third sub-step of a two-bit mask, a rank outside the cluster and an empty mask are undefined.
example : fault (mc 6 2) = some .badValue := rfl
example : fault (mc 13) = some .badValue := rfl
example : fault (mc 12) = some .badValue := rfl
-- A multicast needs the `.shared::cluster` destination.
example : fault (tmaTmpl L 0 t (bc .globalToCta 0 1 (.reg 2) (some (3, 0)) (some (16, .reg 6))))
    = some .noRule := rfl

/-! ## Linear prefetch -/

private def pf (a : Nat) (n : Opnd) : Op := .prefetchBulk a 0 n none
private def prefetched : Tmpl → Option (Acc × Nat)
  | .bulkPrefetch a u => some (a, u.pc)
  | _ => none

example : prefetched (tensorPrefetchTmpl L 0 t (pf 1 (.reg 2))) = some (acc (gl 4096) 64, 1) := rfl
example : prefetched (tensorPrefetchTmpl L 0 t (pf 1 (.imm 16))) = some (acc (gl 4096) 16, 1) := rfl
example : fault (tensorPrefetchTmpl L 0 t (pf 1 (.reg 10))) = some .misaligned := rfl
example : fault (tensorPrefetchTmpl L 0 t (pf 15 (.reg 2))) = some .misaligned := rfl
example : fault (tensorPrefetchTmpl L 0 t (.prefetchBulk 1 0 (.reg 2) (some (.reg 20)))) =
    some .uninitialized := rfl
example : prefetched (tensorPrefetchTmpl L 0 t (.prefetchBulk 1 0 (.reg 2) (some (.reg 9)))) =
    some (acc (gl 4096) 64, 1) := rfl

/-! ## `CopyOk` of a linear copy completed on an mbarrier -/

private def b0 : Byte := (Value.bits 8 1, 0)
private def b1 : Byte := (Value.bits 8 2, 0)
private def spec : AsyncCopy.Spec :=
  (sp (acc (gl 4096) 2) (acc (sh 0 64) 2) (.mbarrier (sh 0 128)))
private def bulkSpec : AsyncCopy.Spec := { spec with completion := .bulkGroup }

example : AsyncCopy.CopyOk spec
    (eff (some [b0, b1]) (some [b0, b1]) true) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro bs h; simp only [eff, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · intro bs h; cases h; simp [eff, spec, sp, acc, AsyncCopy.sourceBytes]
  · intro _; exact ⟨⟨_, rfl⟩, _, rfl⟩
  · exact ⟨fun j bs h => by simp [eff] at h, fun j bs h => by simp [eff] at h⟩
example : ¬ AsyncCopy.CopyOk spec
    (eff (some [b0, b1]) (some [b1, b0]) false) := by
  intro h
  have hw := h.2.2.1 _ rfl
  simp [eff, spec, sp, acc, AsyncCopy.sourceBytes, b0, b1] at hw
-- A bulk-group copy has no completion notification.
example : ¬ AsyncCopy.CopyOk bulkSpec
    (eff (some [b0, b1]) (some [b0, b1]) true) := by
  intro h
  obtain ⟨⟨m, hm⟩, _⟩ := h.2.2.2.1 rfl
  simp [bulkSpec] at hm
-- A notification without the write is not valid.
example : ¬ AsyncCopy.CopyOk spec (eff (some [b0, b1]) none true) := by
  intro h
  obtain ⟨_, bs, hb⟩ := h.2.2.2.1 rfl
  cases hb

end

end PTX.Tests.AsyncLinearCopy
