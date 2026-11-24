-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootClass
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Safety.Tensor
public import Kernels.InklingRelDecode.Proof.Thread.ShapeCopyEvent
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Protocol.RingKvFoot

@[expose] public section

/-!
# The tensor copies of a tracked thread write only the K and V rings

The tensor copies of the program are the prologue's twelve (`ProA.ptcSite i`) and the loader's
eight. `CopyFacts.copy_event_state` classifies a copy event and its spec by the thread machines
and asks for `Frame.Tracked`; `copy_spec_at` is its form for one event the machine tracked through
(`TT`): the spec is `EvW.kvCopySpec` of the thread's CTA at a destination `dst` with
`[dst, dst + 8192)` inside the rings `[sharedBase, sharedBase + 196608)`, and the issuing state is a
prologue copy site or a loader copy site.

`async_write_foot` is the footprint of a write stage of such a copy: the byte it writes is in the
rings of the issuing thread's CTA.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The destination of a prologue copy is a box of the rings. -/
theorem ptc_dst_range (hpre : Pre Q L mem0) {g : Nat} {dt : ProA.Dat} {i : Nat} (hi : i < 12) :
    L.sharedBase ≤ ProA.copyDst L g dt i ∧
      ProA.copyDst L g dt i + 8192 ≤ L.sharedBase + 196608 := by
  have hsb : ProA.SbRoom L := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    unfold ProA.SbRoom
    omega
  rw [ProA.copyDst_form L g dt hsb hi]
  have h1 := ProA.half_lt dt (i / 4)
  have h2 : i / 4 < 3 := by omega
  have h3 : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have h4 : i % 4 / 2 < 2 := by omega
  constructor
  · omega
  · -- the largest destination is `16384 + 65536 + 98304 + 8192`
    have : 16384 * ProA.half dt (i / 4) + 32768 * (i / 4) + 98304 * (i % 2) +
        8192 * (i % 4 / 2) + 8192 ≤ 196608 := by omega
    omega

/-- The destination of a loader copy is a box of the rings. -/
theorem ld_dst_range {L : Launch} {d : Loader.D} {b : Bool × Nat × Nat}
    (hb : EvW.ldBox d.site = some b) :
    L.sharedBase ≤ EvW.ldDst L d b.1 b.2.1 b.2.2 ∧
      EvW.ldDst L d b.1 b.2.1 b.2.2 + 8192 ≤ L.sharedBase + 196608 := by
  have h1 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  have hb' : (b.2.1 = 0 ∨ b.2.1 = 1) ∧ (b.2.2 = 0 ∨ b.2.2 = 1) := by
    revert hb
    cases hs : d.site <;> simp [EvW.ldBox] <;> intro h <;> subst h <;> simp
  unfold EvW.ldDst
  rcases hb' with ⟨h2 | h2, h3 | h3⟩ <;> rw [h2, h3] <;> split_ifs <;> omega

/-- A loader event that is a tensor issue is at a copy site. -/
theorem ldShape_issue {g : Nat} {d : Loader.D} {e : Event} (h : EvW.LdShape Q L g d e)
    (hk : ∃ a sp, e.kind = .tensorIssue a sp) :
    ∃ b, EvW.ldBox d.site = some b ∧
      ∃ pc, e = ⟨pc, .tensorIssue Q.kvMap (EvW.ldCopy Q L g d b)⟩ := by
  obtain ⟨a0, sp0, hk0⟩ := hk
  unfold EvW.LdShape at h
  split at h
  all_goals first
    | (obtain ⟨b, hb, he⟩ := h; exact ⟨b, hb, _, he⟩)
    | (exfalso; rcases h with ⟨_, _, rfl, _⟩; cases hk0)

/-- A loader event that is a tensor issue is at a copy site (for every counter). -/
theorem ldShapeW_issue {g : Nat} {d : Loader.D} {e : Event} (h : EvW.LdShapeW Q L g d e)
    (hk : ∃ a sp, e.kind = .tensorIssue a sp) :
    ∃ b, EvW.ldBox d.site = some b ∧
      ∃ pc, e = ⟨pc, .tensorIssue Q.kvMap (EvW.ldCopyW Q L g d b)⟩ := by
  obtain ⟨a0, sp0, hk0⟩ := hk
  unfold EvW.LdShapeW at h
  split at h
  all_goals first
    | (obtain ⟨b, hb, he⟩ := h; exact ⟨b, hb, _, he⟩)
    | (exfalso; rcases h with ⟨_, _, rfl, _⟩; cases hk0)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
include hpre hX hS

/-- **The spec of a tensor copy of a tracked thread, for every counter of the loader.** As
`copy_spec_at`, with the loader's destination anywhere from `65536` bytes below the rings to their
end, or wrapped to the top `65536` bytes of the 32-bit space (`EvW.ldDstW_range`). -/
theorem copy_spec_atW {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : ∃ a sp, e.kind = .tensorIssue a sp) (hTT : TT Q L X (g, k)) :
    ∃ (col row dst : Nat) (bar : Loc), e.kind = .tensorIssue Q.kvMap
        (EvW.kvCopySpec Q (g / L.block) col row dst bar) ∧
      ((L.sharedBase ≤ dst + 65536 ∧ dst + 8192 ≤ L.sharedBase + 196608) ∨
        2 ^ 32 - 65536 ≤ dst) ∧
      ((∃ d : ProA.D, ∃ i < 12, St Q L X g k = some (some (.d (.pro d))) ∧
          d.site = ProA.ptcSite i) ∨
        ∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P)))) := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    obtain ⟨_, _, h⟩ := hk
    cases h
  obtain ⟨s, hσ⟩ := event_state_at hS hX he hub hTT
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : tensorOp ins.op = true := by
    cases hq : tensorOp ins.op
    · exfalso
      obtain ⟨a, sp, h⟩ := hk
      exact fires_notTensor (eventTmpl_notTensor hq) hf a sp h
    · rfl
  have hpw : TSt.pc s ∈ copyPcs := OpPcsFast.mem kernel_copy_pcs hc hop
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  have hsome : ∃ u, o' = some u := by
    cases o' with
    | some u => exact ⟨u, rfl⟩
    | none =>
      exfalso
      obtain ⟨t', -, hf'⟩ := hF
      obtain ⟨a, sp, h⟩ := hk
      exact fires_none_notTensor hf' a sp h
  obtain ⟨u, rfl⟩ := hsome
  have hr := treach_stateAt hpre hg hσ
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (by exact worker_pc_notCopy w.site)
    | idle d => exact absurd hpw (idle_pc_notCopy d.site)
    | mma d _ => exact absurd hpw (mma_pc_notCopy d.site)
    | exit x => exact absurd hpw (exit_pc_notCopy x.site)
    | loader d P =>
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      have hsh := EvW.loader_shapeW hpre (hr.2) ⟨t', ⟨ha, hi.2⟩, hf'⟩
      obtain ⟨b, hb, pc, he3⟩ := ldShapeW_issue hsh hk
      have hsr := hpre.sharedRange
      unfold sharedBytes at hsr
      have hr' := EvW.ldDstW_range (L := L) (d := d) hsr hb
      refine ⟨EvW.ldCol L g d b.1 b.2.2, EvW.ldRow L g d b.2.1,
        EvW.ldDstW L d b.1 b.2.1 b.2.2, EvW.ldReadyW L (g / L.block) d.i, ?_, hr',
        .inr ⟨d, P, hσ⟩⟩
      rw [he3]
      rfl
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (dstart_pc_notCopy d.site)
    | sm d => exact absurd hpw (sm_pc_notCopy d.site)
    | epi d => exact absurd hpw (epi_pc_notCopy d.site)
    | pro d =>
      obtain ⟨i, hi, hs⟩ := ptc_index _ (pro_pc_copy d.site hpw)
      obtain ⟨tm, -, hpro⟩ := hr.2
      have he2 := ProA.ptc_event hpre hi hpro (fired_pro hF) hs
      have hr' := ptc_dst_range hpre (g := g) (dt := d.dt) hi
      refine ⟨ProA.copyX L g d.dt i, ProA.copyY L g d.dt i, ProA.copyDst L g d.dt i,
        (EvD.kvReadyOf (i / 4)).loc L (g / L.block), ?_, .inl ⟨by omega, hr'.2⟩,
        .inl ⟨d, i, hi, hσ, hs⟩⟩
      rw [he2]

/-- **The spec of a tensor copy of a tracked thread.** -/
theorem copy_spec_at (hrg : LdRng Q L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hk : ∃ a sp, e.kind = .tensorIssue a sp) (hTT : TT Q L X (g, k)) :
    ∃ (col row dst : Nat) (bar : Loc), e.kind = .tensorIssue Q.kvMap
        (EvW.kvCopySpec Q (g / L.block) col row dst bar) ∧
      L.sharedBase ≤ dst ∧ dst + 8192 ≤ L.sharedBase + 196608 ∧
      ((∃ d : ProA.D, ∃ i < 12, St Q L X g k = some (some (.d (.pro d))) ∧
          d.site = ProA.ptcSite i) ∨
        ∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P)))) := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    obtain ⟨_, _, h⟩ := hk
    cases h
  obtain ⟨s, hσ⟩ := event_state_at hS hX he hub hTT
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : tensorOp ins.op = true := by
    cases hq : tensorOp ins.op
    · exfalso
      obtain ⟨a, sp, h⟩ := hk
      exact fires_notTensor (eventTmpl_notTensor hq) hf a sp h
    · rfl
  have hpw : TSt.pc s ∈ copyPcs := OpPcsFast.mem kernel_copy_pcs hc hop
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  have hsome : ∃ u, o' = some u := by
    cases o' with
    | some u => exact ⟨u, rfl⟩
    | none =>
      exfalso
      obtain ⟨t', -, hf'⟩ := hF
      obtain ⟨a, sp, h⟩ := hk
      exact fires_none_notTensor hf' a sp h
  obtain ⟨u, rfl⟩ := hsome
  have hr := treach_stateAt hpre hg hσ
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (by exact worker_pc_notCopy w.site)
    | idle d => exact absurd hpw (idle_pc_notCopy d.site)
    | mma d _ => exact absurd hpw (mma_pc_notCopy d.site)
    | exit x => exact absurd hpw (exit_pc_notCopy x.site)
    | loader d P =>
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      have hsh := EvW.loader_shape hpre (hr.2) (hrg hg hσ) ⟨t', ⟨ha, hi.2⟩, hf'⟩
      obtain ⟨b, hb, pc, he3⟩ := ldShape_issue hsh hk
      have hr' := ld_dst_range (L := L) (d := d) hb
      refine ⟨EvW.ldCol L g d b.1 b.2.2, EvW.ldRow L g d b.2.1,
        EvW.ldDst L d b.1 b.2.1 b.2.2, EvW.kvReady L (g / L.block) (d.i % 3), ?_, hr'.1, hr'.2,
        .inr ⟨d, P, hσ⟩⟩
      rw [he3]
      rfl
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (dstart_pc_notCopy d.site)
    | sm d => exact absurd hpw (sm_pc_notCopy d.site)
    | epi d => exact absurd hpw (epi_pc_notCopy d.site)
    | pro d =>
      obtain ⟨i, hi, hs⟩ := ptc_index _ (pro_pc_copy d.site hpw)
      obtain ⟨tm, -, hpro⟩ := hr.2
      have he2 := ProA.ptc_event hpre hi hpro (fired_pro hF) hs
      have hr' := ptc_dst_range hpre (g := g) (dt := d.dt) hi
      refine ⟨ProA.copyX L g d.dt i, ProA.copyY L g d.dt i, ProA.copyDst L g d.dt i,
        (EvD.kvReadyOf (i / 4)).loc L (g / L.block), ?_, hr'.1, hr'.2, .inl ⟨d, i, hi, hσ, hs⟩⟩
      rw [he2]

/-- **A write stage of a tensor copy of a tracked thread** writes one byte of the issuing thread's
CTA below the end of the rings (at most `65536` bytes below their start), or one wrapped to the top
`65536` bytes of the 32-bit space; it is never at or above `sharedBase + 196608` inside the shared
window. -/
theorem async_write_foot {i : EvId} {x y z : Nat} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites (.async i (.write (.load x y z))) a bs) (hTT : TT Q L X i) :
    a.loc.space = .shared ∧ a.loc.cta = i.1 / L.block ∧
      (a.loc.addr + a.size ≤ L.sharedBase + 196608 ∨ 2 ^ 32 - 65536 ≤ a.loc.addr) := by
  obtain ⟨o, addr, b, ho, ⟨pc, hget⟩, hloc, -, hsz, -⟩ := hw
  have hg : i.1 < L.threads := Frame.lt_of_get hX hget
  obtain ⟨col, row, dst, bar, hk, hd, -⟩ := copy_spec_atW hpre hX hS hg hget
    ⟨addr, o.spec, rfl⟩ hTT
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, hspec⟩ := hk
  rw [hspec] at hloc
  obtain ⟨h1, h2, h3, h4⟩ := Ring.Foot.copy_foot Q (i.1 / L.block) col row dst bar hloc
  refine ⟨h1, h2, by omega⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
