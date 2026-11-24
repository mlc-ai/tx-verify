-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Lemmas.Flow.WaitAcquire

@[expose] public section

/-! # The Tensor Memory allocation, from the MMA warp's run invariant

Only the MMA warp's sites are paired Tensor Memory instructions (`kernel_tmem_pcs`), so every
allocation, relinquishment and deallocation fires at an MMA state (`tmem_state`), where the run
invariant counts the thread's earlier operations (`Mma.Counts.tmem`): the allocation of 512
columns into the base word is the first, the relinquishment the second, the deallocation the
third, and the thread exits after the three (`TmemFacts.event`, `TmemFacts.exit`). The
deallocation frees the column the read-back of the base word returned (`Counts.baseRead`). The
events on barrier 2 are the two `bar.sync 2, 416` after the allocation and after the
relinquishment (`Counts.bar2`); the deallocation follows the second and the successful acquire
poll of the own handshake barrier (`Counts.dealloc`). Lane 0's address store is the event after
its allocation, before barrier 2 (`Counts.allocWrite`, `Counts.wrote`).

The facts that hold of every thread because only warp 12 makes the event are stated as fields;
those whose other roles' part is another package's are stated for warp 12 (`Facts.Mma.*`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Only the MMA warp makes paired Tensor Memory operations -/

/-- The positions of the paired Tensor Memory instructions. -/
abbrev tmemPcs : List Nat := [Flow.tmemAlloc_0, Flow.tmemRelinquish_0, Flow.tmemDealloc_0]

theorem kernel_tmem_pcs : OpPcsFast kernel.code tmemOp tmemPcs = true := by
  decide +kernel

theorem Loader.site_not_tmem (s : Loader.Site) : s.pc ∉ tmemPcs := by
  cases s <;> site_decide

theorem Store.site_not_tmem (s : Store.Site) : s.pc ∉ tmemPcs := by
  cases s <;> site_decide

theorem Idle.site_not_tmem (s : Idle.Site) : s.pc ∉ tmemPcs := by
  cases s <;> site_decide

theorem Correction.site_not_tmem (s : Correction.Site) : s.pc ∉ tmemPcs := by
  cases s <;> site_decide

theorem Softmax.site_not_tmem (s : Softmax.Site) : s.pc ∉ tmemPcs := by
  cases s <;> site_decide

/-- **A paired Tensor Memory operation fires at an MMA state** of a thread of warp 12. -/
theorem tmem_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩) :
    warpOf L g = 12 ∧ ∃ (d : Mma.D) (t : TState) (ins : Instr) (u : TState),
      Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧ t.pc = d.site.pc ∧
      t.sub = d.site.sub ∧ Holds t.regs (Mma.facts L g d) ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) ⟨pc, .tc (.resource grp dst act)⟩
        (some u) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  cases o with
  | none => exact absurd (fires_none_ends hf) (by rintro (⟨f, h⟩ | h) <;> cases h)
  | some u =>
  have hpc := OpPcsFast.mem kernel_tmem_pcs hc (fires_resource_op hf rfl)
  rcases d with p | r
  · exact absurd (pro_event hpre hX he hσ (fun f h => by cases h)).proKind
      (by simp [Prologue.ProKind])
  cases r with
  | idle s => exact absurd hpc (Idle.site_not_tmem s.site)
  | loader l => exact absurd hpc (Loader.site_not_tmem l.site)
  | store s => exact absurd hpc (Store.site_not_tmem s.site)
  | softmax s => exact absurd hpc (Softmax.site_not_tmem s.site)
  | corr c => exact absurd hpc (Correction.site_not_tmem c.site)
  | mma m =>
    have hw : RoleKind.Warp .mma (warpOf L g) :=
      role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k
        (.mma m) hσ
    exact ⟨hw, m, t, ins, u, hJ, hi.1, hat.1, hat.2.1, hat.2.2.2.2, hc, hf⟩

/-- The site of a paired Tensor Memory operation: the allocation, the relinquishment or the
deallocation, with its operation. -/
theorem tmem_site (hpre : Pre P L mem0) {g pc : Nat} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} {d : Mma.D} {t u : TState} {ins : Instr} (hs : t.sub = d.site.sub)
    (h : Holds t.regs (Mma.facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) ⟨pc, .tc (.resource grp dst act)⟩
      (some u)) :
    (d.site = .alloc ∧ grp = .two ∧ dst = some (Mma.baseAt L g) ∧ act = .alloc 512) ∨
    (d.site = .relinquish ∧ grp = .two ∧ act = .relinquish) ∨
    (d.site = .dealloc ∧ grp = .two ∧ ∃ a, act = .dealloc a 512 ∧
      ∀ col, d.base = b32 col → a = col % 2 ^ 32) := by
  have hop := Mma.tmemOp_site hpre hs h hc hf
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site <;> simp [Tmem.Pair.isTmemOp, Mma.tmemEv] at hop
  · have hk := Mma.alloc_site hpre rfl hs h hc hf
    simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
    exact .inl ⟨rfl, hk.1, hk.2.1, hk.2.2⟩
  · code_at hc
    subst hc
    have hk := fires_tcRelinquish_some hf
    simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
    exact .inr (.inl ⟨rfl, hk.1, hk.2.2⟩)
  · obtain ⟨a, hk, hb⟩ := Mma.dealloc_site rfl h hc hf
    simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
    exact .inr (.inr ⟨rfl, hk.1, a, hk.2.2, hb⟩)

/-- The bytes of a 32-bit value rebuild it. -/
theorem rebuild_b32 (col : Nat) : rebuild 3 ((b32 col).toBytes.map some) = .ok (b32 col) := by
  simp [rebuild, b32, Value.toBytes, Value.bytes, Value.byteAt, List.range, List.range.loop,
    pure, Except.pure]

/-! ### `TmemFacts` -/

/-- **The field `TmemFacts.event`.** -/
theorem TmemFacts_event (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (_ : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩) :
    warpOf L g = 12 ∧ grp = .two ∧ Tmem.Pair.TmemShape (Tmem.Pair.tmemOps ((X.tr g).take k)) act ∧
      ∀ n, act = .alloc n → dst = some (baseLoc L (ctaOf L g)) := by
  obtain ⟨hw, d, t, ins, u, hJ, -, -, hs, h, hc, hf⟩ := tmem_state hpre hX ht he
  rw [hJ.tmem]
  rcases tmem_site hpre hs h hc hf with ⟨hd, rfl, rfl, rfl⟩ | ⟨hd, rfl, rfl⟩ |
    ⟨hd, rfl, a, rfl, -⟩ <;> rw [hd]
  · exact ⟨hw, rfl, rfl, fun _ _ => rfl⟩
  · exact ⟨hw, rfl, rfl, fun _ h => by cases h⟩
  · exact ⟨hw, rfl, ⟨a, rfl⟩, fun _ h => by cases h⟩

/-- **The field `TmemFacts.exit`.** -/
theorem TmemFacts_exit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} (_ : g < L.threads) (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) : Tmem.Pair.tmemOps ((X.tr g).take k) = 3 := by
  obtain ⟨d, t, ins, o, -, hJ, -, -, -, -, hc, hf⟩ :=
    mma_state hpre hX ht he hw (by simp [Prologue.ProKind]) (fun f h => by cases h)
  rw [hJ.tmem, Mma.exit_site hc hf rfl]
  rfl

/-- **The field `TmemFacts.dealloc_base`.** -/
theorem TmemFacts_dealloc_base (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc}
    {a n : Nat} (_ : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    ∃ j < k, ∃ pcr ra bs, X.get (g, j) = some ⟨pcr, .rd ra bs⟩ ∧
      ra.loc = baseLoc L (ctaOf L g) ∧ ra.size = 4 ∧
      ∀ col, bs = (b32 col).toBytes.map some → a = col % 2 ^ 32 := by
  obtain ⟨-, d, t, ins, u, hJ, -, -, hs, h, hc, hf⟩ := tmem_state hpre hX ht he
  rcases tmem_site hpre hs h hc hf with ⟨-, -, -, h'⟩ | ⟨-, -, h'⟩ | ⟨hd, -, a', ha, hb⟩
  · cases h'
  · cases h'
  obtain ⟨rfl, -⟩ := Tmem.Request.dealloc.inj ha
  obtain ⟨x, hx, ra, bs, hk, hloc, hsz, hreb⟩ := hJ.baseRead (by rw [hd]; decide)
  obtain ⟨j, hj, hgj⟩ := mem_take_get hx
  refine ⟨j, hj, x.pc, ra, bs, by rw [hgj, ← hk], hloc, hsz, fun col hcol => hb col ?_⟩
  rw [hcol, rebuild_b32] at hreb
  exact (Except.ok.inj hreb).symm

end
end PTX.Kernels.FlashAttn4Fwd.Proof
