-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryGlobal
public import Lemmas.Protocol.Region

@[expose] public section

/-! # Where the kernel's accesses of global memory are

Every access of a global byte is a tensor load reading the `A` or `B` matrix or a tensor store
writing the `D` matrix (`global_access`). Each access is placed by the event that issues it: a
thread's reads are of its CTA's response buffer or base word and its writes are to shared memory
(`ThreadFacts.access_region`, `write_shared`); an MMA reads shared operands; a tensor store reads
its staging buffer (`ThreadFacts.cons_out`) and writes through the `D` map
(`ThreadFacts.store_map`); a tensor load reads through the `A` or `B` map and writes a stage
(`ThreadFacts.tensor_issue`); a cancellation response is written to the shared response buffer
(`RingEvent.clc`); no linear copy is issued (`RingEvent.copy`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory

open PTX AsyncCopy TensorDescriptor

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A one-byte footprint covers its own location. -/
theorem loc_of_one {a : Acc} {l : Loc} (hc : a.Covers l) (hn : a.size = 1) : a.loc = l := by
  obtain ⟨⟨sp, cta, addr⟩, size, acq, rel, scope⟩ := a
  obtain ⟨sp', cta', addr'⟩ := l
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only at h1 h2 h3 h4 hn ⊢
  subst h1 h2 hn
  congr 1
  omega

/-- The operand map a tensor load reads is the `A` or the `B` map. -/
theorem operand_base (hpre : Pre P L mem0) {a b : Nat} {cls : AllocationClass}
    (hm : L.tensorMaps a = some ⟨1, Fp16Gemm8192.mapA b cls⟩)
    (hp : L.paramObjects "gemm_kernel_param_0" = some (mapParam "gemm_kernel_param_0", a) ∨
      L.paramObjects "gemm_kernel_param_1" = some (mapParam "gemm_kernel_param_1", a)) :
    b = P.aBase ∨ b = P.bBase := by
  rcases hp with hp | hp
  · rw [hpre.paramA] at hp
    obtain rfl : P.aMap = a := (Prod.mk.inj (Option.some.inj hp)).2
    rw [hpre.mapA] at hm
    have h := congrArg (fun s : Σ n, Descriptor n => s.2.base) (Option.some.inj hm)
    exact .inl (by simpa [Fp16Gemm8192.mapA, encodeTiled] using h.symm)
  · rw [hpre.paramB] at hp
    obtain rfl : P.bMap = a := (Prod.mk.inj (Option.some.inj hp)).2
    rw [hpre.mapB] at hm
    have h := congrArg (fun s : Σ n, Descriptor n => s.2.base) (Option.some.inj hm)
    exact .inr (by simpa [Fp16Gemm8192.mapA, Fp16Gemm8192.mapB, encodeTiled] using h.symm)

/-- **The accesses of a byte outside shared memory**, which is global: a tensor load's read of the
`A` or `B` matrix, or a tensor store's write of the `D` matrix. -/
theorem global_access (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {ref : Ref} {a : Acc} {w : Bool} {l : Loc} (h : X.Intent ref a w)
    (hc : a.Covers l) (hs : l.space ≠ .shared) :
    (w = false ∧ (InMatrix P.aBase l ∨ InMatrix P.bBase l)) ∨
      (w = true ∧ InMatrix P.dBase l ∧ ∃ i x y k addr s, ref = .async i (.write (.store x y k)) ∧
        X.TensorStoreIssue i addr s ∧ TensorStore.writeLoc s x y k = some l) := by
  have hsp : a.loc.space ≠ .shared := fun h => hs (hc.1.trans h)
  rcases ref with e | ⟨i, p⟩
  · exfalso
    rcases h with ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨old, new, pc, hget⟩
    · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      rcases (ht.access_region (Frame.lt_of_get hX hget) hget hσ).1 a bs rfl with
        ⟨hl, -⟩ | ⟨hl, -⟩ <;>
        rw [hl] at hsp <;> exact (hsp rfl).elim
    · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      rw [ht.write_shared (Frame.lt_of_get hX hget) hget hσ rfl] at hsp
      exact (hsp rfl).elim
    · exact no_rmw hX ht hget
  cases p with
  | mmaRead isB idx =>
    obtain ⟨-, -, hf⟩ := h
    rw [Execution.mmaFootprint_shared hf] at hsp
    exact (hsp rfl).elim
  | readStore x y k =>
    obtain ⟨-, s, addr, ⟨pc, hget⟩, hl, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨c, rfl⟩ := (ht.access_region (Frame.lt_of_get hX hget) hget hσ).2.2 addr s rfl
    obtain ⟨-, -, hr, -⟩ := ht.cons_out (Frame.lt_of_get hX hget) hget hσ
    obtain ⟨s0, hs0, hrd, -⟩ := hr addr s rfl
    rw [(hrd x y k a.loc hl).1] at hsp
    exact (hsp rfl).elim
  | writeStore x y k =>
    obtain ⟨rfl, s, addr, ⟨pc, hget⟩, hl, hn⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨hp, hm⟩ := ht.store_map (Frame.lt_of_get hX hget) hget hσ rfl
    rw [hpre.paramD] at hp
    obtain rfl : P.dMap = addr := (Prod.mk.inj (Option.some.inj hp)).2
    rw [hpre.mapD] at hm
    rw [loc_of_one hc hn] at hl
    exact .inr ⟨rfl, store_in (Option.some.inj hm).symm hl, i, x, y, k, P.dMap, s, rfl,
      ⟨pc, hget⟩, hl⟩
  | readLoad x y k =>
    obtain ⟨rfl, s, addr, ⟨pc, hget⟩, hl, hn⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨ld, b, j, hd, hsite, hmb, ⟨base, cls, origin, hsp', hm, hpm⟩, -⟩ :=
      ht.tensor_issue (Frame.lt_of_get hX hget) hget hσ rfl
    rw [loc_of_one hc hn, hsp'] at hl
    refine .inl ⟨rfl, ?_⟩
    rcases operand_base hpre hm hpm with rfl | rfl
    · exact .inl (copy_in hl)
    · exact .inr (copy_in hl)
  | writeLoad x y k =>
    exfalso
    obtain ⟨-, s, addr, ⟨pc, hget⟩, hl, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨ld, b, j, hd, hsite, hmb, ⟨base, cls, origin, hsp', -⟩, -⟩ :=
      ht.tensor_issue (Frame.lt_of_get hX hget) hget hσ rfl
    rw [hsp'] at hl
    simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
    obtain ⟨slot, -, hl⟩ := hl
    rw [← hl] at hsp
    exact (hsp rfl).elim
  | readPrefetch x y k =>
    exfalso
    obtain ⟨-, s, addr, ⟨pc, hget⟩, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    exact ht.no_tensor_prefetch (Frame.lt_of_get hX hget) hget hσ rfl
  | writeCta c =>
    exfalso
    obtain ⟨-, s, tg, ⟨pc, hget⟩, -, rfl⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨b, -, -, -, hresp, -⟩ := (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).clc s tg rfl
    simp only [hresp] at hsp
    exact (hsp rfl).elim
  | readCopy =>
    exfalso
    obtain ⟨-, ⟨s, ⟨pc, hget⟩, -⟩ | hp⟩ := h
    · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      exact (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).copy s rfl
    · exact no_bulkPrefetch hX ht hp
  | writeCopy =>
    exfalso
    obtain ⟨-, s, ⟨pc, hget⟩, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    exact (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).copy s rfl
  | writeElem j =>
    exfalso
    obtain ⟨-, s, ⟨pc, hget⟩, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    exact (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).copy s rfl
  | oldElem j =>
    exfalso
    obtain ⟨-, s, r, ⟨pc, hget⟩, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    exact (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).copy s rfl
  | oldStore x y k =>
    exfalso
    obtain ⟨-, s, addr, ⟨pc, hget⟩, hr, -⟩ := h
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨c, s1, hd, hsite, hvalid, b, cls, origin, hspec⟩ :=
      ht.cons_tma (Frame.lt_of_get hX hget) hget hσ
    rw [hspec] at hr
    simp at hr
  | _ => exact h.2.elim

/-- **The bytes outside shared memory are ordered**: two conflicting accesses of such a byte, which
is global, would be two output writes, one store's write of one slot (`OutputUnique`), or an output
write and an input read, of disjoint matrices (`Pre`). -/
theorem global_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hout : OutputUnique X) :
    ConflictsOrdered L X fun l => l.space ≠ .shared := by
  refine ConflictsOrdered.of_none fun e f a b l hc ha hb hs => ?_
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hc
  have hdA := hpre.outputDisjointA
  have hdB := hpre.outputDisjointB
  rcases global_access hpre hX ht he ha hs with ⟨rfl, hre⟩ | ⟨rfl, hde, i, x, y, k, addr, s, rfl,
      hi, hli⟩ <;>
    rcases global_access hpre hX ht hf hb hs with ⟨rfl, hrf⟩ | ⟨rfl, hdf, j, x', y', k', addr', s',
      rfl, hj, hlj⟩
  · rcases hw with h | h <;> cases h
  · rcases hre with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> obtain ⟨-, -, h3, h4⟩ := hdf <;> omega
  · rcases hrf with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> obtain ⟨-, -, h3, h4⟩ := hde <;> omega
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hout i j addr addr' s s' x y k x' y' k' l hi hj hli hlj
    exact hne rfl

/-- **The global writes**: every write of a global byte is a one-byte write of a tensor store's
slot, inside the `D` matrix (`global_access`; a thread writes only shared memory). -/
theorem global_writes (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : GlobalWrites P X := by
  intro w a bs hm hs
  have hpos : 0 < a.size := by
    rcases w with e | ⟨i, p⟩
    · exfalso
      rcases hm with ⟨pc, hget⟩ | ⟨old, pc, hget⟩
      · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        rw [ht.write_shared (Frame.lt_of_get hX hget) hget hσ rfl] at hs
        cases hs
      · exact no_rmw hX ht hget
    · cases p with
      | writeStore x y k =>
        obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hm
        omega
      | writeLoad x y k =>
        obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hm
        omega
      | writeCta c =>
        obtain ⟨-, -, -, -, -, -, -, rfl, -⟩ := hm
        exact Nat.succ_pos _
      | writeCopy =>
        exfalso
        obtain ⟨s, ⟨pc, hget⟩, -⟩ := hm
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        exact (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).copy s rfl
      | writeElem j =>
        exfalso
        obtain ⟨s, ⟨pc, hget⟩, -⟩ := hm
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
        exact (ht.ring_event (Frame.lt_of_get hX hget) hget hσ).copy s rfl
      | _ => exact hm.elim
  have hc : a.Covers a.loc := ⟨rfl, rfl, Nat.le_refl _, by omega⟩
  rcases global_access hpre hX ht (Execution.MemWrites.intent hm) hc
      (fun h => by rw [hs] at h; cases h) with ⟨h, -⟩ | ⟨-, hd, i, x,
      y, k, -, -, rfl, -⟩
  · cases h
  · obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := hm
    obtain ⟨-, h2, h3, h4⟩ := hd
    exact ⟨h1, h2, h3, h4, i, x, y, k, rfl⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory
