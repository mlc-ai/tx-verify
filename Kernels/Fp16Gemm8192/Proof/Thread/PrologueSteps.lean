-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Prologue
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Lemmas.Flow.Local
public import Lemmas.Flow.Scalars

@[expose] public section

/-! # The prologue's paths between events

The local code after the shuffle and the election tests for thread 0 (which initializes
the mbarriers), computes the leader CTA's copy of the first full barrier with `cvta`, an
offset and `mapa`, and tests for warp 0 (which allocates Tensor Memory). The three pointer
steps depend on the cluster layout and are taken one at a time (`run_local`); the tests
split the segment (`run_bra`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000


/-- A concrete state of a prologue or loader state. -/
def Good (L : Launch) (g : Nat) : D ⊕ Role → TState → Prop
  | .inl p, t => (t.pc = p.site.pc ∧ t.sub = sub p ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g p)) ∧ Inv p
  | .inr (.loader l), t => At t l.site.pc (Loader.facts L g l) ∧ Loader.Inv l ∧
      (∀ b, l.site = .arrive b → Loader.leader L g = true)
  | .inr (.mma m), t => At t m.site.pc (Mma.facts L g m) ∧ Mma.Inv m ∧
      ((m.site = .ack ∨ m.site = .accWait) → m.q = 0) ∧
      (m.site = .exitArrive ∨ m.site = .exitWait ∨ m.site = .exit ∨ g / L.block % 2 = 0)
  | .inr (.sched s), t => At t s.site.pc (Scheduler.facts L g s) ∧ Scheduler.Inv s
  | .inr (.cons c), t => (t.pc = c.site.pc ∧ t.sub = c.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (Consumer.facts L g c)) ∧ Consumer.Inv c ∧ Consumer.tidOf L g < 256

theorem good_of_at {L : Launch} {g : Nat} {p : D} {t : TState} (hs : p.site ≠ .allocWrite)
    (h : At t p.site.pc (facts L g p)) (hi : Inv p) : Good L g (.inl p) t := by
  simp only [Good, sub, hs, ↓reduceIte]
  exact ⟨h, hi⟩

theorem tid_lt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    g % L.block < 2 ^ 32 := by
  have := Nat.mod_lt g (show L.block > 0 by rw [hpre.block]; omega)
  rw [hpre.block] at this ⊢
  omega

/-- The opening local code reaches the shuffle. -/
theorem start {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    ∃ t, Relation.ReflTransGen (Tau kernel Prod L g) {} t ∧
      At t Site.shfl.pc (facts L g ⟨.shfl, 0⟩) := by
  have hx := tid_lt (g := g) hpre
  obtain ⟨t, hr, ht⟩ : ∃ t, run kernel Prod L g 5 {} = some t ∧
      At t Site.shfl.pc (facts L g ⟨.shfl, 0⟩) := by
    pro_seg at_init hpre [Launch.oneDim_tidOf hpre.oneDimLaunch.1 g, Dim3.get]
  exact ⟨t, run_rtg hr, ht⟩

/-- The thread-0 test: a one-dimensional block's linear thread index is `tid.x`. -/
theorem tid_or {L : Launch} {x : Nat} (hx : x < 2 ^ 32) :
    truncBits 32
          (truncBits 32
              (truncBits 32
                (truncBits 32
                    (truncBits 32
                      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 0)) *
                          truncBits 32 (truncBits 32 (BitVec.ofNat 64 1)) +
                        truncBits 32 (truncBits 32 (BitVec.ofNat 64 0)))) *
                  truncBits 32 (truncBits 32 (BitVec.ofNat 64 L.block)))) |||
            truncBits 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 64 x := by
  have h0 : truncBits 32 (truncBits 32 (truncBits 32 0#64) * truncBits 32 (truncBits 32 1#64) +
      truncBits 32 (truncBits 32 0#64)) = 0 := by decide
  have hz : truncBits 32 (0 : BitVec 64) = 0 := by decide
  have hm : ∀ y : BitVec 64, (0 : BitVec 64) * y = 0 := fun y => by simp
  have ho : ∀ y : BitVec 64, (0 : BitVec 64) ||| y = y := fun y => by simp
  rw [h0, hz, hm, hz, hz, ho, truncBits_ofNat hx (by decide), truncBits_ofNat hx (by decide)]

theorem reg_val {L : Launch} {g pc : Nat} {d : D} {t : TState} {r : Nat} {v : Value}
    (h : At t pc (factsAt L g pc d)) (hl : r ∈ Flow.live pc) (hv : valueOf L g d r = v) :
    t.regs r = some v := hv ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

theorem reg_val_mem {L : Launch} {g pc : Nat} {d : D} {r : Nat} {v : Value}
    (hl : r ∈ Flow.live pc) (hv : valueOf L g d r = v) : (r, v) ∈ factsAt L g pc d :=
  hv ▸ Flow.mem_factsFrom hl

theorem ne_cons {F : List (Nat × Value)} {r r' : Nat} {v : Value} (hr : r' ≠ r)
    (hF : ∀ p ∈ F, p.1 ≠ r) : ∀ p ∈ (r', v) :: F, p.1 ≠ r := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hr
  · exact hF p hp

/-- From the test for warp 0 onwards: the leader CTA's copy of the first full barrier (a
`cvta`, an offset and a `mapa`), then the allocation (warp 0) or the fence. -/
theorem from_pointer {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hi : Inv d)
    (h : At t ((Site.init 17).pc + 1) (factsAt L g ((Site.init 17).pc + 1) d)) :
    ∃ k t', run kernel Prod L g k t = some t' ∧
      At t' (afterInits d.w).pc (facts L g { d with site := afterInits d.w }) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hcta := cta_lt hpre hg
  have hw := hi.w
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 3 t = some t1 ∧
      At t1 ((Site.init 17).pc + 4) (factsAt L g ((Site.init 17).pc + 4) d) := by
    pro_seg h hpre
  have h10 : t1.regs 903 = some (.bits 64 (BitVec.ofNat 64 L.sharedBase)) :=
    reg_val ht1 (by table_decide) (by pro_values; rfl)
  obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel Prod L g 1 t1 = some t2 ∧
      At t2 ((Site.init 17).pc + 5)
        ((904, .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 L.sharedBase)) ::
          factsAt L g ((Site.init 17).pc + 4) d) :=
    ⟨_, run_local Flow.code_73 rfl ht1
      (exec_cvtaShared (readSharedAddress_bits (cl := false) h10 (.inr rfl) hg hcta (by omega))
        (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t1)),
      At.set ht1 (not_mem_factsFrom (by table_decide))⟩
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 1 t2 = some t3 ∧
      At t3 ((Site.init 17).pc + 6)
        ((902, .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 (L.sharedBase +
          8))) ::
          (904, .ptr 64 true (.shared (g / L.block) (g / L.block))
              (BitVec.ofNat 64 L.sharedBase)) ::
          factsAt L g ((Site.init 17).pc + 4) d) :=
    ⟨_, run_local Flow.code_74 rfl ht2
      (exec_add_sharedPtr (ik := .s) (k := 8) (holds_mem ht2.2.2.2.2 List.mem_cons_self) (.inr rfl)
        (by omega) (by decide)
        (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t2)),
      At.set ht2 (ne_cons (by decide) (not_mem_factsFrom (by table_decide)))⟩
  obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel Prod L g 1 t3 = some t4 ∧
      At t4 ((Site.init 17).pc + 7) (factsAt L g ((Site.init 17).pc + 7) d) := by
    pro_seg ht3 hpre
  have h9 : t4.regs 902 =
      some (.ptr 64 true (.shared (g / L.block) (g / L.block))
          (BitVec.ofNat 64 (L.sharedBase + 8))) :=
    reg_val ht4 (by table_decide) (by pro_values)
  have h42 : t4.regs 88 = some (b32 0) := reg_val ht4 (by table_decide) (by pro_values)
  have hoff : (BitVec.ofNat 64 (L.sharedBase + 8)).toNat = L.sharedBase + 8 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hl := readSharedAddress_ptr (gen := true) (cl :=
    true) h9 (.inr rfl) hg hcta rfl (.inl rfl) (.inl rfl)
    (by rw [hoff]; omega)
  rw [hoff] at hl
  obtain ⟨t5, hr5, ht5⟩ : ∃ t5, run kernel Prod L g 1 t4 = some t5 ∧
      At t5 Flow.bra_77
        ((926, .ptr 64 true (.shared (g / L.block) (2 *
          ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8))) ::
          factsAt L g ((Site.init 17).pc + 7) d) :=
    ⟨_, run_local Flow.code_76 rfl ht4
      (exec_mapa hl (show readBits L g t4 32 (.reg 88) = .ok 0 by
        simp [readBits, readReg, h42, b32, truncBits, bind, Except.bind, pure, Except.pure])
        (map_zero hpre hg _)
        (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t4)),
      At.set ht4 (not_mem_factsFrom (by table_decide))⟩
  have hp5 : t5.regs 5 = some (.pred (decide (d.w ≠ 0))) :=
    holds_mem ht5.2.2.2.2 (List.mem_cons_of_mem _
      (reg_val_mem (r := 5) (by table_decide) (by pro_values)))
  obtain ⟨t6, hr6, ht6⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_77
    (decide (d.w ≠ 0)) ht5 hp5 (prod_localRule_bra L g _ _ _)
  by_cases hw : d.w = 0
  · rw [show decide (d.w ≠ 0) = false by simp [hw]] at ht6
    simp only [Bool.false_eq_true, ↓reduceIte] at ht6
    obtain ⟨t7, hr7, ht7⟩ : ∃ t7, run kernel Prod L g 2 t6 = some t7 ∧
        At t7 Site.alloc.pc (facts L g { d with site := .alloc }) := by
      pro_seg ht6 hpre
    refine ⟨_, t7, run_comp (run_comp (run_comp (run_comp (run_comp hr1 hr2) hr3) hr4) hr5)
      (run_comp hr6 hr7), ?_⟩
    simpa [afterInits, hw] using ht7
  · rw [show decide (d.w ≠ 0) = true by simp [hw]] at ht6
    simp only [↓reduceIte] at ht6
    obtain ⟨t7, hr7, ht7⟩ : ∃ t7, run kernel Prod L g 0 t6 = some t7 ∧
        At t7 Site.fence.pc (facts L g { d with site := .fence }) := by
      pro_seg ht6 hpre
    refine ⟨_, t7, run_comp (run_comp (run_comp (run_comp (run_comp hr1 hr2) hr3) hr4) hr5)
      (run_comp hr6 hr7), ?_⟩
    simpa [afterInits, hw] using ht7

/-- From the test for thread 0 onwards: the barrier initializations (thread 0), or the
pointer and the test for warp 0. -/
theorem from_tid {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hi : Inv d)
    (h : At t (Site.elect.pc + 10) (factsAt L g (Site.elect.pc + 10) d)) :
    ∃ k t', run kernel Prod L g k t = some t' ∧
      At t' (afterElect L g d.w).pc (facts L g { d with site := afterElect L g d.w }) := by
  have hw := hi.w
  have hx := tid_lt (g := g) hpre
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 8 t = some t1 ∧
      At t1 Flow.bra_28 (factsAt L g Flow.bra_28 d) := by
    pro_seg h hpre [tid_or hx, Launch.oneDim_tidOf hpre.oneDimLaunch.1 g,
      hpre.oneDimLaunch.1.1, Dim3.get]
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_28
    (decide (g % L.block ≠ 0)) ht1 (reg_val ht1 (r := 4) (by table_decide) (by pro_values))
    (prod_localRule_bra L g _ _ _)
  by_cases h0 : g % L.block = 0
  · rw [show decide (g % L.block ≠ 0) = false by simp [h0]] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 3 t2 = some t3 ∧
        At t3 (Site.init 0).pc (facts L g { d with site := .init 0 }) := by
      pro_seg ht2 hpre
    refine ⟨_, t3, run_comp (run_comp hr1 hr2) hr3, ?_⟩
    simpa [afterElect, first, h0] using ht3
  · rw [show decide (g % L.block ≠ 0) = true by simp [h0]] at ht2
    simp only [↓reduceIte] at ht2
    have ht2' : At t2 ((Site.init 17).pc + 1) (factsAt L g ((Site.init 17).pc + 1) d) :=
      At.mono ht2 (Flow.holds_factsFrom_mono ht2.2.2.2.2 (by table_decide))
    obtain ⟨k, t3, hr3, ht3⟩ := from_pointer hpre hg hi ht2'
    refine ⟨_, t3, run_comp (run_comp hr1 hr2) hr3, ?_⟩
    simpa [afterElect, first, h0] using ht3

end
end PTX.Kernels.Fp16Gemm8192.Proof.Prologue
