-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5BRInv
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneCta

@[expose] public section

/-!
# The barrier-0 ordinal across the warps of a CTA

From the count along the trace (`count_inv`) and the `bar24` states (`rlow`, `rinv_all`), the
barrier-0 count of a default-partition thread at a state is a function of the state's position
and of the CTA's decisions:

* `bar.sync 0` of the common start: at most 1;
* a prologue `bar.sync 0, 128`: below `2 + C0` (`C0 = 1 + 5 nbQ`, the CTA's prologue count);
* a softmax state of iteration `i'`: `2 + C0 + phi + nB24`;
* the epilogue: `2 + C0 + Lfun num_iters + nB24` (one more after its last `bar.sync 0`).

Delivered:

* `b0At_of`: `B0At c i` (the default threads of a CTA at `bar23` of iteration `i` have made the
  same number of barrier-0 events) from the agreement of the decisions below `i`;
* `b0Pos_of`: `B0PosB c i` (the barrier-0 events of the CTA's default threads at the count of
  `bar23` of iteration `i` are those `bar23`, the next count is a `bar.sync 0, 128`, an exit has
  two more) from the same;
* `alphaAgree_of`: `Bar.AlphaAgree` from the agreement of every iteration's decision.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree B0At)
open Classical

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The positions of the barrier-0 events of the CTA's default threads at the count of `bar23` of
iteration `i`.** -/
def B0PosB (Q : Params) (L : Launch) (X : Execution) (c i : Nat) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, g < L.threads → g / L.block = c →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .bar23 → d.i = i →
    ∀ {g' : Nat}, g' < L.threads → g' / L.block = c → g' % L.block < 128 →
      (∀ {k' pc : Nat} {cn : Option Nat}, X.IsBarrier (g', k') 0 cn pc →
        ((X.tr g').take k').countP (Execution.isBarId 0) =
          ((X.tr g).take k).countP (Execution.isBarId 0) →
        ∃ d' : Sm.D, St Q L X g' k' = some (some (.d (.sm d'))) ∧ d'.site = .bar23 ∧
          d'.i = i) ∧
      (∀ {k' pc : Nat} {cn : Option Nat}, X.IsBarrier (g', k') 0 cn pc →
        ((X.tr g').take k').countP (Execution.isBarId 0) =
          ((X.tr g).take k).countP (Execution.isBarId 0) + 1 → cn = some 128) ∧
      (∀ {j pcx : Nat}, X.get (g', j) = some ⟨pcx, .exit⟩ →
        ((X.tr g).take k).countP (Execution.isBarId 0) + 2 ≤
          ((X.tr g').take j).countP (Execution.isBarId 0))

/-! ### Indices and states -/

theorem norm_idx {g k : Nat} {s : TSt} (hσ : St Q L X g k = some (some s)) :
    ∃ k0, k0 ≤ (X.tr g).length ∧ St Q L X g k0 = some (some s) ∧ cnt0 X g k0 = cnt0 X g k := by
  by_cases hk : k ≤ (X.tr g).length
  · exact ⟨k, hk, hσ, rfl⟩
  · refine ⟨(X.tr g).length, le_rfl, ?_, ?_⟩
    · have h1 : Frame.stateAt (code L Q) X g k =
          Frame.stateAt (code L Q) X g (X.tr g).length :=
        Frame.stateAt_of_le (by omega)
      exact h1.symm.trans hσ
    · unfold cnt0
      rw [List.take_of_length_le le_rfl, List.take_of_length_le (by omega)]

theorem default_of {g k : Nat} {s : DComp.St} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d s))) : g % L.block < 128 :=
  (cls_inv k _ hk hσ).mp trivial

/-- The barrier-0 states of the default partition. -/
theorem b0_state {s : DComp.St} (hb : b0At (DComp.pc s) ≠ 0) :
    (∃ d, s = .dstart d ∧ dN0 s ≤ 1) ∨ (∃ d, s = .pro d ∧ proB0 d.site = 2) ∨
      (∃ d, s = .sm d ∧ smB0 d.site = 2) ∨ (∃ d, s = .epi d ∧ d.site = .bar3) := by
  cases s with
  | dstart d =>
    left
    refine ⟨d, rfl, ?_⟩
    simp only [DComp.pc, dstart_b0] at hb
    obtain ⟨site, tm⟩ := d
    cases site <;> simp_all [dN0]
  | pro d =>
    right; left
    refine ⟨d, rfl, ?_⟩
    simp only [DComp.pc, pro_b0At, proB0] at hb ⊢
    split <;> simp_all
  | sm d =>
    right; right; left
    refine ⟨d, rfl, ?_⟩
    simp only [DComp.pc, sm_b0At, smB0] at hb ⊢
    split <;> simp_all
  | epi d =>
    right; right; right
    refine ⟨d, rfl, ?_⟩
    simp only [DComp.pc, epi_b0] at hb
    cases h : d.site <;> simp_all

/-- **The count field of a barrier-0 event is its state's instruction's.** -/
theorem b0_count (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k pc : Nat} {cn : Option Nat}
    {m : BarMode} {s : TSt} (he : X.get (g, k) = some ⟨pc, .bar 0 cn m⟩)
    (hσ : St Q L X g k = some (some s)) :
    (cn = none ∧ b0At (TSt.pc s) = 1) ∨ (cn = some 128 ∧ b0At (TSt.pc s) = 2) := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) ⟨pc, .bar 0 cn m⟩ o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  rcases bar_kind_op hb (List.mem_of_getElem? hc') hf' rfl with ⟨al, hop⟩ | ⟨-, al, hop⟩
  · rw [hop] at hf'
    have := EvD.fires_barSync_imm (id := 0) (by decide) hf'
    simp only [Event.mk.injEq, Kind.bar.injEq] at this
    left
    refine ⟨this.2.2.1, ?_⟩
    simp [b0At, hc', hop]
  · rw [hop] at hf'
    have := EvD.fires_barSyncN_128 hb hf'
    simp only [Event.mk.injEq, Kind.bar.injEq] at this
    right
    refine ⟨this.2.2.1, ?_⟩
    simp [b0At, hc', hop]

/-! ### The counts at the barrier-0 states -/

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

theorem cnt_eq {g k : Nat} {s : DComp.St} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d s))) :
    (cnt0 X g k : Int) = dN0 s + p128 L g (C0 Q L g) (Lc Q L g) s + nB24 Q L X g k :=
  count_inv hpre hX hf hg (default_of hk hσ) k hk s hσ

theorem nb_pro {g k : Nat} {d : ProA.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) : nB24 Q L X g k = 0 :=
  rlow hpre hX hf hg (default_of hk hσ) 0 (fun _ hj => absurd hj (Nat.not_lt_zero _)) k hk _ hσ

theorem nb_dstart {g k : Nat} {d : DStart.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.dstart d))))  : nB24 Q L X g k = 0 :=
  rlow hpre hX hf hg (default_of hk hσ) 0 (fun _ hj => absurd hj (Nat.not_lt_zero _)) k hk _ hσ

/-- A prologue `bar.sync 0, 128` has fewer than `2 + C0` barrier-0 events before it. -/
theorem cnt_pro {g k : Nat} {d : ProA.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hb : proB0 d.site = 2) :
    (cnt0 X g k : Int) < 2 + C0 Q L g := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  rw [nb_pro hpre hX hf hg hk hσ] at h1
  have hG := (pgSo_all hpre hX hf (g := g) k _ hσ).1
  have hlt := proOff_b0_lt hb hG
  rw [nbOf_pro hpre hX hf hg hσ (pro_b0_afterSk hb)] at hlt
  simp only [dN0, p128, C0] at h1 ⊢
  omega

/-- The common start's `bar.sync 0` have at most one before them. -/
theorem cnt_dstart {g k : Nat} {d : DStart.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.dstart d)))) (hb : dN0 (.dstart d) ≤ 1) :
    (cnt0 X g k : Int) ≤ 1 := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  rw [nb_dstart hpre hX hf hg hk hσ] at h1
  simp only [p128] at h1
  omega

omit hpre hX hf in
theorem lfun_ge {n i : Nat} (h : i < n) : 4 * (i : Int) + 2 ≤ Lfun n := by
  unfold Lfun
  split_ifs <;> omega

/-! ### `B0At` -/

/-- The count at `bar23` of iteration `i`. -/
theorem cnt_bar23 {i : Nat} {g k : Nat} {d : Sm.D} (hg : g < L.threads)
    (hD : ∀ j < i, DecAgree Q L X (g / L.block) j) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .bar23) (hi : d.i = i) :
    (cnt0 X g k : Int) = 2 + C0 Q L g + (4 * (i : Int) - 1) +
      nResc (Dc Q L X (g / L.block)) i ∧ 1 ≤ i := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  have hR := rlow hpre hX hf hg (default_of hk hσ) i hD k hk _ hσ
  have hb : Bnd i (.sm d) := by simp [Bnd, hs, hi, late]
  obtain ⟨hv, -⟩ := hR
  obtain ⟨⟨hJ1, -⟩, hv⟩ := hv hb
  rw [hv] at h1
  have hi1 : 1 ≤ d.i := hJ1 (Or.inl (by rw [hs]; rfl))
  refine ⟨?_, by omega⟩
  rw [h1]
  simp only [dN0, p128, hs, phi, RD, postR, hi]
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.cast_ofNat]
  ring_nf

/-- **`B0At c i` from the agreement of the decisions below `i`.** -/
theorem b0At_of {c i : Nat} (hD : ∀ j < i, DecAgree Q L X c j) : B0At Q L X c i := by
  intro g g' k k' d d' hg hg' hc hc' hσ hσ' hs hs' hi hi'
  obtain ⟨k0, hk0, hσ0, hc0⟩ := norm_idx hσ
  obtain ⟨k1, hk1, hσ1, hc1⟩ := norm_idx hσ'
  have h1 := (cnt_bar23 hpre hX hf hg (hc ▸ hD) hk0 hσ0 hs hi).1
  have h2 := (cnt_bar23 hpre hX hf hg' (hc' ▸ hD) hk1 hσ1 hs' hi').1
  have hq : C0 Q L g = C0 Q L g' := by
    simp only [C0, nbQ_cta (Q := Q) (hc.trans hc'.symm)]
  rw [hc] at h1
  rw [hc'] at h2
  have : (cnt0 X g k0 : Int) = cnt0 X g' k1 := by rw [h1, h2, hq]
  have : cnt0 X g k0 = cnt0 X g' k1 := by exact_mod_cast this
  show cnt0 X g k = cnt0 X g' k'
  omega

/-! ### The counts of the other barrier-0 states -/

/-- The count at a softmax state, below the bound `I`: exact before the decision of `I`, at least
`nResc I` past it. -/
theorem cnt_sm {I : Nat} {g k : Nat} {d : Sm.D} (hg : g < L.threads)
    (hD : ∀ j < I, DecAgree Q L X (g / L.block) j) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    (Bnd I (.sm d) ∧ JS (Dc Q L X (g / L.block)) d ∧
      (cnt0 X g k : Int) = 2 + C0 Q L g + phi d.site d.i + RD (Dc Q L X (g / L.block)) d) ∨
    (¬ Bnd I (.sm d) ∧
      2 + C0 Q L g + phi d.site d.i + nResc (Dc Q L X (g / L.block)) I ≤ (cnt0 X g k : Int)) := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  have hR := rlow hpre hX hf hg (default_of hk hσ) I hD k hk _ hσ
  obtain ⟨hB, hU⟩ := hR
  simp only [dN0, p128] at h1
  by_cases hb : Bnd I (.sm d)
  · obtain ⟨hJ, hv⟩ := hB hb
    left
    refine ⟨hb, hJ, ?_⟩
    rw [h1, hv]
    push_cast
    ring_nf
  · right
    refine ⟨hb, ?_⟩
    have := hU hb
    rw [h1]
    push_cast
    have : ((nResc (Dc Q L X (g / L.block)) I : Nat) : Int) ≤ (nB24 Q L X g k : Int) := by
      exact_mod_cast this
    linarith

/-- The count at an epilogue state, below the bound `I`. -/
theorem cnt_epi {I : Nat} {g k : Nat} {d : Epi.D} (hg : g < L.threads)
    (hD : ∀ j < I, DecAgree Q L X (g / L.block) j) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.epi d)))) :
    (dN0 (.epi d) : Int) + C0 Q L g + Lfun (nIt Q L g) +
      nResc (Dc Q L X (g / L.block)) (min (nIt Q L g) I) ≤ (cnt0 X g k : Int) := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  have hR : nResc (Dc Q L X (g / L.block)) (min (nIt Q L g) I) ≤ nB24 Q L X g k :=
    rlow hpre hX hf hg (default_of hk hσ) I hD k hk _ hσ
  simp only [p128, Lc] at h1
  have : ((nResc (Dc Q L X (g / L.block)) (min (nIt Q L g) I) : Nat) : Int) ≤
      (nB24 Q L X g k : Int) := by exact_mod_cast hR
  linarith

/-- The iteration of a state at `bar23` is below `num_iters`. -/
theorem bar23_lt {g k : Nat} {d : Sm.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .bar23) :
    d.i < nIt Q L g := by
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k1, d1, e, rfl, he, hσ1, hn⟩
  · simp [SmEntry.d0] at hs
  · obtain ⟨h1, h2⟩ := prev_bar23 hn hs
    have he' : X.get (g, k1) = some e := he
    have hI := Sv.sm_inv_at hX hf he' hσ1
    have hl : d1.i < d1.e.r26 := (hI.late (by rw [h1]; trivial)).2.2
    rw [r26_numIters hpre hX hf hg he' hσ1] at hl
    simp only [nIt]
    omega


omit hpre hX hf in
/-- A state of a default thread is a default-partition state. -/
theorem dstate_of {g k : Nat} {σ : TSt} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some σ)) (hd : g % L.block < 128) : ∃ s, σ = .d s := by
  cases σ with
  | d s => exact ⟨s, rfl⟩
  | w s => exact absurd ((cls_inv k _ hk hσ).mpr hd) (by simp [TSt.isD])

omit hpre hX hf in
theorem lfun_nonneg (n : Nat) : 0 ≤ Lfun n := by
  unfold Lfun
  split_ifs <;> omega

omit hpre hX hf in
theorem c0_pos (g : Nat) : 1 ≤ C0 Q L g := by
  unfold C0
  have := Int.natCast_nonneg (nbQ Q L g)
  omega

/-- The state and the instruction of a barrier-0 event of a default thread. -/
theorem bar_state {g k pc : Nat} {cn : Option Nat} (hd : g % L.block < 128)
    (hb : X.IsBarrier (g, k) 0 cn pc) :
    ∃ s, St Q L X g k = some (some (.d s)) ∧ k ≤ (X.tr g).length ∧
      b0At (DComp.pc s) ≠ 0 ∧ ((cn = none ∧ b0At (DComp.pc s) = 1) ∨
        (cn = some 128 ∧ b0At (DComp.pc s) = 2)) := by
  have hb' : X.get (g, k) = some ⟨pc, .bar 0 cn .sync⟩ := hb
  obtain ⟨σ, hσ'⟩ := Frame.event_state hf.sound hX hf.tracked hb' (fun pc f h => by cases h)
  have hσ : St Q L X g k = some (some σ) := hσ'
  have hk := (List.getElem?_eq_some_iff.mp hb').1.le
  obtain ⟨s, rfl⟩ := dstate_of hk hσ hd
  have hz := (b0_event hpre hX hf.sound hb' hσ).mp (by simp [Execution.isBarId])
  exact ⟨s, hσ, hk, hz, b0_count hpre hX hf.sound hb' hσ⟩

/-- **`B0PosB c i` from the agreement of the decisions below `i`.** -/
theorem b0Pos_of {c i : Nat} (hD : ∀ j < i, DecAgree Q L X c j) : B0PosB Q L X c i := by
  intro g k d hg hc hσ hs hi g' hg' hc' hd'
  obtain ⟨k0, hk0, hσ0, hc0⟩ := norm_idx hσ
  have hDg : ∀ j < i, DecAgree Q L X (g / L.block) j := hc ▸ hD
  have hDg' : ∀ j < i, DecAgree Q L X (g' / L.block) j := hc' ▸ hD
  obtain ⟨hφ, hi1⟩ := cnt_bar23 hpre hX hf hg hDg hk0 hσ0 hs hi
  have hin : i < nIt Q L g := hi ▸ bar23_lt hpre hX hf hg hk0 hσ0 hs
  have hcc : g / L.block = g' / L.block := hc.trans hc'.symm
  have hC : C0 Q L g' = C0 Q L g := by simp only [C0, nbQ_cta (Q := Q) hcc]
  have hN : nIt Q L g' = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block hcc .z, ProA.cta_eq_of_block hcc .x]
  have hDc : Dc Q L X (g' / L.block) = Dc Q L X (g / L.block) := by rw [hcc]
  have hC1 := c0_pos (Q := Q) (L := L) g
  set R := nResc (Dc Q L X (g / L.block)) i with hR
  have hcntg : (cnt0 X g k : Int) = 2 + C0 Q L g + (4 * (i : Int) - 1) + R := by
    rw [← hc0]; exact hφ
  -- the epilogue
  have epi_low : ∀ {k' : Nat} {de : Epi.D}, k' ≤ (X.tr g').length →
      St Q L X g' k' = some (some (.d (.epi de))) →
      (dN0 (.epi de) : Int) + C0 Q L g + 4 * (i : Int) + 2 + R ≤ cnt0 X g' k' := by
    intro k' de hk' hσ'
    have h := cnt_epi hpre hX hf hg' hDg' hk' hσ'
    rw [hC, hN, hDc, Nat.min_eq_right hin.le] at h
    have := lfun_ge hin
    linarith
  -- the softmax region
  have sm_cls : ∀ {k' : Nat} {d' : Sm.D}, k' ≤ (X.tr g').length →
      St Q L X g' k' = some (some (.d (.sm d'))) → smB0 d'.site = 2 →
      (d'.site = .bar23 ∧ d'.i = i) ∨
        (cnt0 X g' k' : Int) < 2 + C0 Q L g + (4 * (i : Int) - 1) + R ∨
        2 + C0 Q L g + (4 * (i : Int) - 1) + R + 1 ≤ (cnt0 X g' k' : Int) := by
    intro k' d' hk' hσ' h2
    rcases cnt_sm hpre hX hf hg' hDg' hk' hσ' with ⟨hb, hJ, hv⟩ | ⟨hb, hv⟩
    · rw [hC, hDc] at hv
      simp only [Bnd] at hb
      have hrd := rd_le (Dc Q L X (g / L.block)) d'
      rcases phi_b0 h2 d'.i with ⟨hsite, hp⟩ | ⟨hsite, hp⟩ | ⟨hl, hp1, hp2, -⟩
      · rw [hp] at hv
        simp only [RD, postR, hsite, Bool.false_eq_true, false_and, ↓reduceIte,
          add_zero] at hv
        right; left
        rcases hb with hlt | ⟨heq, -⟩
        · have := nResc_mono (Dc Q L X (g / L.block)) hlt.le
          have : ((nResc (Dc Q L X (g / L.block)) d'.i : Nat) : Int) ≤ (R : Int) := by
            exact_mod_cast this
          omega
        · rw [heq] at hv; omega
      · rw [hp] at hv
        simp only [RD, postR, hsite, Bool.false_eq_true, false_and, ↓reduceIte,
          add_zero] at hv
        rcases hb with hlt | ⟨heq, -⟩
        · right; left
          have := nResc_mono (Dc Q L X (g / L.block)) hlt.le
          have : ((nResc (Dc Q L X (g / L.block)) d'.i : Nat) : Int) ≤ (R : Int) := by
            exact_mod_cast this
          omega
        · left; exact ⟨hsite, heq⟩
      · right; left
        rcases hb with hlt | ⟨-, hlf⟩
        · have := nResc_mono (Dc Q L X (g / L.block)) (show d'.i + 1 ≤ i by omega)
          have : ((RD (Dc Q L X (g / L.block)) d' : Nat) : Int) ≤ (R : Int) := by
            exact_mod_cast le_trans hrd this
          omega
        · rw [hl] at hlf; exact absurd hlf (by decide)
    · rw [hC, hDc] at hv
      simp only [Bnd, not_or, not_and] at hb
      right; right
      rcases phi_b0 h2 d'.i with ⟨hsite, hp⟩ | ⟨hsite, hp⟩ | ⟨hl, hp1, hp2, -⟩
      · rw [hp] at hv
        have : d'.i ≠ i := fun h => hb.2 h (by rw [hsite]; rfl)
        omega
      · rw [hp] at hv
        have : d'.i ≠ i := fun h => hb.2 h (by rw [hsite]; rfl)
        omega
      · omega
  refine ⟨fun {k' pc cn} hb hcnt => ?_, fun {k' pc cn} hb hcnt => ?_, fun {j pcx} hj => ?_⟩
  · have hcnt' : (cnt0 X g' k' : Int) = cnt0 X g k := by exact_mod_cast hcnt
    obtain ⟨s', hσ', hk', hz, -⟩ := bar_state hpre hX hf hd' hb
    rcases b0_state hz with ⟨d0, rfl, hn0⟩ | ⟨d0, rfl, hp⟩ | ⟨d0, rfl, hsm⟩ | ⟨d0, rfl, h3⟩
    · have := cnt_dstart hpre hX hf hg' hk' hσ' hn0
      omega
    · have := cnt_pro hpre hX hf hg' hk' hσ' hp
      rw [hC] at this
      omega
    · rcases sm_cls hk' hσ' hsm with ⟨h1, h2⟩ | h | h
      · exact ⟨d0, hσ', h1, h2⟩
      · omega
      · omega
    · have := epi_low hk' hσ'
      simp only [dN0, h3] at this
      omega
  · have hcnt' : (cnt0 X g' k' : Int) = cnt0 X g k + 1 := by exact_mod_cast hcnt
    obtain ⟨s', hσ', hk', hz, hcn⟩ := bar_state hpre hX hf hd' hb
    rcases hcn with ⟨-, h1⟩ | ⟨h, -⟩
    · exfalso
      rcases b0_state hz with ⟨d0, rfl, hn0⟩ | ⟨d0, rfl, hp⟩ | ⟨d0, rfl, hsm⟩ | ⟨d0, rfl, h3⟩
      · have := cnt_dstart hpre hX hf hg' hk' hσ' hn0
        omega
      · simp only [DComp.pc, pro_b0At, hp] at h1
        omega
      · simp only [DComp.pc, sm_b0At, hsm] at h1
        omega
      · have := epi_low hk' hσ'
        simp only [dN0, h3] at this
        omega
    · exact h
  · have hk' := (List.getElem?_eq_some_iff.mp hj).1.le
    rcases exit_event_state hX hf.sound hf.tracked hj with ⟨de, hσ', hx⟩ | ⟨x, hσ', -⟩
    · have := epi_low hk' hσ'
      simp only [dN0, hx] at this
      have : (cnt0 X g k : Int) + 2 ≤ cnt0 X g' j := by omega
      show cnt0 X g k + 2 ≤ cnt0 X g' j
      omega
    · obtain ⟨s, hs⟩ := dstate_of hk' hσ' hd'
      cases hs

/-! ### `AlphaAgree` -/

/-- The count at a softmax `bar.sync 0, 128` when every decision agrees: at least `2 + C0`, at most
`2 + C0 + 4 i' + 1 + nResc n`, with `i' < n`. -/
theorem cnt_sm_all {g k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads)
    (hD : ∀ j, DecAgree Q L X (g / L.block) j) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hb : smB0 d.site = 2) :
    d.i < nIt Q L g ∧ 2 + C0 Q L g ≤ (cnt0 X g k : Int) ∧
      (cnt0 X g k : Int) ≤ 2 + C0 Q L g + 4 * (d.i : Int) + 1 +
        nResc (Dc Q L X (g / L.block)) (nIt Q L g) := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hI := Sv.sm_inv_at hX hf he hσ
  have hlt : d.i < nIt Q L g := by
    have := (hI.late (lateSite_b0 hb)).2.2
    rw [r26_numIters hpre hX hf hg he hσ] at this
    simp only [nIt]
    omega
  have h1 := cnt_eq hpre hX hf hg hk hσ
  obtain ⟨hJ, hv⟩ := rinv_all hpre hX hf hg (default_of hk hσ) hD k hk _ hσ
  simp only [JSx] at hJ
  simp only [Rval] at hv
  rw [hv] at h1
  simp only [dN0, p128] at h1
  have hrd := rd_le (Dc Q L X (g / L.block)) d
  have hmono := nResc_mono (Dc Q L X (g / L.block)) (show d.i + 1 ≤ nIt Q L g by omega)
  have hrd' : ((RD (Dc Q L X (g / L.block)) d : Nat) : Int) ≤
      ((nResc (Dc Q L X (g / L.block)) (nIt Q L g) : Nat) : Int) := by
    exact_mod_cast le_trans hrd hmono
  have hnn : (0 : Int) ≤ ((RD (Dc Q L X (g / L.block)) d : Nat) : Int) := Int.natCast_nonneg _
  refine ⟨hlt, ?_, ?_⟩
  · rcases phi_b0 hb d.i with ⟨hsite, hp⟩ | ⟨hsite, hp⟩ | ⟨-, hp1, -, -⟩
    · have : 1 ≤ d.i := hJ.1 (Or.inl (by rw [hsite]; rfl))
      rw [hp] at h1
      omega
    · have : 1 ≤ d.i := hJ.1 (Or.inl (by rw [hsite]; rfl))
      rw [hp] at h1
      omega
    · omega
  · rcases phi_b0 hb d.i with ⟨-, hp⟩ | ⟨-, hp⟩ | ⟨-, -, hp2, -⟩
    · rw [hp] at h1; omega
    · rw [hp] at h1; omega
    · omega

/-- The count at the epilogue's `bar3` when every decision agrees. -/
theorem cnt_bar3_all {g k : Nat} {d : Epi.D} (hg : g < L.threads)
    (hD : ∀ j, DecAgree Q L X (g / L.block) j) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.epi d)))) (h3 : d.site = .bar3) :
    (cnt0 X g k : Int) = 2 + C0 Q L g + Lfun (nIt Q L g) +
      nResc (Dc Q L X (g / L.block)) (nIt Q L g) := by
  have h1 := cnt_eq hpre hX hf hg hk hσ
  obtain ⟨-, hv⟩ := rinv_all hpre hX hf hg (default_of hk hσ) hD k hk _ hσ
  simp only [Rval] at hv
  rw [hv] at h1
  simp only [dN0, p128, Lc, h3] at h1
  rw [h1]
  push_cast
  ring_nf

/-- **A barrier-0 event without a count and one with the count 128 of two default threads of a
CTA have different counts**, when every decision agrees. -/
theorem mix_false (hD : ∀ c j, DecAgree Q L X c j) {g g' k k' : Nat} {s s' : DComp.St}
    {e e' : Event} (hg : g < L.threads) (hg' : g' < L.threads)
    (hcc : g / L.block = g' / L.block) (he : X.get (g, k) = some e)
    (he' : X.get (g', k') = some e') (hσ : St Q L X g k = some (some (.d s)))
    (hσ' : St Q L X g' k' = some (some (.d s'))) (h1 : b0At (DComp.pc s) = 1)
    (h2 : b0At (DComp.pc s') = 2) (hcnt : cnt0 X g k = cnt0 X g' k') : False := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hk' : k' ≤ (X.tr g').length := (List.getElem?_eq_some_iff.mp he').1.le
  have hcnt' : (cnt0 X g k : Int) = cnt0 X g' k' := by exact_mod_cast hcnt
  have hC : C0 Q L g' = C0 Q L g := by simp only [C0, nbQ_cta (Q := Q) hcc]
  have hN : nIt Q L g' = nIt Q L g := by
    simp only [nIt, ProA.cta_eq_of_block hcc .z, ProA.cta_eq_of_block hcc .x]
  have hDc : Dc Q L X (g' / L.block) = Dc Q L X (g / L.block) := by rw [hcc]
  have hC1 := c0_pos (Q := Q) (L := L) g
  have hz : b0At (DComp.pc s) ≠ 0 := by omega
  have hz' : b0At (DComp.pc s') ≠ 0 := by omega
  -- the second thread
  have low' : 2 ≤ (cnt0 X g' k' : Int) := by
    rcases b0_state hz' with ⟨d0, rfl, -⟩ | ⟨d0, rfl, hp⟩ | ⟨d0, rfl, hsm⟩ | ⟨d0, rfl, h3⟩
    · simp only [DComp.pc, dstart_b0] at h2; split at h2 <;> omega
    · have h := cnt_eq hpre hX hf hg' hk' hσ'
      rw [nb_pro hpre hX hf hg' hk' hσ'] at h
      simp only [dN0, p128] at h
      omega
    · have := (cnt_sm_all hpre hX hf hg' (hD _) he' hσ' hsm).2.1
      omega
    · simp only [DComp.pc, epi_b0, h3] at h2; omega
  rcases b0_state hz with ⟨d0, rfl, hn0⟩ | ⟨d0, rfl, hp⟩ | ⟨d0, rfl, hsm⟩ | ⟨d0, rfl, h3⟩
  · have := cnt_dstart hpre hX hf hg hk hσ hn0
    omega
  · simp only [DComp.pc, pro_b0At, hp] at h1; omega
  · simp only [DComp.pc, sm_b0At, hsm] at h1; omega
  · have hv := cnt_bar3_all hpre hX hf hg (hD _) hk hσ h3
    have hl0 := lfun_nonneg (nIt Q L g)
    have hn0 : (0 : Int) ≤ ((nResc (Dc Q L X (g / L.block)) (nIt Q L g) : Nat) : Int) :=
      Int.natCast_nonneg _
    rcases b0_state hz' with ⟨d1, rfl, -⟩ | ⟨d1, rfl, hp'⟩ | ⟨d1, rfl, hsm'⟩ | ⟨d1, rfl, h3'⟩
    · simp only [DComp.pc, dstart_b0] at h2; split at h2 <;> omega
    · have := cnt_pro hpre hX hf hg' hk' hσ' hp'
      rw [hC] at this
      omega
    · obtain ⟨hlt, -, hup⟩ := cnt_sm_all hpre hX hf hg' (hD _) he' hσ' hsm'
      rw [hC, hN, hDc] at hup
      rw [hN] at hlt
      have := lfun_ge hlt
      omega
    · simp only [DComp.pc, epi_b0, h3'] at h2; omega

/-- **`Bar.AlphaAgree` from the agreement of every iteration's decision.** -/
theorem alphaAgree_of (hD : ∀ c j, DecAgree Q L X c j) : Bar.AlphaAgree L X := by
  intro g g' k k' pc pc' c c' m m' hg hg' hcc hd hd' he he' hcnt
  obtain ⟨σ, hσ'⟩ := Frame.event_state hf.sound hX hf.tracked he (fun pc f h => by cases h)
  obtain ⟨σ', hσ''⟩ := Frame.event_state hf.sound hX hf.tracked he' (fun pc f h => by cases h)
  have hσ : St Q L X g k = some (some σ) := hσ'
  have hσ2 : St Q L X g' k' = some (some σ') := hσ''
  obtain ⟨s, rfl⟩ := dstate_of (List.getElem?_eq_some_iff.mp he).1.le hσ hd
  obtain ⟨s', rfl⟩ := dstate_of (List.getElem?_eq_some_iff.mp he').1.le hσ2 hd'
  have hcnt' : cnt0 X g k = cnt0 X g' k' := hcnt
  rcases b0_count hpre hX hf.sound he hσ with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
    rcases b0_count hpre hX hf.sound he' hσ2 with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · rfl
  · exact (mix_false hpre hX hf hD hg hg' hcc he he' hσ hσ2 h1 h2 hcnt').elim
  · exact (mix_false hpre hX hf hD hg' hg hcc.symm he' he hσ2 hσ h2 h1 hcnt'.symm).elim
  · rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
