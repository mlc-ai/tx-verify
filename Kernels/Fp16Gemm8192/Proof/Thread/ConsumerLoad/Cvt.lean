-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base
public import Kernels.Fp16Gemm8192.Flow.CvtRuns

@[expose] public section

/-! # The conversions after a load's wait

After the wait of load `j` the code converts the load's sixteen values to eight pairs of
halves (`cvts j`). When no conversion faults the conversions write the packed registers with their
pairs (`loadWait_conv`, first part); otherwise one of them faults and the thread is dead (second
part). The facts this needs about each load's conversions are tables (`CvtTable`), checked once
per load. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- What the conversions after load `j`'s wait need from the tables. -/
structure CvtTable (j : Fin 16) : Prop where
  len : (cvts j).length = 8
  code : CvtCode kernel ((Site.loadWait j).pc + 1) (cvts j)
  fresh : CvtFresh (cvts j)
  src : ∀ c ∈ cvts j, ∃ ia ib, 16 * j.val ≤ ia ∧ ia < 16 * j.val + 16 ∧ 16 * j.val ≤ ib ∧
    ib < 16 * j.val + 16 ∧ dataTable.lookup c.2.1 = some ia ∧ dataTable.lookup c.2.2 = some ib ∧
    dataTable.lookup c.1 = none ∧ packTable.lookup c.1 = some (ia, ib)
  live : ∀ c ∈ cvts j, c.2.1 ∈ Flow.live (Site.loadWait j).pc ∧
    c.2.2 ∈ Flow.live (Site.loadWait j).pc
  cover : ∀ k < 16, ∃ c ∈ cvts j, dataTable.lookup c.2.1 = some (16 * j.val + k) ∨
    dataTable.lookup c.2.2 = some (16 * j.val + k)
  after : ∀ r ∈ Flow.live ((Site.loadWait j).pc + 9),
    r ∈ (cvts j).map (·.1) ++ Flow.live (Site.loadWait j).pc

/-- The table facts of one conversion of load `j`. -/
def srcOk (j : Nat) (c : Nat × Nat × Nat) : Bool :=
  match dataTable.lookup c.2.1, dataTable.lookup c.2.2, dataTable.lookup c.1,
      packTable.lookup c.1 with
  | some ia, some ib, none, some p =>
    p == (ia, ib) && decide (16 * j ≤ ia ∧ ia < 16 * j + 16 ∧ 16 * j ≤ ib ∧ ib < 16 * j + 16)
  | _, _, _, _ => false

theorem srcOk_spec {j : Nat} {c : Nat × Nat × Nat} (h : srcOk j c = true) :
    ∃ ia ib, 16 * j ≤ ia ∧ ia < 16 * j + 16 ∧ 16 * j ≤ ib ∧ ib < 16 * j + 16 ∧
      dataTable.lookup c.2.1 = some ia ∧ dataTable.lookup c.2.2 = some ib ∧
      dataTable.lookup c.1 = none ∧ packTable.lookup c.1 = some (ia, ib) := by
  unfold srcOk at h
  split at h
  · rename_i ia ib p ha hb hd hp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, h1, h2, h3, h4⟩ := h
    exact ⟨ia, ib, h1, h2, h3, h4, ha, hb, hd, hp⟩
  · cases h

/-- The table facts of load `j`'s conversions, as one computation. -/
def cvtCheck (j : Fin 16) : Bool :=
  (cvts j).length == 8 && decide (CvtFresh (cvts j)) && (cvts j).all (srcOk j.val) &&
  (cvts j).all (fun c => decide (c.2.1 ∈ Flow.live (Site.loadWait j).pc) &&
    decide (c.2.2 ∈ Flow.live (Site.loadWait j).pc)) &&
  (List.range 16).all (fun k => (cvts j).any fun c =>
    dataTable.lookup c.2.1 == some (16 * j.val + k) ||
      dataTable.lookup c.2.2 == some (16 * j.val + k)) &&
  (Flow.live ((Site.loadWait j).pc + 9)).all
    (fun r => decide (r ∈ (cvts j).map (·.1) ++ Flow.live (Site.loadWait j).pc)) &&
  (Flow.cvtRuns.lookup ((Site.loadWait j).pc + 1)).isSome

theorem lookup_mem {l : List (Nat × List (Nat × Nat × Nat))} {k : Nat}
    {v : List (Nat × Nat × Nat)} (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk
      cases h
      simp only [beq_iff_eq] at hk
      subst hk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem CvtTable.of_check {j : Fin 16} (h : cvtCheck j = true) : CvtTable j := by
  simp only [cvtCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, Bool.or_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hlen, hfresh⟩, hsrc⟩, hlive⟩, hcover⟩, hafter⟩, hsome⟩ := h
  refine ⟨hlen, ?_, hfresh, fun c hc => srcOk_spec (hsrc c hc), hlive, fun k hk => ?_, hafter⟩
  · obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp hsome
    have hm := lookup_mem hcs
    have hc : cvts j = cs := by simp [cvts, hcs]
    rw [hc]
    exact Flow.cvtRuns_code _ hm
  · obtain ⟨c, hc, hk'⟩ := hcover k hk
    exact ⟨c, hc, hk'.imp (by simp) (by simp)⟩



/-- A conversion after load `j`'s wait, when no conversion of the load faults, has an outcome. -/
theorem chunk_ok {acc : Nat → Value} {j : Fin 16} (h : chunkOk acc j = true)
    {c : Nat × Nat × Nat} (hc : c ∈ cvts j) {ia ib : Nat} (ha : dataTable.lookup c.2.1 = some ia)
    (hb : dataTable.lookup c.2.2 = some ib) : ∃ v, Flow.cvtPairE (acc ia) (acc ib) = .ok v := by
  have := List.all_eq_true.mp h c hc
  simp only [cvtOk, ha, hb] at this
  cases hv : Flow.cvtPairE (acc ia) (acc ib) with
  | ok v => exact ⟨v, rfl⟩
  | error f => rw [hv] at this; cases this

set_option maxHeartbeats 4000000 in
/-- The conversions after load `j`'s wait: they reach the instruction after them with the
packed registers written when no conversion faults, and fault otherwise. -/
theorem loadWait_conv {L : Launch} {g : Nat} {d : D} {t : TState} {j : Fin 16} (ht : CvtTable j)
    (hs : d.site = .loadWait j) (h : At t d.site.pc (facts L g d)) :
    (chunkOk d.acc j = true → ∃ t', run kernel Prod L g 8 (PTX.next t) = some t' ∧
      At t' ((Site.loadWait j).pc + 9) (factsAt L g ((Site.loadWait j).pc + 9) d)) ∧
    (chunkOk d.acc j = false →
      Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) (PTX.next t)) := by
  have hpc : (PTX.next t).pc = (Site.loadWait j).pc + 1 := by
    simp [PTX.next, h.1, hs]
  have hreg : ∀ r ∈ Flow.live (Site.loadWait j).pc, (PTX.next t).regs r = some (valueOf L g d r) :=
    fun r hr => by
      have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) (hs ▸ hr))
      simpa [PTX.next] using this
  have hcode : CvtCode kernel (PTX.next t).pc (cvts j) := hpc ▸ ht.code
  have hf : (PTX.next t).fault = none := by simpa [PTX.next] using h.2.2.2.1
  -- each operand register holds its accumulator entry
  have hop : ∀ c ∈ cvts j, ∃ ia ib, dataTable.lookup c.2.1 = some ia ∧
      dataTable.lookup c.2.2 = some ib ∧ (PTX.next t).regs c.2.1 = some (d.acc ia) ∧
      (PTX.next t).regs c.2.2 = some (d.acc ib) ∧
      valueOf L g d c.1 = Flow.cvtPairV (d.acc ia) (d.acc ib) := by
    intro c hc
    obtain ⟨ia, ib, -, -, -, -, ha, hb, hd0, hd⟩ := ht.src c hc
    obtain ⟨la, lb⟩ := ht.live c hc
    exact ⟨ia, ib, ha, hb, by rw [hreg _ la, valueOf_data ha],
      by rw [hreg _ lb, valueOf_data hb], valueOf_pack hd0 hd⟩
  refine ⟨fun hok => ?_, fun hbad => ?_⟩
  · obtain ⟨t', hr, hpc', hs', ha', hf', hd, ho⟩ := Flow.cvt_chain (K := kernel) (L := L) (g := g)
      prod_ideal_cvt prod_decline_cvt (cvts j) (PTX.next t) hcode ht.fresh hf
      (by simpa [PTX.next] using h.2.1) (by simpa [PTX.next] using h.2.2.1)
      (fun c hc => by
        obtain ⟨ia, ib, hia, hib, ha, hb, -⟩ := hop c hc
        exact ⟨_, _, ha, hb, chunk_ok hok hc hia hib⟩)
    rw [ht.len] at hr hpc'
    refine ⟨t', hr, ⟨by rw [hpc', hpc], hs', ha', hf', Flow.holds_of_pointwise fun r hr' => ?_⟩⟩
    by_cases hm : r ∈ (cvts j).map (·.1)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
      obtain ⟨ia, ib, -, -, ha, hb, hv⟩ := hop c hc
      rw [hd c hc _ _ ha hb, hv]
    · rw [ho r hm]
      rcases List.mem_append.mp (ht.after r hr') with h' | h'
      · exact absurd h' hm
      · exact hreg r h'
  · obtain ⟨c, hc, hcb⟩ : ∃ c ∈ cvts j, cvtOk d.acc c = false := by
      by_contra hn
      push Not at hn
      have : chunkOk d.acc j = true := List.all_eq_true.mpr fun c hc => by simpa using hn c hc
      rw [this] at hbad
      cases hbad
    refine Flow.cvt_chain_dead (K := kernel) (L := L) (g := g) prod_ideal_cvt prod_decline_cvt
      (cvts j) (PTX.next t) hcode ht.fresh hf (fun c hc => ?_) ⟨c, hc, ?_⟩
    · obtain ⟨ia, ib, -, -, ha, hb, -⟩ := hop c hc
      exact ⟨⟨_, ha⟩, ⟨_, hb⟩⟩
    · obtain ⟨ia, ib, hia, hib, ha, hb, -⟩ := hop c hc
      simp only [cvtOk, hia, hib] at hcb
      intro va vb ha' hb'
      rw [ha] at ha'; rw [hb] at hb'
      cases ha'; cases hb'
      cases hv : Flow.cvtPairE (d.acc ia) (d.acc ib) with
      | error f => exact ⟨f, rfl⟩
      | ok v => rw [hv] at hcb; cases hcb

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
