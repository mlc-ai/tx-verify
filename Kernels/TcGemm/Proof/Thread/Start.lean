-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Tmpl

@[expose] public section

/-! # `tc_gemm`: the first site of a thread

From the launch state, local steps compute the thread's index, warp and the shared addresses of
the mbarriers and the address slot; warp 0 reaches the allocation, every other warp branches
past it and past the issue to the first barrier. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

/-- The code before the first branch. -/
theorem seg_head (hpre : Pre L A B D a b mem0) (hg : g < L.threads) (d : ThreadD) :
    ∃ t, run kernel [] L g 7 {} = some t ∧ At t 7 (factsOn L A B D g d (trimIssue (Flow.live 7))) :=
      by
  have hb := hpre.block
  have hbase := hpre.sharedRange
  have hg' := lt_block hpre hg
  have h0 : At ({} : TState) 0 [] := ⟨rfl, rfl, rfl, rfl, trivial⟩
  have htid := Launch.oneDim_tidOf hpre.oneDimLaunch.1 g
  have hg32 : g < 2 ^ 32 := by omega
  have hmod : g % L.block = g := by rw [hb]; exact Nat.mod_eq_of_lt hg'
  seg_fp h0 using
    tc_values
    all_goals first
      | seg_close [sregValue, hb, Nat.mod_eq_of_lt hg']
      | (rw [htid]; show Value.bits _ _ = _
         simp only [Dim3.get, hmod]
         norm_bits [truncBits_ofNat hg32 (by decide)])
      | (rw [htid]; show Value.pred _ = _
         simp only [Dim3.get, hmod]
         norm_cmp [truncBits_ofNat hg32 (by decide)])

/-- **The start**: local steps reach the allocation on warp 0 and the first barrier elsewhere. -/
theorem start (hpre : Pre L A B D a b mem0) (hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel [] L g) {} t ∧ (code L A B D g).AtD (code L A B D g).init
      t ∧
      (code L A B D g).inv (code L A B D g).init := by
  have hg' := lt_block hpre hg
  let d0 : ThreadD := { site := if g / 32 = 0 then .alloc else .bar0 false, c := 0, vals := [] }
  obtain ⟨t, hr, ht⟩ := seg_head hpre hg d0
  have h1 : t.regs 1 = some (.pred (decide (g / 32 ≠ 0))) := by
    rw [holds_mem ht.2.2.2.2 (Flow.mem_factsFrom (show 1 ∈ trimIssue (Flow.live 7) by
      table_decide))]
    tc_values
  obtain ⟨u, hu, hat⟩ := run_bra (K := kernel) (A := []) (L := L) (g := g) Flow.code_7 _ ht h1
    (fun _ h => by cases h)
  by_cases hw : g / 32 = 0
  · simp only [hw, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hat
    refine ⟨u, run_rtg (run_comp hr hu), ?_, ?_⟩
    · have hd : d0 = { site := .alloc, c := 0, vals := [] } := by simp [d0, hw]
      show u.pc = d0.site.pc ∧ u.sub = d0.site.sub ∧ u.acc = [] ∧ u.fault = none ∧
        Holds u.regs (facts L A B D g d0)
      rw [hd]
      exact ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1,
        Flow.holds_factsFrom_mono hat.2.2.2.2 (by table_decide)⟩
    · show Inv g d0
      constructor <;> simp [d0, hw, Site.zero]
  · have hp1 : decide (g / 32 ≠ 0) = true := by simp [hw]
    rw [hp1] at hat
    simp only [↓reduceIte] at hat
    have hg0 : g ≠ 0 := by rintro rfl; exact hw rfl
    have h2 : u.regs 2 = some (.pred true) := by
      rw [holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (show 2 ∈ trimIssue (Flow.live 7) by
        table_decide))]
      simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, hg0, ne_eq,
        not_false_eq_true, decide_true]
    obtain ⟨v, hv, hatv⟩ := run_bra (K := kernel) (A := []) (L := L) (g := g) Flow.code_9 _ hat h2
      (fun _ h => by cases h)
    simp only [↓reduceIte] at hatv
    refine ⟨v, run_rtg (run_comp (run_comp hr hu) hv), ?_, ?_⟩
    · have hd : d0 = { site := .bar0 false, c := 0, vals := [] } := by simp [d0, hw]
      show v.pc = d0.site.pc ∧ v.sub = d0.site.sub ∧ v.acc = [] ∧ v.fault = none ∧
        Holds v.regs (facts L A B D g d0)
      rw [hd]
      exact ⟨hatv.1, hatv.2.1, hatv.2.2.1, hatv.2.2.2.1,
        Flow.holds_factsFrom_mono hatv.2.2.2.2 (by table_decide)⟩
    · show Inv g d0
      constructor <;> simp [d0, hw, hg0, Site.zero]

end
end PTX.Kernels.TcGemm.Proof
