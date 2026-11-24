-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFirstScanTrace
public import Kernels.TmlFa4Fwd.Flow.Code.Part031

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private theorem int32Signed {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem cutoffWord (l : Launch) (g : Nat) {count heads cta : Nat}
    (hc : count < 2 ^ 31) (hh : heads < 2 ^ 31) (hg : cta < 2 ^ 31)
    (htotal : count * heads < 2 ^ 31) :
    Seg kernel [] l g 3 1981 [(7198, b32 count), (7139, b32 heads), (1072, b32 cta)] 1984
      [(7200, b32 (count * heads)), (346, .pred (decide (cta < count * heads))),
       (7199, b32 0)] := by
  intro t ht
  have hCount : count < 2 ^ 32 := by omega
  have hHeads : heads < 2 ^ 32 := by omega
  have hCta : cta < 2 ^ 32 := by omega
  have hTotal : count * heads < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_mul, truncBits_ofNat hCount (by decide),
        truncBits_ofNat hHeads (by decide), truncBits_ofNat hCta (by decide),
        truncBits_ofNat hTotal (by decide), compare, Option.getD_some, int32Signed hg,
        int32Signed htotal, Int.ofNat_lt]


/-- The first group branch keeps the physical CTA and the scheduler's launch frame. -/
theorem firstGroupRouteKeeping {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {cta : Nat} (hCta : cta < 2 ^ 31) {t : TState} :
    let count := tilePrefix p (min p.batch 31)
    let limit := count * p.heads
    At t 1981 [(7198, b32 count), (7139, b32 p.heads), (1072, b32 cta)] →
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if cta < limit then 2042 else 1985) [(7200, b32 limit), (7199, b32 0)] ∧
      ∀ r ∈ [1072, 7203, 2535, 7196, 7197, 7198, 7139, 7502, 7503, 1180, 7506],
        u.regs r = t.regs r := by
  dsimp only
  intro ht
  let count := tilePrefix p (min p.batch 31)
  let limit := count * p.heads
  have hWork : limit < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left p.batch 31)
  have hPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hCount : count < 2 ^ 31 := (Nat.le_mul_of_pos_right count hPos).trans_lt hWork
  obtain ⟨u, hu, hU⟩ := cutoffWord l g hCount hp.heads_signed hCta hWork t ht
  have hCalc := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hu
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1984 _ hU hU.2.2.2.2.2.1 (by simp)
  have hBr := localRun (by decide) (by decide) hU.1 rfl hv
  refine ⟨v, run_comp hCalc hBr, ?_, ?_⟩
  · refine ⟨?_, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.2.1, trivial⟩
    simpa only [decide_eq_true_eq] using hV.1
  · intro r hr
    exact schedulerLocalFrame (lo := 1981) (len := 4) (by decide +kernel) (by decide +kernel)
      (run_comp hu hv) ht.1.ge (by rw [ht.1]) hr

/-- The first group branch retains the CTA, launch batch and shared base. -/
theorem firstGroupRouteWithFrame {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {cta : Nat} (hCta : cta < 2 ^ 31) {t : TState} :
    let count := tilePrefix p (min p.batch 31)
    let limit := count * p.heads
    At t 1981 [(7198, b32 count), (7139, b32 p.heads), (1072, b32 cta)] →
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if cta < limit then 2042 else 1985) [(7200, b32 limit), (7199, b32 0)] ∧
      ∀ r ∈ [1072, 7203, 2535], u.regs r = t.regs r := by
  dsimp only
  intro ht
  obtain ⟨u, hr, hu, hKeep⟩ := firstGroupRouteKeeping hp g hCta ht
  refine ⟨u, hr, hu, fun r hr => hKeep r ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  tauto

/-- A CTA below the first group's cutoff takes the selected-group edge. The other edge starts
the next group search, with the computed cutoff retained in both cases. -/
theorem firstGroupRoute {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {cta : Nat} (hCta : cta < 2 ^ 31) {t : TState} :
    let count := tilePrefix p (min p.batch 31)
    let limit := count * p.heads
    At t 1981 [(7198, b32 count), (7139, b32 p.heads), (1072, b32 cta)] →
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if cta < limit then 2042 else 1985) [(7200, b32 limit), (7199, b32 0)] := by
  dsimp only
  intro ht
  obtain ⟨u, hr, hu, _⟩ := firstGroupRouteWithFrame hp g hCta ht
  exact ⟨u, hr, hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
