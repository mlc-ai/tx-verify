-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpEst
public import Lemmas.Flow.OutPath

@[expose] public section

/-! # The local paths of the exponent window

The runs of the exponent window as paths (`PathD`, `Lemmas/Flow/OutPath.lean`): the states the
local steps reach from the state after the shuffle of pc 1838, beyond the start of the software
`exp2` instance `n`, come from the end of the instances before it, and have the registers the
window leaves (`exp_path`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

noncomputable section
variable {L : Launch} {g : Nat}

/-- A generated run has its path form (`Gen.<name>_path`). -/
def RunData.Path (r : RunData) : Prop := ∀ (L : Launch) (g : Nat) (V : Nat → Value),
  PathD kernel Assumptions.all L g r.n r.s (r.fs0 V) (r.s + r.n) (r.fs1 V) (r.C V)

theorem runE1_path : runE1.Path := fun L g V => Gen.ex1_path L g V

/-- **A generated run on a register file**, as a path. -/
theorem RunData.advP (r : RunData) (ok : r.Ok) (hp : r.Path) {K : List Nat} (V : Nat → Value)
    (hl : r.live.all (fun x => K.contains x) = true) :
    PathD kernel Assumptions.all L g r.n r.s (factsFrom K V) (r.s + r.n)
      (factsFrom (r.K' K) (r.V' V)) (r.C V) := by
  have h := hp L g V
  rw [ok.h0 V] at h
  have h2 := PathD.frame (H := factsFrom (keep r.ins K) V) Lib.rulesFrame h rfl ok.len
    (by rw [factsFrom_keys]; exact frameB_keep K ok.loc) ok.free
  refine PathD.weaken h2 (fun R hR => ?_) (fun R hR => ?_)
  · refine (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hR fun r' hr => by
      simpa using List.all_eq_true.mp hl r' hr, ?_⟩
    exact holds_factsFrom_mono hR fun r' hr => (List.mem_filter.mp hr).1
  · have := holds_ex (Kf := keep r.ins K) (V := V) (fs := r.fs1 V) hR
    rwa [ok.h1 V] at this

/-- **The sixteen instances** as a path. -/
theorem sw_chainP {K : List Nat} {V : Nat → Value} {n : Nat} (hn : n ≤ 16)
    (hx : ∀ i < n, swX (swPc i) ∈ K) (ht : ∀ i < n, SK.ni.Has (V (swX (swPc i)))) :
    PathD kernel Assumptions.all L g n (swPc 0) (factsFrom K V) (swPc n)
      (factsFrom (swKs K n) (swVs V n)) True := by
  induction n with
  | zero =>
    intro t ht' t' hr _
    exact ⟨trivial, t, rfl, ht', hr⟩
  | succ n ih =>
    have ih := ih (by omega) (fun i hi => hx i (by omega)) (fun i hi => ht i (by omega))
    have hs := sw_seg (L := L) (g := g) (swPc_site (i := n) (by omega)) (K := swKs K n)
      (V := swVs V n)
      (swKs_mem (fun j hj => swDis_xw (by omega) hj) (hx n (by omega)))
      (by rw [swVs_other fun j hj => swDis_xy (by omega) hj]; exact ht n (by omega))
    have e : swPc n + 11 = swPc (n + 1) := by simp only [swPc]; omega
    rw [e] at hs
    exact (ih.comp (PathD.of_seg1 hs (by simp only [swPc]; omega))
      (by simp only [swPc]; omega)).mono_cond fun _ => trivial

/-- The rescale run from the shuffle's successor, as a path. -/
theorem alpha_path_k (m sent recv : Value) (vH : Nat → Value) :
    PathD kernel Assumptions.all L g 8 1839
      (factsFrom ([1520, 1521, 1914, 498] ++ kHx) (alphaW L m sent recv vH)) 1847
      (factsFrom ([498, 1914, 1522, 168, 507, 1523] ++ kHx)
        (xFinal (alphaW L m sent recv vH) Lib.alphaItems))
      (xCond (alphaW L m sent recv vH) Lib.alphaItems) :=
  PathD.of_items Lib.alpha_at (by decide +kernel) (by decide +kernel) (req_alpha _)
    (by decide +kernel)

/-- **The local paths of the exponent window** from the state after the shuffle of pc 1838: a
state at the start of instance `n` or beyond comes from the end of the instances before it. -/
theorem exp_path (m sent recv : Value) (vH : Nat → Value) {V : Nat → Value} (hE : ExpIn V)
    (hV : ∀ r ∈ kE0, V r = if r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 then
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r else vH r) {n : Nat} (hn : n ≤ 16) :
    ∃ N, PathD kernel Assumptions.all L g N 1839
      ([(1520, sent), (1521, recv), (1914, m), (498, scaleW L)] ++ factsFrom kHx vH) (swPc n)
      (factsFrom (swKs kE1 n) (swVs (vE1 V) n)) True := by
  obtain ⟨k0, k1, -, k3, -, -⟩ := kE_ok
  have p1 := (alpha_path_k (L := L) (g := g) m sent recv vH).weaken
    (alpha_start (L := L) m sent recv vH) (fun R h => h)
  have p2 := (runE1.advP (L := L) (g := g) runE1_ok runE1_path (K := kE0) V k0).weaken
    (fun R h => holds_of_mem fun r v hrv =>
      holds_mem h (alpha_sub (L := L) m sent recv vH hV _ hrv))
    (fun R h => h)
  have p3 := sw_chainP (L := L) (g := g) (K := kE1) (V := vE1 V) hn
    (fun i hi => by
      simpa using List.all_eq_true.mp k1 i (by simpa using lt_of_lt_of_le hi hn))
    (fun i hi => vE1_has hE (by
      simpa [xRegs] using List.all_eq_true.mp k3 i (by simpa using lt_of_lt_of_le hi hn)))
  exact ⟨_, ((p1.comp p2 (by decide)).comp p3
    (by show 1847 + 66 ≤ swPc n; simp only [swPc]; omega)).mono_cond fun _ => trivial⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
