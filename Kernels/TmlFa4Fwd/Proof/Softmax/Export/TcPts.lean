-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcCount
public import Kernels.TmlFa4Fwd.Proof.Softmax.Order
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane's warp-collective `tcgen05` events by the places

The warp-collective `tcgen05` events before a state (`soft_tc`) are those of the sites the state has
passed (`tcPts`), with the implicit wait of a delayed store when it has been made (`tc_count`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (allSites mem_allSites ptsOf before passed)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- The warp-collective `tcgen05` events at a site. -/
def Softmax.tw : Softmax.Site → Nat
  | .sld _ _ | .sldw _ | .pwst _ _ => 1
  | .pst .plain _ => 1
  | .pst _ q => if q.val = 0 then 2 else 1
  | _ => 0

/-- The points of the warp-collective `tcgen05` events. -/
def Softmax.tcPts : List Nat := allSites.flatMap fun s => List.replicate (Softmax.tw s) s.pos

/-- The events of a delayed store's site already made. -/
def Softmax.ex (d : Softmax.D) : Nat := Progress.Sm.subOff d

theorem delayed_site {s : Softmax.Site} (h : s.delayed = true) :
    s = .pst .first 0 ∨ s = .pst .bias 0 := by
  have h1 : allSites.all (fun s => !s.delayed || decide (s = .pst .first 0) ||
      decide (s = .pst .bias 0)) = true := by decide +kernel
  simpa [h] using List.all_eq_true.mp h1 s (mem_allSites s)

private theorem tw_pst : ∀ (r : Softmax.Rd) (q : Fin 4), 0 < Softmax.tw (.pst r q) := by
  intro r; cases r <;> decide

/-- The site of a warp-collective `tcgen05` event of a softmax lane. -/
theorem tc_site {d : Softmax.D} (hev : Softmax.Ev p L g d e) (hne : ∀ f, e.kind ≠ .ub f) :
    isTcColl e = decide (0 < Softmax.tw d.site) := by
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hne
  cases s
  all_goals simp only [Softmax.Ev, Softmax.rdOrUb, Softmax.tcLdOrUb, Epilogue.Ev,
    Softmax.Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals first
    | exact absurd rfl (hne _)
    | rfl
    | simp [isTcColl, tw_pst]


private def base (b : Bool) (s : Softmax.Site) : Int :=
  (ptsOf b .tcld).countP (before s) + (ptsOf b .tcst).countP (before s) +
    6 * (ptsOf b .nb).countP (before s) - 3 * (ptsOf b .sb).countP (before s)

private theorem base_tab : [false, true].all (fun b => allSites.all fun s =>
    decide (base b s + Softmax.tcCorr s true = Softmax.tcPts.countP (before s)) &&
    decide (base b s + Softmax.tcCorr s false = Softmax.tcPts.countP (before s) +
      (if s.delayed then 1 else 0))) = true := by decide +kernel

private theorem rnd (b : Bool) : Softmax.tcPts.countP Softmax.inBias = 11 ∧
    Softmax.tcPts.countP Softmax.inPlain = 14 ∧
    (ptsOf b .tcld).countP Softmax.inBias = 4 ∧ (ptsOf b .tcld).countP Softmax.inPlain = 4 ∧
    (ptsOf b .tcst).countP Softmax.inBias = 4 ∧ (ptsOf b .tcst).countP Softmax.inPlain = 4 ∧
    (ptsOf b .nb).countP Softmax.inBias = 1 ∧ (ptsOf b .nb).countP Softmax.inPlain = 1 ∧
    (ptsOf b .sb).countP Softmax.inBias = 1 ∧ (ptsOf b .sb).countP Softmax.inPlain = 0 := by
  cases b <;> decide +kernel

/-- **The warp-collective `tcgen05` events before a state of a softmax lane** are those of the
points
it has passed and those of its site already made. -/
theorem tc_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) (hub : ¬ HasUb X) {d : Softmax.Control.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)))
    (hub0 : n .ub = 0) {rb rp : Nat}
    (hc : ∀ c, c.pointed = true →
      n (.soft c) = passed (ptsOf (Softmax.lz L g) c) d.site rb rp) :
    ((X.tr g).take k).countP isTcColl = passed Softmax.tcPts d.site rb rp + Softmax.ex d := by
  have h : (((X.tr g).take k).countP isTcColl : Int) = n (.soft .tcld) + n (.soft .tcst) +
      6 * n (.soft .nb) - 3 * n (.soft .sb) + Softmax.tcCorr d.site (d.k == 0) :=
    soft_tc hp hX hFw hg k _ (by rintro j _ ⟨pc, _⟩ he f rfl; exact hub ⟨_, pc, f, he⟩) hσ hub0
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp base_tab (Softmax.lz L g)
    (by cases Softmax.lz L g <;> simp)) d.site (mem_allSites _)
  rw [Bool.and_eq_true] at h1
  have b1 := of_decide_eq_true h1.1
  have b2 := of_decide_eq_true h1.2
  simp only [base] at b1 b2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := rnd (Softmax.lz L g)
  have e1 := hc .tcld rfl
  have e2 := hc .tcst rfl
  have e3 := hc .nb rfl
  have e4 := hc .sb rfl
  simp only [passed, r3, r4, r5, r6, r7, r8, r9, r10] at e1 e2 e3 e4
  have hex : (Softmax.ex d : Int) = if d.k = 0 then 0 else if d.site.delayed then 1 else 0 := by
    obtain ⟨s, v, kk, acc⟩ := d
    by_cases hd : s.delayed = true
    · rcases delayed_site hd with rfl | rfl <;>
        (show ((min kk.val 1 : Nat) : Int) = _
         by_cases h0 : kk = 0
         · simp [h0]
         · have : kk.val ≠ 0 := fun h => h0 (Fin.ext h)
           simp only [h0, hd, ite_true, ite_false]
           omega)
    · have : Softmax.ex ⟨s, v.scheduler, kk, acc⟩ = 0 := by
        unfold Softmax.ex Progress.Sm.subOff
        split <;> first | rfl | (rename_i hs; simp only at hs; subst hs; exact absurd rfl hd)
      show ((Softmax.ex ⟨s, v.scheduler, kk, acc⟩ : Nat) : Int) = _
      rw [this]
      simp [hd]
  simp only [passed, r1, r2]
  by_cases h0 : d.k = 0
  · simp only [h0, beq_self_eq_true, ite_true] at h hex
    omega
  · have hb : (d.k == 0) = false := by simpa using h0
    simp only [h0, ite_false] at hex
    rw [hb] at h
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
