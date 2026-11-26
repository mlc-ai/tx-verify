-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaCoordW
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Won
import Lemmas.Flow.TensorRows

@[expose] public section

/-! # The TMA warp's gathers: their coordinate operands

`tma_gather_rows`: a gather of the TMA lane (gather `q`) records the column origin `0` and, as its
four row coordinates, the words of the lane's last load of coordinate quadruple `q` (`coordWords`:
the words of its last four reads at the load's pc), as signed 32-bit coordinates (`wordInt`). The
TMA lane's state keeps the words its loads returned (`Common/TmaCoordInv.lean`); at the gather the
coordinate registers hold them (`Tma.crdWord`), and the gather's operands are those registers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The coordinate operands of a gather4 load, when the instruction is one. -/
private def gatherForm : Op → Option (List Opnd)
  | .cpTensor _ _ _ _ _ cs _ _ none .fourRows _ => some cs
  | _ => none

/-- **Gather `i`'s code**: a unicast gather4 load whose coordinates are register 691 (the origin,
zero) and the four words of quadruple `i`. -/
private theorem gather_code : ∀ i < 16,
    (kernel.code[gatherPc i]?).bind (fun ins => gatherForm ins.op) =
      some ((691 :: Tma.ldRegs i).map Opnd.reg) := by
  decide +kernel

/-- The coordinate registers are live at their gather. -/
private theorem gather_live : ∀ i < 16, ∀ r ∈ 691 :: Tma.ldRegs i, r ∈ Flow.live (gatherPc i) := by
  decide +kernel

/-- No coordinate register is in the value tables. -/
private theorem keys_none (b : BitVec 64) (d : Tma.D) :
    ∀ r ∈ Tma.crdRegs,
      (Tma.dstVals b ++ Tma.valuesLoop P L d ++ Tma.valuesPre P L g d).lookup r = none ∧
      (Tma.valuesLaunch L g).lookup r = none := by
  intro r hr
  simp only [Tma.crdRegs, List.mem_flatMap, List.mem_range] at hr
  obtain ⟨i, hi, hr⟩ := hr
  interval_cases i <;> simp only [Tma.ldRegs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

private theorem gatherForm_eq {op : Op} {cs : List Opnd} (h : gatherForm op = some cs) :
    ∃ ca grp dst off map mb moff pol,
      op = .cpTensor ca grp dst off map cs mb moff none .fourRows pol := by
  cases op <;> simp only [gatherForm, reduceCtorEq] at h
  rename_i ca grp dst off map cs' mb moff mc mode pol
  cases mc <;> cases mode <;> simp only [reduceCtorEq, Option.some.injEq] at h
  subst h
  exact ⟨ca, grp, dst, off, map, mb, moff, pol, rfl⟩

/-- The registers `valueOf` takes from the coordinate words. -/
private theorem crd_value (P : Params) (L : Launch) (g : Nat) (d : Tma.D) (k : Fin 16)
    (hs : d.site = .gather k) (j : Fin 4) :
    Tma.valueOf P L g d ((Tma.ldRegs k.val).getD j.val 0) =
      (if k.val < 15 then d.cp else d.cq).list.getD j.val (.pred false) := by
  have hslot : ∀ k : Fin 16, ∀ j : Fin 4,
      Tma.crdSlot ((Tma.ldRegs k.val).getD j.val 0) = some (k.val, j.val) := by decide
  have hmem' : ∀ k : Fin 16, ∀ j : Fin 4, (Tma.ldRegs k.val).getD j.val 0 ∈ Tma.crdRegs := by
    decide
  have hmem := hmem' k j
  have hv : Tma.values P L g d = Tma.dstVals (Tma.rawB L d) ++ Tma.valuesLoop P L d ++
      Tma.valuesPre P L g d := by
    unfold Tma.values
    rw [hs]
  obtain ⟨h1, h2⟩ := keys_none (P := P) (L := L) (g := g) (Tma.rawB L d) d _ hmem
  unfold Tma.valueOf
  rw [hv, h1, h2]
  simp only [Option.getD_none, Tma.crdWord, hslot k j, Tma.crdSrc, hs]
  split_ifs <;> simp_all

/-- No event of a lane's prefix before an event is undefined behaviour. -/
private theorem prefix_noUb (hX : Consistent L kernel Assumptions.all m X) {g k i0 : Nat}
    {e f : Event} (he : X.get (g, k) = some e) (hi : i0 < k) (hf : (X.tr g)[i0]? = some f) :
    ∀ fl, f.kind ≠ .ub fl := by
  intro fl hk
  have h0 := take_noUb_of (g := g)
    (c := fun f : Event => match f.kind with | .ub _ => true | _ => false)
    (fun f hf => by
      obtain ⟨pc', kd⟩ := f
      cases kd <;> first | exact ⟨_, rfl⟩ | simp at hf) hX he
  have hm : f ∈ (X.tr g).take k :=
    List.mem_iff_getElem?.mpr ⟨i0, by rw [List.getElem?_take_of_lt hi]; exact hf⟩
  have := List.countP_eq_zero.mp h0 f hm
  obtain ⟨pc', kd⟩ := f
  simp only at hk
  subst hk
  simp at this

/-- **The coordinates of a TMA gather**: gather `q` of the TMA lane has the column origin `0` and
as its row coordinates the words of the lane's last load of quadruple `q`. -/
theorem tma_gather_rows (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hW : CoordWordsBits L X) {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) (hat : MbarRow.TmaAt L g pc) :
    ∃ q < 16, pc = gatherPc q ∧ s.origin 0 = 0 ∧ ∃ ys : Fin 4 → Int, s.rows = some ys ∧
      ∀ j : Fin 4, ys j = wordInt ((coordWords X g k q).getD j.val (.pred false)) := by
  have hub : ∀ f, (⟨pc, .tensorIssue a s⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  obtain ⟨hw5, hr⟩ := hat
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, -, hE, hl, -⟩ := tma_state hJ hi hev hpc hr
  obtain ⟨q, hs⟩ := Tma.ev_gather hl hE rfl
  have hpcq : pc = gatherPc q.val := by
    have := hE.1
    rw [hs] at this
    exact this
  have hpcR : 2165 < pc ∧ pc < 2332 := by
    rw [hpcq]
    exact (by decide : ∀ i : Fin 16, 2165 < gatherPc i.val ∧ gatherPc i.val < 2332) q
  obtain ⟨j, hjk, inst, hj⟩ := tma_won hp hX hFw he hub hpcR
  have hKl : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hreg := tma_region_idx hp hX hFw (fun i d => CoordInv X g i d ∧ CoordW d) hKl hj
    (fun i0 f _ hi hf => prefix_noUb hX he hi hf)
    (fun d => ⟨coordInv_plain (plain_lead d), coordW_plain (plain_lead d)⟩)
    (fun {i0 d a n f} _ _ _ _ hq hg hpcf ha => ⟨coordInv_step hg hpcf hq.1 ha,
      coordW_step hpcf (fun ac bs hk h1 h2 => by
        have hget : X.get (g, i0) = some ⟨f.pc, .rd ac bs⟩ := by
          obtain ⟨pc', kd⟩ := f
          simp only at hk
          subst hk
          exact hg
        obtain ⟨z, hz⟩ := hW hget ⟨hw5, h1, h2⟩
        exact ⟨z, by rw [rdVal_rd hk, hz]; rfl⟩) hq.2 ha⟩) hjk le_rfl hσ
  obtain ⟨d', n', heq, -, hinv, hw⟩ := hreg
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heq
  obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heq
  obtain ⟨t, ins, o, hAt, hc, hf⟩ := tma_fired hp hX he hub hσ
  obtain ⟨-, -, -, -, hH⟩ := hAt
  have hpcd : (Tma.code P L g).pc d = gatherPc q.val := by
    show d.site.pc = _
    rw [hs]
    rfl
  rw [hpcd] at hc hf
  have hform := gather_code q.val q.isLt
  rw [hc, Option.bind_some] at hform
  obtain ⟨ca, grp, dst, off, map, mb, moff, pol, hop⟩ := gatherForm_eq hform
  rw [hop] at hf
  have hcopy := fires_cpTensor_copy hf rfl
  have h4 : ∀ q < 16, Tma.ldRegs q = [(Tma.ldRegs q).getD 0 0, (Tma.ldRegs q).getD 1 0,
      (Tma.ldRegs q).getD 2 0, (Tma.ldRegs q).getD 3 0] := by decide
  rw [h4 q.val q.isLt] at hcopy
  simp only [List.map_cons, List.map_nil] at hcopy
  -- the registers hold the words
  have hlive : ∀ r ∈ 691 :: Tma.ldRegs q.val, t.regs r = some (Tma.valueOf P L g d r) := by
    intro r hr
    have hmem := mem_factsFrom (live := Tma.tmaLive d.site.pc) (val := Tma.valueOf P L g d)
      (r := r) (by rw [hs]; exact gather_live q.val q.isLt r hr)
    exact holds_mem hH hmem
  have hWd : (if q.val < 15 then d.cp else d.cq).list = coordWords X g k q.val ∧
      ∀ v ∈ (if q.val < 15 then d.cp else d.cq).list, IsW32 v := by
    simp only [CoordInv, hs] at hinv
    simp only [CoordW, hs] at hw
    by_cases h15 : q.val < 15
    · simp only [h15, ↓reduceIte]
      exact ⟨(hinv.1 h15).1, (hw.1 h15).1⟩
    · simp only [h15, ↓reduceIte]
      have h' : q.val = 15 := by have := q.isLt; omega
      rw [h']
      exact ⟨hinv.2 h', hw.2 h'⟩
  have hj : ∀ j : Fin 4, ∃ z, (coordWords X g k q.val).getD j.val (.pred false) = .bits 32 z ∧
      t.regs ((Tma.ldRegs q.val).getD j.val 0) = some (.bits 32 z) := by
    intro j
    have hmem : (Tma.ldRegs q.val).getD j.val 0 ∈ 691 :: Tma.ldRegs q.val := by
      have : ∀ q : Fin 16, ∀ j : Fin 4,
          (Tma.ldRegs q.val).getD j.val 0 ∈ 691 :: Tma.ldRegs q.val := by
        decide
      exact this q j
    have h1 := hlive _ hmem
    rw [crd_value P L g d q hs j, hWd.1] at h1
    have h2 : IsW32 ((coordWords X g k q.val).getD j.val (.pred false)) := by
      rw [← hWd.1]
      apply hWd.2
      fin_cases j <;> simp [Tma.Quad.list]
    obtain ⟨z, hz⟩ := h2
    exact ⟨z, hz, by rw [h1, hz]⟩
  have h691 : t.regs 691 = some (.bits 32 (PTX.Flow.Arith32.i32 0)) := by
    have := hlive 691 List.mem_cons_self
    rw [this]
    unfold Tma.valueOf Tma.values
    rw [hs]
    rfl
  obtain ⟨z0, hw0, hr0⟩ := hj 0
  obtain ⟨z1, hw1, hr1⟩ := hj 1
  obtain ⟨z2, hw2, hr2⟩ := hj 2
  obtain ⟨z3, hw3, hr3⟩ := hj 3
  obtain ⟨hor, hrow⟩ := tensorLoadCopy_rows hcopy h691 hr0 hr1 hr2 hr3
  refine ⟨q.val, q.isLt, hpcq, ?_, _, hrow, fun j => ?_⟩
  · rw [hor]
    decide
  · fin_cases j
    · show (BitVec.ofNat 32 (truncBits 32 z0).toNat).toInt =
        wordInt ((coordWords X g k q.val).getD 0 (.pred false))
      have h : (coordWords X g k q.val).getD 0 (.pred false) = .bits 32 z0 := hw0
      rw [h]
      rfl
    · show (BitVec.ofNat 32 (truncBits 32 z1).toNat).toInt =
        wordInt ((coordWords X g k q.val).getD 1 (.pred false))
      have h : (coordWords X g k q.val).getD 1 (.pred false) = .bits 32 z1 := hw1
      rw [h]
      rfl
    · show (BitVec.ofNat 32 (truncBits 32 z2).toNat).toInt =
        wordInt ((coordWords X g k q.val).getD 2 (.pred false))
      have h : (coordWords X g k q.val).getD 2 (.pred false) = .bits 32 z2 := hw2
      rw [h]
      rfl
    · show (BitVec.ofNat 32 (truncBits 32 z3).toNat).toInt =
        wordInt ((coordWords X g k q.val).getD 3 (.pred false))
      have h : (coordWords X g k q.val).getD 3 (.pred false) = .bits 32 z3 := hw3
      rw [h]
      rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
