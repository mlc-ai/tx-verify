-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Select
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Store
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Proof.SchedulerFrame

@[expose] public section

/-! # The output warp's stores are the CTA's work item

Every tensor store of a consistent execution is a store of a lane of warp 13 (`output_event`)
at a store state of its machine (`store_kind`). The state holds the first pass's choice
(`Fits`), which is the request whose work holds the CTA, with the scheduler's coordinates
(`chosen_spec`). So the store writes the CTA's work item: `store_issue`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The operand words of a store are the words of the CTA's work item. -/
theorem storeVals_eq (hp : Pre p L m) {g : Nat} {d : D} {st : Fin 2} {bx : Fin 4} {b : Nat}
    (hb : b < p.batch) (hlo : tilePrefix p b * p.heads ≤ g / L.block)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads)
    (hrow : (coords p L g d).row =
      W (2 ^ 30 + 256 * (Epilogue.assignedCoordinates p b (g / L.block)).1))
    (hhead : (coords p L g d).head = W (Epilogue.assignedCoordinates p b (g / L.block)).2)
    (hc0 : d.c0 = W (p.qOffset b)) (hc1 : d.c1 = W (p.qOffset (b + 1))) :
    storeVals p L g d st bx = Epilogue.storeWords p b
      (Epilogue.assignedCoordinates p b (g / L.block)).2
      (Epilogue.assignedCoordinates p b (g / L.block)).1 st bx := by
  obtain ⟨ht, hh⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  generalize (Epilogue.assignedCoordinates p b (g / L.block)).1 = tile at ht hrow ⊢
  generalize (Epilogue.assignedCoordinates p b (g / L.block)).2 = head at hh hhead ⊢
  have hq := qOffset_lt hp (show b ≤ p.batch by omega)
  have hq1 := qOffset_lt hp (show b + 1 ≤ p.batch by omega)
  have hmono := hp.qOffset_mono (show b ≤ b + 1 by omega) (show b + 1 ≤ p.batch by omega)
  have hql := hp.qLength_fits hb
  have hhd := heads_lt hp
  have hlen : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
  have hr0 : sub32 (add32 (coords p L g d).row d.c0) d.c1 =
      W (2 ^ 30 - p.qLength b + 256 * tile) := by
    rw [hrow, hc0, hc1, add32_W (by omega), sub32_W (by omega) (by omega)]
    congr 1; omega
  have htr (x : Nat) (hx : x < 2 ^ 32) : truncBits 32 (W x) = W x := r32_W hx
  have hcol : truncBits 32 (colV bx) = BitVec.ofNat 64 (32 * bx.val) := by
    fin_cases bx <;> rfl
  have hrw : truncBits 32 (rowV p L g d st) =
      BitVec.ofNat 64 (2 ^ 30 - p.qLength b + Epilogue.stageRow tile st) := by
    simp only [rowV, Epilogue.stageRow, hr0]
    fin_cases st
    · split
      · rw [htr _ (by omega)]
        congr 1
      · exact absurd rfl ‹_›
    · split
      · exact absurd ‹_› (by decide)
      · rw [show (128 : Int) = ((128 : Nat) : Int) from rfl, addi_W (by decide) (by omega),
          htr _ (by omega)]
        congr 1
  have hh : truncBits 32 (coords p L g d).head = BitVec.ofNat 64 head := by
    rw [hhead, htr _ (by omega)]
  have h1 : truncBits 32 d.c1 = BitVec.ofNat 64 (p.qOffset (b + 1)) := by
    rw [hc1, htr _ (by omega)]
  simp only [storeVals, Epilogue.storeWords, hcol, hrw, hh, h1]

/-- **Every tensor store writes its CTA's work item**: through the O map, from a staging slot
of its CTA, at the scheduler's coordinates of the request whose work holds the CTA. -/
theorem store_issue (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    addr = p.oMapAddress ∧ ∃ b < p.batch, ∃ (st : Fin 2) (bx : Fin 4),
      tilePrefix p b * p.heads ≤ i.1 / L.block ∧ i.1 / L.block < tilePrefix p (b + 1) * p.heads ∧
      s = Epilogue.writebackStoreSpec p L i.1 b
        (Epilogue.assignedCoordinates p b (i.1 / L.block)).2
        (Epilogue.assignedCoordinates p b (i.1 / L.block)).1 st bx := by
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hpc := tensorStoreSite hX he
  simp only [outputStoreSites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, hj5, d, n, hσ, hF, hE, -⟩ := output_event (p := p) hp hX he
    (by simp only; omega) (by simp only; omega) (by rintro _ _ ⟨⟩)
  obtain ⟨-, o, hf⟩ := fired hp hX he hσ
  obtain ⟨site, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases site <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self] at hE
  case store st bx =>
  rcases store_kind hp hg rfl hf with ⟨f, hk⟩ | hk
  · cases hk
  simp only [Kind.tensorStore.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨R, bal', hC, hc0, hc1⟩ := hF
  obtain ⟨b, hb, hlo, hhi, hch, hco⟩ := chosen_spec hp hg hC
  have hbb := batch_lt hp
  simp only at hch hc0 hc1
  rw [hch, qv_W hp (by omega)] at hc0
  rw [hch, addi1_W (by omega), qv_W hp (by omega)] at hc1
  have hvals := storeVals_eq (st := st) (bx := bx) hp hb hlo hhi (by rw [hco]) (by rw [hco])
    hc0 hc1
  obtain ⟨ht, hh⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  refine ⟨rfl, b, hb, st, bx, hlo, hhi, ?_⟩
  rw [hvals, Epilogue.storeSpec, Epilogue.storeOrigin hp hb hh ht st bx]
  rfl

/-- **A lane frees a stage only when its CTA has a work item.** -/
theorem free_work (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .arrive target tx n rel sc⟩) (hpc : pc = 2983 ∨ pc = 2985) :
    g / L.block < tilePrefix p p.batch * p.heads := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, hj5, -⟩ := output_event (p := p) hp hX he (by simp only; omega)
    (by simp only; omega) (by rintro _ _ ⟨⟩)
  obtain ⟨d, n, hσ, st, hs, -⟩ := arrive_site hp hX hw hj5 he
  have hF := (fits hp hX hg hw hσ).1
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only at hs
  subst hs
  obtain ⟨R, bal', hC, -⟩ := hF
  obtain ⟨-, -, -, hhigh, -, -⟩ := picked_group hp hg hC.1.pre
  have := Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show min p.batch (31 * R + 31) ≤ p.batch by omega))
  omega

/-- **A store follows its stage's successful ready poll**, and reads that stage's staging slot. -/
theorem store_ready (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    ∃ (st : Fin 2) (bx : Fin 4), s.sharedBase = Epilogue.sharedSlot L i.1 st bx ∧
      ∃ j < i.2, X.get (i.1, j) =
        some ⟨(Site.ready st).pc, .wait (readyLoc L i.1 st) 0 true true .cta⟩ := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hpc := tensorStoreSite hX he
  simp only [outputStoreSites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, hj5, d, n, hσ, -, hE, -⟩ := output_event (p := p) hp hX he
    (by simp only; omega) (by simp only; omega) (by rintro _ _ ⟨⟩)
  obtain ⟨-, o, hf⟩ := fired hp hX he hσ
  obtain ⟨site, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases site <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self] at hE
  case store st bx =>
  rcases store_kind hp hg rfl hf with ⟨f, hk⟩ | hk
  · cases hk
  simp only [Kind.tensorStore.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  refine ⟨st, bx, rfl, ?_⟩
  obtain ⟨j, hjk, hj5', pc', q, acq, sc, he'⟩ :=
    ready_before (st := st) hp hX hw hσ (by simp [acqd]) he
  obtain ⟨st', hpc', ht, rfl, rfl, rfl⟩ := wait_site hp hX hw hj5' he'
  obtain rfl := readyLoc_inj ht.symm
  exact ⟨j, hjk, by rw [he', hpc']⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
