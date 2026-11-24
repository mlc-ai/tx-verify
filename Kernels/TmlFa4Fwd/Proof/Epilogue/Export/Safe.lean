-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's reads are no undefined behaviour under its reference values

The shape table `Ev` admits undefined behaviour at the scan's and the request's reads for any
address (`shape_ld`). `EvA` keeps Core's condition (`shape_ldM`): a read is undefined behaviour
only when its address is not 4-aligned. Under `Fits` the address is a cuQ word, `cuQBase + 4 i`
with `cuQBase` 4-aligned (`Pre.alignment`), so no read of the output warp is undefined behaviour
(`ref_safe`). Of its other sites only the tensor stores have an undefined-behaviour shape; their
fault conditions are not excluded yet.

`shapeA_read` steps each read site by hand (`epa_read`): `site_shape` fails on these sites because
`shape_ldM`'s condition carries the access's register count `MemAccess.regs` of the literal
instruction unreduced, which `shape_close` does not simplify (recorded for lane L in
`DECISIONS.md`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value} {ns nv : Nat}

/-- The reads' shapes with Core's misalignment condition (`True` at the other sites). -/
def EvA (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .word _ | .q0 | .q1 => (∃ bs, e.kind = .rd (wordAcc (rdAddr p L g d).toNat) bs) ∨
      ((rdAddr p L g d).toNat % 4 ≠ 0 ∧ e.kind = .ub .misaligned)
  | _ => True

set_option hygiene false in
macro "epa_shape" : tactic => `(tactic|
  site_shape s skip_by (simp at hs)
    unfolding [EvA, rdAddr, vbits]
    reg_vals [valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesWrite, valuesStart,
      partials, loopRegs, lanePreds, lookupLit]
    addr_by (ep_addr))

set_option hygiene false in
/-- One read site's shape with the misalignment condition: `shape_ldM`, then the read's location
and the condition from the address register's value. -/
macro "epa_read" : tactic => `(tactic| (
  intro t ins e o hat hi hc hf
  have hF : Holds t.regs (PTX.Flow.factsFrom _ _) := hat.2.2.2.2
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  tmpl_unfold hf PTX.loadTmpl
  try dsimp only [PTX.DType.width] at hf
  apply shape_ldM hf
  all_goals try first
    | exact hat.2.1
    | (site_read [valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesWrite,
        valuesStart, partials, loopRegs, lanePreds, lookupLit]; done)
    | (site_acc [valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesWrite,
        valuesStart, partials, loopRegs, lanePreds, lookupLit]; done)
  · intro bs hl
    refine .inl ⟨bs, ?_⟩
    simp [rdAddr, vbits, wordAcc, globalLoc, Loc.at]
  · intro h
    refine .inr ⟨?_, rfl⟩
    simp only [rdAddr, vbits] at h ⊢
    simpa [PTX.MemAccess.regs] using h))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem shapeA_read (d : D) (hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1) :
    (code p L g ent).ShapeAt (EvA p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  rcases hs with ⟨k, hs⟩ | hs | hs <;> simp only at hs <;> subst hs
  · cases k <;> epa_read
  · epa_read
  · epa_read

/-- **The reads' shapes keep the misalignment condition.** -/
theorem shapeA : (code p L g ent).Shape (EvA p L g) := by
  have h : ∀ d, (code p L g ent).ShapeAt (EvA p L g) d := by
    intro d
    by_cases hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1
    · exact shapeA_read d hs
    · intro _ _ _ _
      obtain ⟨s, w⟩ := d
      cases s <;> simp_all [EvA]
  exact @Code.Shape.of_at _ _ _ _ (code p L g ent) (EvA p L g) h

/-- **The output warp's read addresses are 4-aligned under its reference values.** -/
theorem rd_aligned (hp : Pre p L m) {d : D} (hF : Fits p L g d ns nv)
    (hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1) :
    (rdAddr p L g d).toNat % 4 = 0 := by
  have hb := batch_lt hp
  have hroom := cuQ_room hp
  obtain ⟨-, -, -, -, -, -, -, -, hcq, -⟩ := hp.alignment
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  rcases hs with ⟨k', hs⟩ | hs | hs
  · simp only [Fits, hs] at hF
    obtain ⟨r, n0, v0, hP, hR, hns, -, hL, hrd⟩ := hF
    have hidx := reqN_le hp hl hrd
    have haddr : (rdAddr p L g d).toNat = p.cuQBase + 4 * reqN p r (laneOf L g) :=
      rdAddr_eq hp hs hR hL hrd
    rw [haddr]
    omega
  all_goals
    obtain ⟨R, bal, hC⟩ : ∃ R bal, ChosenVals p L g R bal d ns nv := by
      simp only [Fits, hs] at hF
      first | exact hF | (obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩)
    obtain ⟨i, hi, hib⟩ := chosen_W hp hC
  · have haddr : (rdAddr p L g d).toNat = p.cuQBase + 4 * i := by
      simp only [rdAddr, hs, hi]
      exact addrS_toNat0 hp (by omega)
    rw [haddr]
    omega
  · have haddr : (rdAddr p L g d).toNat = p.cuQBase + 4 * (i + 1) := by
      simp only [rdAddr, hs, hi]
      exact addrS_toNat4 hp hib
    rw [haddr]
    omega

/-- **`ref_safe` of the output warp outside its tensor stores**: an event of a state's shape (`Ev`
and `EvA`) under the reference values is no undefined behaviour. The tensor stores' own fault
conditions (`tensorStoreSpec`: the map, the 128-byte aligned source, nonnegative coordinates, an
aligned box) are not excluded here (`DECISIONS.md`). -/
theorem ref_safe (hp : Pre p L m) {d : D} {e : Event} (hF : Fits p L g d ns nv)
    (hev : Ev p L g d e) (hA : EvA p L g d e) (hst : ∀ st b, d.site ≠ .store st b) (f : Fault) :
    e.kind ≠ .ub f := by
  intro hk
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  by_cases hs : (∃ k, s = .word k) ∨ s = .q0 ∨ s = .q1
  · have hal := rd_aligned hp hF hs
    rcases hs with ⟨k, rfl⟩ | rfl | rfl <;> simp only [EvA] at hA <;>
      rcases hA with ⟨bs, h⟩ | ⟨h, -⟩ <;> first | cases h | exact h hal
  · cases s <;> first | (simp at hs; done) | (simp [Ev] at hev; done) | exact absurd rfl (hst _ _)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
