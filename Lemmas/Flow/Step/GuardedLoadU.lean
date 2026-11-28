-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section
namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The active arm of a scalar load. A malformed read may fault and a successful
read can write any payload when the control facts carried forward omit its destination. -/
theorem guardedLoadU {d dn : C.D} {gd : Option (Nat × Bool)} {a : MemAccess} {r : Nat}
    (fetch : K.code[C.pc d]? = some ⟨gd,.mem a⟩) (nonlocal : (Op.mem a).isLocal = false)
    (guardAt : GuardTrue (C.facts d) gd) (load : a.kind = .load)
    (cached : a.nc = false) (ext : a.ext = .same) (reg : a.regs = [r])
    (scalar : C.sub d = 0) (acc : C.acc d = []) (scalar' : C.sub dn = 0) (acc' : C.acc dn = [])
    (go : ∀ x bs, C.next d ⟨C.pc d,.rd x bs⟩ = some (some dn)) (inv : C.inv dn)
    (free : r ∉ (C.facts d).map Prod.fst)
    (seg : SegU K A L g (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_,fetch,nonlocal,guardAt⟩
  step := by
    intro t e u ins atD _ hi fire
    obtain rfl := Option.some.inj (hi.symm.trans fetch)
    obtain ⟨x,bs,rfl,rfl⟩ := fires_load load cached fire ext
    refine .inl (.inr ⟨dn,?_⟩)
    rw [reg]
    have hat := at_of_atD atD scalar acc
    have hu : ∃ s, Relation.ReflTransGen (Tau K A L g) (afterLoad t [r] bs) s ∧
        C.GoodU (some dn) s := by
      cases h : rebuild 3 bs with
      | error f =>
        exact goodU_of_dead _ (Machine.dead_of_fault (f := f) (by simp only [afterLoad,h]))
      | ok v =>
        have ⟨pc,sub,accum,fault,regs⟩ := hat
        rw [afterLoad_ok sub accum h]
        apply landsU _ seg inv scalar' acc'
        exact ⟨congrArg (·+1) pc,rfl,rfl,fault,holds_update regs
          fun p hp eq => free (eq ▸ List.mem_map_of_mem hp)⟩
    obtain ⟨s,ht,hs⟩ := hu
    exact ⟨s,go _ _,ht,hs⟩

end PTX.Flow.Code
