-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section
namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An unguarded scalar load whose successor state records the loaded word. The destination
register is not among the facts before the load; after it, the facts of the successor hold
from the rebuilt value, and the segment starts with that value among its facts. A malformed
read faults the thread. -/
theorem dataLoadU {d : C.D} {dn : List (Option Byte) → C.D} {a : MemAccess} {r : Nat}
    (fetch : K.code[C.pc d]? = some ⟨none,.mem a⟩) (nonlocal : (Op.mem a).isLocal = false)
    (load : a.kind = .load) (cached : a.nc = false) (ext : a.ext = .same) (reg : a.regs = [r])
    (scalar : C.sub d = 0) (acc : C.acc d = []) (scalar' : ∀ bs, C.sub (dn bs) = 0)
    (acc' : ∀ bs, C.acc (dn bs) = [])
    (go : ∀ x bs, C.next d ⟨C.pc d,.rd x bs⟩ = some (some (dn bs))) (inv : ∀ bs, C.inv (dn bs))
    (free : r ∉ (C.facts d).map Prod.fst)
    (seg : ∀ bs v, rebuild 3 bs = .ok v →
      SegU K A L g (C.pc d + 1) ((r,v) :: C.facts d) (C.pc (dn bs)) (C.facts (dn bs))) :
    C.StepAtU d where
  site := fun _ => ⟨_,fetch,nonlocal,trivial⟩
  step := by
    intro t e u ins atD _ hi fire
    obtain rfl := Option.some.inj (hi.symm.trans fetch)
    obtain ⟨x,bs,rfl,rfl⟩ := fires_load load cached fire ext
    refine .inl (.inr ⟨dn bs,?_⟩)
    rw [reg]
    have hat := at_of_atD atD scalar acc
    have hu : ∃ s, Relation.ReflTransGen (Tau K A L g) (afterLoad t [r] bs) s ∧
        C.GoodU (some (dn bs)) s := by
      cases h : rebuild 3 bs with
      | error f =>
        exact goodU_of_dead _ (Machine.dead_of_fault (f := f) (by simp only [afterLoad,h]))
      | ok v =>
        have ⟨pc,sub,accum,fault,regs⟩ := hat
        rw [afterLoad_ok sub accum h]
        apply landsU _ (seg bs v h) (inv bs) (scalar' bs) (acc' bs)
        exact ⟨congrArg (·+1) pc,rfl,rfl,fault,by simp [setReg],
          holds_update regs fun p hp eq => free (eq ▸ List.mem_map_of_mem hp)⟩
    obtain ⟨s,ht,hs⟩ := hu
    exact ⟨s,go _ _,ht,hs⟩

end PTX.Flow.Code
