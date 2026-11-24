-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Flow
open PTX.Proof

/-- A successful ballot records its actual predicate and returned word. No predicate fact is
needed: a failed register read cannot have a continuing callback. -/
theorem fires_ballotU {A L g t pc d a neg ty mask e u}
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.vote .ballot neg, ty, [some d], [.reg a], some mask⟩)) e (some u)) :
    ∃ p b, e = ⟨pc, .vote (2 ^ 32 - 1) p b⟩ ∧
      u = PTX.next (setReg t d (.bits 32 (BitVec.ofNat 64 b.toNat))) := by
  simp only [eventTmpl, warpTmpl_vote, voteTmpl] at hf
  cases hm : readBits L g t 32 mask with
  | error f => simp only [hm, Fires] at hf; cases hf.2
  | ok m =>
    cases hp : readPred L g t (.reg a) with
    | error f => simp only [hm, hp, Fires] at hf; cases hf.2
    | ok pred =>
      simp only [hm, hp] at hf
      split at hf
      · rename_i h
        obtain ⟨b, he, hu⟩ := hf
        exact ⟨_, b, h.1 ▸ he, Option.some.inj hu⟩
      · cases hf.2

namespace Code
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- Control may branch on the ballot without a model of the floating-point comparison. -/
theorem ballotU {d : C.D} {dst : BitVec 32 → C.D} {ty dv pr neg mask}
    (hc : K.code[C.pc d]? = some ⟨none,.warp ⟨.vote .ballot neg, ty, [some dv], [.reg pr],
      some mask⟩⟩)
    (hoff : dv ∉ (C.facts d).map Prod.fst)
    (hn : ∀ p b, C.next d ⟨C.pc d, .vote (2 ^ 32 - 1) p b⟩ = some (some (dst b)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ b, C.sub (dst b) = 0)
    (ha' : ∀ b, C.acc (dst b) = []) (hi : ∀ b, C.inv (dst b))
    (seg : ∀ b, SegU K A L g (C.pc d+1)
      ((dv,.bits 32 (BitVec.ofNat 64 b.toNat)) :: C.facts d) (C.pc (dst b)) (C.facts (dst b))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc, rfl, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨p, b, rfl, rfl⟩ := fires_ballotU hf
    have ht := At.set (r := dv) (v := .bits 32 (BitVec.ofNat 64 b.toNat)) (at_of_atD hat hs ha)
      (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
    obtain ⟨u, ht, hu⟩ := landsU ht (seg b) (hi b) (hs' b) (ha' b)
    exact .inl (.inr ⟨dst b, u, hn p b, ht, hu⟩)

end Code
end PTX.Flow
