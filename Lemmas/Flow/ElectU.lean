-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU
public import Lemmas.Flow.Step.Combinators

@[expose] public section

/-! # An election, a tensor store and a bulk commit for UB-tolerant control machines

`Code.electU`: an `elect.sync` into a leader register and a predicate whose successor depends on
the leader; the segment after it starts with both facts. `fires_cpTensorStore_next`,
`fires_bulkCommit_next`: a TMA store and a bulk commit that fire continue at the next
instruction. -/

namespace PTX.Flow
open PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- A TMA tensor store that fires continues at the next instruction. -/
theorem fires_cpTensorStore_next {t u : TState} {map : Opnd} {cs : List Opnd} {src : Nat}
    {off : Int} {policy : Option Opnd} {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat}
    {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e
      (some u)) : u = PTX.next t := by
  simp only [eventTmpl, tensorStoreTmpl] at hf
  cases hs : tensorStoreSpec L g t map cs src off policy mode reduce with
  | error f => simp only [hs, bind, Except.bind, ofExec, Fires] at hf; cases hf.2
  | ok r =>
    simp only [hs, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
    exact Option.some.inj hf.2

/-- A bulk commit continues at the next instruction. -/
theorem fires_bulkCommit_next {t u : TState} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t .bulkCommit) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, tensorStoreTmpl, Fires] at hf
  exact Option.some.inj hf.2

end PTX.Flow

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An election into the leader register `r` and the predicate `p`: the successor `dst ld`
follows the leader `ld`, and the segment after it knows both registers. -/
theorem electU {d : C.D} {dst : Nat → C.D} {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hc : K.code[C.pc d]? = some ⟨none, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (hr : r ∉ (C.facts d).map Prod.fst) (hp : p ∉ (C.facts d).map Prod.fst) (hrp : r ≠ p)
    (hn : ∀ mk inst ld, C.next d ⟨C.pc d, .elect mk inst ld⟩ = some (some (dst ld)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ ld, C.sub (dst ld) = 0)
    (ha' : ∀ ld, C.acc (dst ld) = []) (hi : ∀ ld, C.inv (dst ld))
    (seg : ∀ ld, SegU K A L g (C.pc d + 1) ((p, .pred (laneOf L g == ld)) ::
      (r, .bits 32 (BitVec.ofNat 64 ld)) :: C.facts d) (C.pc (dst ld)) (C.facts (dst ld))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc, rfl, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
    have h0 := at_of_atD hat hs ha
    have h1 : At (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) (C.pc d)
        ((r, .bits 32 (BitVec.ofNat 64 ld)) :: C.facts d) :=
      ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self ..,
        holds_update h0.2.2.2.2 (fun q hq he => hr (he ▸ List.mem_map_of_mem hq))⟩
    have h2 := At.set (r := p) (v := .pred (laneOf L g == ld)) h1 (fun q hq he => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hrp he
      · exact hp (he ▸ List.mem_map_of_mem hq))
    obtain ⟨u, ht, hu⟩ := landsU h2 (seg ld) (hi ld) (hs' ld) (ha' ld)
    exact .inl (.inr ⟨dst ld, u, hn mk inst ld, ht, hu⟩)

end PTX.Flow.Code
