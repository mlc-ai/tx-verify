-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Machine
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # The startup's events by state

The event a state of the startup fires is the event of its site (`Ev`, `shape`): the three
shuffles send, from every lane, the shared base (`sh 0`), the warp index as the code computes it
(`sh 1`, `warpW`) and the word the second shuffle returned (`sh 2`); the fence is the
mbarrier-initialization fence and the barrier is CTA barrier 0. The elections, which only warp 0
reaches, elect among the full warp at their pc, and an initialization initializes some mbarrier;
either may instead be undefined behaviour. `warpW_eq` evaluates the warp index under a
one-dimensional launch. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Startup
open PTX PTX.Proof PTX.Flow
open Epilogue (r32 i32 mad32 shru)

noncomputable section
set_option maxRecDepth 100000

/-- The event-shape table of the startup. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .sh 0 => ∃ r ok, e.kind = .shfl .idx (b32 L.sharedBase) 0 31 r ok
  | .sh 1 => ∃ r ok, e.kind = .shfl .idx (w32 (warpW L g)) 0 31 r ok
  | .sh 2 => ∃ r ok, e.kind = .shfl .idx (w32 d.x2) 0 31 r ok
  | .fence => e.kind = .fenceMbarInit
  | .bar => e.kind = .bar 0 none .sync
  | .elect _ =>
      (∃ inst ld, e.pc = d.site.pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .init _ => (∃ l c, e.kind = .mbInit l c) ∨ ∃ f, e.kind = .ub f
  | .enter _ => True

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_fence (x1 x2 x3 : BitVec 64) :
    (code p L g).ShapeAt (Ev L g) ⟨.fence, x1, x2, x3⟩ := by
  intro t ins e o _ _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_172)
  simp only [eventTmpl, tmaTmpl, widenMbarScope] at hf
  split_ifs at hf <;> (simp only [Fires] at hf; rw [hf.1]; rfl)

/-- An election with the immediate mask `-1` elects among the full warp, at its pc. -/
theorem elect_ev {t : TState} {dst : Option Nat} {pr : Nat} {ty : Option DType} {pc : Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.elect, ty, [dst, some pr], [], some (.imm (-1))⟩)) e o) :
    (∃ inst ld, e.pc = pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f := by
  rcases fires_elect_mask (bits := truncBits 32 (BitVec.ofInt 64 (-1))) rfl hf with
    ⟨inst, ld, rfl⟩ | ⟨f, rfl⟩
  · exact .inl ⟨inst, ld, rfl, rfl⟩
  · exact .inr ⟨f, rfl⟩

theorem shapeAt_elect (j : Fin 16) (x1 x2 x3 : BitVec 64) :
    (code p L g).ShapeAt (Ev L g) ⟨.elect j, x1, x2, x3⟩ := by
  intro t ins e o _ _ hc hf
  simp only [Ev]
  fin_cases j <;> simp only [Site.pc, electPc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;> exact elect_ev hf

theorem shapeAt_init (n : Fin 34) (x1 x2 x3 : BitVec 64) :
    (code p L g).ShapeAt (Ev L g) ⟨.init n, x1, x2, x3⟩ := by
  intro t ins e o _ _ hc hf
  simp only [Ev]
  fin_cases n <;> simp only [Site.pc, initPc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
    exact shape_mbInitAny (P := fun e => (∃ l c, e.kind = .mbInit l c) ∨ ∃ f, e.kind = .ub f) hf
      (fun l c => .inl ⟨l, c, rfl⟩) (fun f => .inr ⟨f, rfl⟩)

/-- **The event a state of the startup fires is the event of its site.** -/
theorem shape (hp : Pre p L m) : (code p L g).Shape (Ev L g) := by
  refine Code.Shape.of_at fun d => ?_
  obtain ⟨s, x1, x2, x3⟩ := d
  site_shape s except [.fence => shapeAt_fence x1 x2 x3, .elect _ => (shapeAt_elect _ x1 x2 x3),
      .init _ => (shapeAt_init _ x1 x2 x3)]
    skip_by (intro _ _ _ _ _ _ _ _; exact trivial)
    unfolding [Ev] reg_vals [valueOf, values, Prologue.abiFacts, lookupLit]
    addr_by (rw [hp.block])

/-- The warp index as the code computes it is the thread's warp in its CTA (`g % block / 32`,
`Prologue.warpIndex`). -/
theorem warpW_eq (hp : Pre p L m) (g : Nat) :
    warpW L g = BitVec.ofNat 64 (g % L.block / 32) := by
  obtain ⟨hn, -⟩ := hp.cluster.2.2
  unfold warpW
  rw [Launch.oneDim_tidOf hp.cluster.2.2, hn]
  have hb := hp.block
  have ht : g % L.block < 512 := hb ▸ Nat.mod_lt g (by rw [hb]; decide)
  simp only [sreg, Dim3.get, mad32, shru, r32, i32, hb]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofInt]
  norm_num
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Startup
