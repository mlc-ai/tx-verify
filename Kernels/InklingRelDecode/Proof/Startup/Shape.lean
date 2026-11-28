-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Machine
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The startup's events by state

The event a state of the startup fires is the event of its site (`Ev`, `shape`): the allocation
and the address store (warp 0), the two CTA barriers, the four-byte load of the base word at the
shared base, the relinquish, and the full-warp shuffle whose operand is the thread's warp index.
The exits have no entry (`True`): the glue replaces them by their roles' first states. One call of
`site_shape`; the load, whose address is the symbol `global_smem`, by `shapeAt_ld0`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

/-- The event-shape table of the startup. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .alloc => e = ⟨11, .tc (.resource .one (some ⟨.shared, g / L.block, L.sharedBase⟩)
      (.alloc 512))⟩
  | .allocWr => ∃ col, col < 2 ^ 16 ∧ e = ⟨11, .wr
      { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 col).toBytes⟩
  | .bar0 => e = ⟨12, .bar 0 none .sync⟩
  | .bar1 => e = ⟨14, .bar 0 none .sync⟩
  | .ld0 => ∃ ac bs, e = ⟨13, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ ac.size = 4 ∧ ac.elem = 0
  | .relinq => e = ⟨15, .tc (.resource .one none .relinquish)⟩
  | .shfl => ∃ recv ok, e = ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩
  | .enter _ => True

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ld0 (hS : SharedOk L) (tm : Nat) (x : BitVec 64) :
    (code Q L g).ShapeAt (OrUb (Ev L g)) ⟨.ld0, tm, x, bw⟩ := by
  intro t ins e o hat hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_13)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  obtain ⟨ac, bs, he, hl, hsz, hel⟩ := fires_ldv_sharedSym (o := 0) (off := 0) rfl
    rfl rfl rfl rfl rfl rfl rfl rfl (by have := hS.2; omega) hf
  have hsub : t.sub = 0 := hat.2.1
  rw [hsub] at hl hel
  exact ⟨ac, bs, he, by simpa using hl, hsz, hel⟩

set_option hygiene false in
macro "st_addr" : tactic => `(tactic| first
  | exact hb
  | (simp only [Startup.sb_toNat hS]; have := hS.1; omega)
  | omega)

/-- **The shape table of the startup.** -/
theorem shape_code (hb : L.block % 32 = 0) (hS : SharedOk L) :
    (code Q L g).Shape (OrUb (Ev L g)) := by
  refine Code.Shape.of_at fun d => ?_
  obtain ⟨s, tm, x, bw⟩ := d
  site_shape s except [.ld0 => shapeAt_ld0 hS tm x]
    skip_by (intro _ _ _ _ _ _ _ _; exact .inl trivial)
    unfolding [OrUb, Ev, Startup.sb_toNat hS]
    reg_vals [valueOf, values, Startup.table, lookupLit]
    addr_by (st_addr)

/-- **The event a state of the startup fires is its shape** unless it is undefined behaviour,
under `Pre`. -/
theorem shape (hp : Pre Q L m) :
    (code Q L g).Shape (fun d e => (∀ f, e.kind ≠ .ub f) → Ev L g d e) :=
  fun hat hi hc hf hu => by
    rcases shape_code (by rw [hp.block]) (sharedOk_of_pre hp) hat hi hc hf with
      h | ⟨f', hf'⟩
    · exact h
    · exact absurd hf' (hu f')

end
end PTX.Kernels.InklingRelDecode.Proof.Startup
