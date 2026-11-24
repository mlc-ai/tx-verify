-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartStart
public import Kernels.InklingRelDecode.Proof.Thread.EvDProBase
public import Kernels.InklingRelDecode.Proof.Thread.EvWBase
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # Event shapes of the common start

What the events of the common start (pc 11 to 27) are, over its abstract states `DStart.D`
(`Shape`, one clause per site; the pc stays behind `evPc`):

* `alloc` (warp 0, every lane): `tcgen05.alloc.cta_group::1 [global_smem], 512`;
* `allocWr` (warp 0, lane 0): the store of the allocated address, `b32 col` with `col < 2 ^ 16`;
* `bar0`, `bar1`: `bar.sync 0` without a count;
* `ld0`: the load of the Tensor Memory base word: four bytes at `sharedBase`, element 0;
* `relinq` (warp 0): `tcgen05.relinquish_alloc_permit.cta_group::1`;
* `shfl`: the full-warp `shfl.sync.idx` of the warp index from lane 0;
* `toProA`: `setmaxnreg.inc 256`, the prologue's first site.

`shape_code` proves the table of the code machine by one call of `site_shape` (the shared load
`ld0`, whose address is the symbol `global_smem`, by `shapeAt_ld0`); `shape` reads it at a fired
event, which is never undefined behaviour. The launch facts used are the shared window
(`ProA.SharedOk`) and a block of whole warps (`Pre.block`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The source position of the events a site fires: the instruction's own position. -/
def evPc (s : Site) : Nat := s.pc

/-- The event `e` fires from a concrete thread state of the abstract state `d` of the common
start, continuing in `o` (`none` after a fault). -/
def Fired (L : Launch) (g : Nat) (Q : Params) (d : D) (e : Event) (o : Option TState) : Prop :=
  ∃ t, AtS L g Q d t ∧ Inv L g Q d ∧ ∃ ins, kernel.code[d.site.pc]? = some ins ∧
    Fires d.site.pc (eventTmpl asms L g t ins.op) e o

/-- The code machine's `Fired` at `some d` is `Fired`. -/
theorem Fired_of_machine {L : Launch} {g : Nat} {Q : Params} {d : D} {e : Event}
    {o : Option TState} (h : (code L g Q).toMachine.Fired (some d) e o) : Fired L g Q d e o := by
  obtain ⟨t, ⟨ha, hinv⟩, hf⟩ := h
  obtain ⟨ins, hc, -, -⟩ := site_ok hinv
  refine ⟨t, ha, hinv, ins, hc, ?_⟩
  have hpc : t.pc = d.site.pc := ha.1
  rw [hpc] at hf
  change Fires d.site.pc ((code L g Q).tmpl (some d) t) e o at hf
  simpa only [Flow.Code.tmpl, hc] using hf

variable {L : Launch} {g : Nat} {Q : Params} {d : D} {e : Event} {u : TState}

/-- What the event of a site is. -/
def Shape (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .alloc => e = ⟨evPc d.site, .tc (.resource .one (some ⟨.shared, g / L.block, L.sharedBase⟩)
      (.alloc 512))⟩
  | .allocWr => ∃ col, col < 2 ^ 16 ∧ e = ⟨evPc d.site, .wr
      { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 col).toBytes⟩
  | .bar0 => e = ⟨evPc d.site, .bar 0 none .sync⟩
  | .bar1 => e = ⟨evPc d.site, .bar 0 none .sync⟩
  | .ld0 => ∃ ac bs, e = ⟨evPc d.site, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ ac.size = 4 ∧ ac.elem = 0
  | .relinq => e = ⟨evPc d.site, .tc (.resource .one none .relinquish)⟩
  | .shfl => ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩
  | .toProA => ∃ inst, e = ⟨evPc d.site, .setMaxReg true 256 inst⟩

/-- The shared base as the register `%r73` (`mov.b32 %r73, global_smem`) holds it. -/
theorem sb_toNat (hS : ProA.SharedOk L) :
    (BitVec.ofNat 64 (L.sharedBase + 0)).toNat % 2 ^ 32 = L.sharedBase := by
  have := hS.2
  simp only [BitVec.toNat_ofNat]
  omega

/-- The load of the base word: its address is the symbol `global_smem`. -/
theorem shapeAt_ld0 (hS : ProA.SharedOk L) (w : Value) :
    (code L g Q).ShapeAt (OrUb (Shape L g)) ⟨.ld0, w⟩ := by
  intro t ins e o hat hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_13)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  obtain ⟨ac, bs, he, hl, hsz, hel⟩ := EvW.fires_ldv_sharedSym (o := 0) (off := 0) rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (by have := hS.2; omega) hf
  have hsub : t.sub = 0 := hat.2.1
  rw [hsub] at hl hel
  exact ⟨ac, bs, he, by simpa using hl, hsz, hel⟩

set_option hygiene false in
/-- The common start's side conditions: the block, the shared base register. -/
macro "dstart_addr" : tactic => `(tactic| first
  | exact hb
  | (simp only [sb_toNat hS]; have := hS.1; omega)
  | omega)

/-- **The shape table of the common start.** -/
theorem shape_code (hb : L.block % 32 = 0) (hS : ProA.SharedOk L) :
    (code L g Q).Shape (OrUb (Shape L g)) := by
  refine Code.Shape.of_at fun d => ?_
  obtain ⟨s, w⟩ := d
  site_shape s except [.ld0 => shapeAt_ld0 hS w]
    unfolding [OrUb, Shape, evPc, sb_toNat hS]
    reg_vals [valueOf, table, lookupLit]
    addr_by (dstart_addr)

/-- **The event fired at a state of the common start is its shape.** -/
theorem shape (hb : L.block % 32 = 0) (hS : ProA.SharedOk L) (hF : Fired L g Q d e (some u)) :
    Shape L g d e := by
  obtain ⟨t, ha, hi, ins, hc, hf⟩ := hF
  exact OrUb.of_some (shape_code hb hS ha hi hc hf) hf

/-- The shapes under `Pre`: the block is a whole number of warps, the shared window is aligned. -/
theorem shape_of_pre {mem0 : Mem0} (hpre : Pre Q L mem0) (hF : Fired L g Q d e (some u)) :
    Shape L g d e :=
  shape (by rw [hpre.block]) (ProA.sharedOk_of_pre hpre) hF

theorem shape_alloc (hb : L.block % 32 = 0) (hS : ProA.SharedOk L)
    (hF : Fired L g Q d e (some u)) (hs : d.site = .alloc) :
    e = ⟨evPc d.site, .tc (.resource .one (some ⟨.shared, g / L.block, L.sharedBase⟩)
      (.alloc 512))⟩ := by
  simpa only [Shape, hs] using shape hb hS hF

theorem shape_allocWr (hb : L.block % 32 = 0) (hS : ProA.SharedOk L)
    (hF : Fired L g Q d e (some u)) (hs : d.site = .allocWr) :
    ∃ col, col < 2 ^ 16 ∧ e = ⟨evPc d.site, .wr
      { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 col).toBytes⟩ := by
  simpa only [Shape, hs] using shape hb hS hF

theorem shape_ld0 (hS : ProA.SharedOk L) (hF : Fired L g Q d e (some u)) (hs : d.site = .ld0) :
    ∃ ac bs, e = ⟨evPc d.site, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ ac.size = 4 ∧ ac.elem = 0 := by
  obtain ⟨s, w⟩ := d
  obtain rfl : s = .ld0 := hs
  obtain ⟨t, ha, hi, ins, hc, hf⟩ := hF
  simpa only [Shape] using OrUb.of_some (shapeAt_ld0 (Q := Q) hS w ha hi hc hf) hf

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
