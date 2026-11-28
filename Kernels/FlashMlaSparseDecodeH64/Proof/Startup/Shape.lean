-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Seg
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.ElectFull
public import Lemmas.Flow.Step.GenericShared

@[expose] public section

/-! # The startup's events by state

The event a state of the startup fires is the event of its site (`Ev`, `shape`): the two
shuffles send, from every lane, the warpgroup index (`sh 0`) and the warp index as the code
computes it (`sh 1`); the elections, which only warp 0 reaches, elect among the full warp at
their pc; initialization `n` initializes the mbarrier `initFam n` of the thread's CTA with its
count; the fence is the mbarrier-initialization fence; the allocation requests 512 columns into
the shared word at `222752`, lane 0 stores the address there, and every lane reads it back; the
`trap` is undefined behaviour; the barrier is CTA barrier 0. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

/-- The shared word that receives the Tensor Memory address. -/
abbrev tmemWordLoc (L : Launch) (g : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + 222752⟩

/-- The event-shape table of the startup. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .sh 0 => ∃ r ok, e.kind = .shfl .idx (w32 (BitVec.ofNat 64 (tidOf L g / 128))) 0 31 r ok
  | .sh 1 => ∃ r ok, e.kind = .shfl .idx (w32 (shru (tw L g) 5)) 0 31 r ok
  | .elect _ => ∃ inst ld, e.pc = d.site.pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld
  | .init n => e.kind = .mbInit (mbarLoc L (g / L.block) (initFam n)) (initFam n).count
  | .fence => e.kind = .fenceMbarInit
  | .alloc => e.kind = .tc (.resource .one (some (tmemWordLoc L g)) (.alloc 512))
  | .allocSt => ∃ col, col < 2 ^ 16 ∧
      e.kind = .wr { loc := tmemWordLoc L g, size := 4 } (b32 col).toBytes
  | .ld => (∃ a bs, e.kind = .rd a bs ∧ a.loc = (⟨.shared, g / L.block,
      wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + 0)) 222752⟩ : Loc).at (4 * 0) ∧ a.size = 4) ∨
      ∃ f, e.kind = .ub f
  | .trap => e.kind = .ub .trap
  | .relinq => e.kind = .tc (.resource .one none .relinquish)
  | .bar => e.kind = .bar 0 none .sync
  | .enter _ => True

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- An election whose mask register holds the word `-1` elects among the full warp. -/
theorem elect_full {t : TState} {dst : Option Nat} {pr r : Nat} {ty : Option DType} {pc : Nat}
    {e : Event} {o : Option TState} (hr : t.regs r = some (w32 (i32 (-1))))
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.elect, ty, [dst, some pr], [], some (.reg r)⟩)) e o) :
    ∃ inst ld, e.pc = pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld :=
  fires_elect_full (by simp only [readBits, readReg, hr]; rfl) (by decide) hf

theorem shapeAt_elect (j : Fin 2) (x1 x2 : BitVec 64) :
    (code L g).ShapeAt (Ev L g) ⟨.elect j, x1, x2⟩ := by
  intro t ins e o hat _ hc hf
  simp only [Ev]
  fin_cases j
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_16)
    exact elect_full (holds_mem (atD_holds hat) (mem_factsFrom (by lit_mem))) hf
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_31)
    exact elect_full (holds_mem (atD_holds hat) (mem_factsFrom (by lit_mem))) hf

theorem shapeAt_fence (x1 x2 : BitVec 64) :
    (code L g).ShapeAt (Ev L g) ⟨.fence, x1, x2⟩ := by
  intro t ins e o _ _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_87)
  simp only [eventTmpl, tmaTmpl, widenMbarScope] at hf
  split_ifs at hf <;> (simp only [Fires] at hf; rw [hf.1]; rfl)

theorem shapeAt_trap (x1 x2 : BitVec 64) :
    (code L g).ShapeAt (Ev L g) ⟨.trap, x1, x2⟩ := by
  intro t ins e o _ _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_95)
  simp only [eventTmpl, Fires] at hf
  rw [hf.1]
  rfl

/-- The read-back at pc 92 is a weak load of the shared variable's word at byte 222752. -/
theorem ld_ins : ∃ a, kernel.code[92]? = some ⟨none, .mem a⟩ ∧ a.kind = .load ∧ a.nc = false ∧
    a.sem = .weak ∧ a.space = some (.shared .cta) ∧ a.addr.base = .sharedSym 0 ∧
    a.addr.off = 222752 ∧ a.elem.width = 32 ∧ a.rule = some .threadAccess ∧ a.locSpace? = none :=
  ⟨_, Flow.code_92, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩

theorem shapeAt_ld (x1 x2 : BitVec 64) :
    (code L g).ShapeAt (Ev L g) ⟨.ld, x1, x2⟩ := by
  intro t ins e o hat _ hc hf
  obtain ⟨a, hc92, hk, hnc, hs, hsp, hb, ho, hw, hr, hl⟩ := ld_ins
  obtain rfl := Option.some.inj (hc.symm.trans hc92)
  have h := fires_sym_rd_at (n := 4) hk hs hsp hb hnc (by rw [hw]) hat.2.1 hr hl hf
  rw [ho] at h
  exact h

/-- The address and count registers of initialization `n`. -/
def initRegs (n : Fin 23) : Nat × Nat :=
  [(527, 526), (529, 528), (530, 528), (531, 526), (532, 528), (533, 526), (534, 528),
    (535, 526), (536, 528), (537, 526), (538, 528), (539, 526), (540, 528), (541, 526),
    (542, 528), (544, 543), (546, 545), (547, 543), (548, 545), (549, 543), (550, 545),
    (551, 543), (552, 545)].getD n.val (0, 0)

theorem init_ins (n : Fin 23) :
    kernel.code[initPc n]? = some ⟨none, .mbarInit (initRegs n).1 0 (.reg (initRegs n).2)⟩ := by
  fin_cases n <;> simp only [initPc, initRegs, List.getD_cons_zero,
    List.getD_cons_succ] <;> code_lookup

theorem init_live (n : Fin 23) :
    (initRegs n).1 ∈ liveAt (initPc n) ∧ (initRegs n).2 ∈ liveAt (initPc n) := by
  fin_cases n <;> decide +kernel

theorem init_vals (x1 x2 : BitVec 64) (n : Fin 23) :
    valueOf L g ⟨.init n, x1, x2⟩ (initRegs n).1 = b32 (L.sharedBase + (initFam n).off) ∧
      valueOf L g ⟨.init n, x1, x2⟩ (initRegs n).2 = b32 (initFam n).count := by
  fin_cases n <;> exact ⟨rfl, rfl⟩

theorem shapeAt_init (hp : Pre P L m) (n : Fin 23) (x1 x2 : BitVec 64) :
    (code L g).ShapeAt (Ev L g) ⟨.init n, x1, x2⟩ := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (init_ins n))
  have hbase := sharedBase_lt hp
  have hal : L.sharedBase % 1024 = 0 := hp.sharedBase ▸ hp.sharedAlignment
  obtain ⟨hl1, hl2⟩ := init_live n
  obtain ⟨hv1, hv2⟩ := init_vals (L := L) (g := g) x1 x2 n
  have hr1 := holds_mem (atD_holds hat) (mem_factsFrom hl1)
  have hr2 := holds_mem (atD_holds hat) (mem_factsFrom hl2)
  rw [hv1] at hr1
  rw [hv2] at hr2
  obtain ⟨hlo, hhi, hmod⟩ := (initFam n).off_range
  have hc0 : 0 < (initFam n).count ∧ (initFam n).count < 2 ^ 20 := by
    generalize initFam n = f; cases f <;> simp only [MbarFam.count] <;> decide
  exact shape_mbInitR hf hr1 (by omega) hr2 hc0.1 hc0.2 (by omega) rfl

/-- **The allocation's two steps**: the request of 512 columns into the shared word at
`222752`, and lane 0's store of the address there. -/
theorem shapeAt_alloc (hp : Pre P L m) (st : Bool) (x1 x2 : BitVec 64) :
    (code L g).ShapeAt (Ev L g) ⟨if st then .allocSt else .alloc, x1, x2⟩ := by
  intro t ins e o hat _ hc hf
  have hc' : kernel.code[91]? = some ins := by cases st <;> exact hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_91)
  have hbase := sharedBase_lt hp
  have hal : L.sharedBase % 1024 = 0 := hp.sharedBase ▸ hp.sharedAlignment
  have hl1 : 554 ∈ liveAt 91 := by decide +kernel
  have hl2 : 555 ∈ liveAt 91 := by decide +kernel
  have hpc : (code L g).pc ⟨if st then .allocSt else .alloc, x1, x2⟩ = 91 := by cases st <;> rfl
  have hF : Holds t.regs (factsFrom (liveAt 91) (valueOf L g ⟨if st then .allocSt else .alloc,
      x1, x2⟩)) := by rw [← hpc]; exact (atD_holds hat)
  have hr1 : t.regs 554 = some (b32 (L.sharedBase + 222752)) := by
    have := holds_mem hF (mem_factsFrom hl1); cases st <;> exact this
  have hr2 : t.regs 555 = some (w32 (i32 512)) := by
    have := holds_mem hF (mem_factsFrom hl2); cases st <;> exact this
  have hn : readBits L g t 32 (.reg 555) = .ok (i32 512) := by
    simp only [readBits, readReg, hr2]; rfl
  cases st
  · exact shape_tcAlloc hf hat.2.1 hr1 hn (by rw [hp.block]) (by omega) (by omega) rfl rfl
  · exact shape_tcAllocWr hf hat.2.1 hr1 hn (by rw [hp.block]) (by omega) (by omega) rfl
      (fun col hcol => ⟨col, hcol, rfl⟩)

set_option hygiene false in
/-- The shape at a state of a site family, by `site_shape` (the other sites are skipped). -/
macro "st_shape" hp:term:max s:ident : tactic => `(tactic| (
  have hbase := sharedBase_lt $hp
  site_shape $s
    skip_by (simp at hs)
    unfolding [Ev, tmemWordLoc]
    reg_vals [valueOf, values, entryVal, entryVals, lookupLit, sb]
    addr_by (first | rw [($hp).block] | omega)))

theorem shapeAt_ctl (hp : Pre P L m) (d : D)
    (hs : (∃ j, d.site = .sh j) ∨ d.site = .relinq ∨ d.site = .bar) :
    (code L g).ShapeAt (Ev L g) d := by
  obtain ⟨s, x1, x2⟩ := d
  st_shape hp s

/-- **The event a state of the startup fires is the event of its site.** -/
theorem shape (hp : Pre P L m) : (code L g).Shape (Ev L g) := by
  refine Code.Shape.of_at fun d => ?_
  obtain ⟨s, x1, x2⟩ := d
  cases s with
  | sh j => exact shapeAt_ctl hp _ (.inl ⟨j, rfl⟩)
  | elect j => exact shapeAt_elect j x1 x2
  | init n => exact shapeAt_init hp n x1 x2
  | fence => exact shapeAt_fence x1 x2
  | alloc => exact shapeAt_alloc hp false x1 x2
  | allocSt => exact shapeAt_alloc hp true x1 x2
  | ld => exact shapeAt_ld x1 x2
  | trap => exact shapeAt_trap x1 x2
  | relinq => exact shapeAt_ctl hp _ (.inr (.inl rfl))
  | bar => exact shapeAt_ctl hp _ (.inr (.inr rfl))
  | enter r => exact fun _ _ _ _ => trivial

end
/-- **A startup event is no wait and no exit**, and at the barrier site it is `bar.sync 0`. -/
theorem ev_quiet {d : D} {e : Event} (hev : Ev L g d e) (hx : exitOf d = none) :
    (∀ l q ok b sc, e.kind ≠ .wait l q ok b sc) ∧ e.kind ≠ .exit ∧
      (d.site = .bar → e.kind = .bar 0 none .sync) := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> simp [hk]
  | elect j => obtain ⟨inst, ld, -, hk⟩ := hev; simp [hk]
  | allocSt => obtain ⟨col, -, hk⟩ := hev; simp [hk]
  | ld => rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> simp [hk]
  | enter r => simp [exitOf] at hx
  | init n => simp only [Ev] at hev; simp [hev]
  | fence => simp only [Ev] at hev; simp [hev]
  | alloc => simp only [Ev] at hev; simp [hev]
  | trap => simp only [Ev] at hev; simp [hev]
  | relinq => simp only [Ev] at hev; simp [hev]
  | bar => simp only [Ev] at hev; simp [hev]

/-- **The startup's collectives**: no startup event is a vote, and a shuffle is fired at a
shuffle site. -/
theorem ev_coll {d : D} {e : Event} (hev : Ev L g d e) (hx : exitOf d = none) :
    voteClass e.kind = none ∧
      ∀ md a b c r ok, e.kind = .shfl md a b c r ok → ∃ j, d.site = .sh j := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> simp [hk, voteClass]
  | elect j => obtain ⟨inst, ld, -, hk⟩ := hev; simp [hk, voteClass]
  | allocSt => obtain ⟨col, -, hk⟩ := hev; simp [hk, voteClass]
  | ld => rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> simp [hk, voteClass]
  | enter r => simp [exitOf] at hx
  | init n => simp only [Ev] at hev; simp [hev, voteClass]
  | fence => simp only [Ev] at hev; simp [hev, voteClass]
  | alloc => simp only [Ev] at hev; simp [hev, voteClass]
  | trap => simp only [Ev] at hev; simp [hev, voteClass]
  | relinq => simp only [Ev] at hev; simp [hev, voteClass]
  | bar => simp only [Ev] at hev; simp [hev, voteClass]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
