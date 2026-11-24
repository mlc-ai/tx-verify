-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.FloatRead
import Lemmas.Flow.LoadShared
import Lemmas.Flow.Scalars

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

private theorem lse_sub_zero {d : D} (hi : Inv P L g d) (hs : d.site.elems = 1) :
    d.sub = 0 := by
  have h := hi.subLt
  omega

private theorem lse_bar_regs {d : D} {t : TState} (ha : (code P L g).AtD d t)
    (hd : d.site = .lseBar ∨ d.site = .lseBar2) :
    t.regs 1725 = some (b32 9) ∧ t.regs 1726 = some (b32 128) := by
  constructor
  · exact reg_value ha (by rcases hd with h | h <;> rw [h] <;> decide +kernel)
  · exact reg_value ha (by rcases hd with h | h <;> rw [h] <;> decide +kernel)

/-- Both row-sum barriers use the same 128-thread named barrier. -/
private theorem event_lseBar (hpre : Pre P L mem0) {d : D} {t : TState}
    (ha : (code P L g).AtD d t) (hd : d.site = .lseBar ∨ d.site = .lseBar2) :
    eventTmpl asms L g t (.barSyncN (.reg 1725) (.reg 1726) true) =
      .bar 9 (PTX.next t) (some 128) .sync := by
  obtain ⟨hr, hs⟩ := lse_bar_regs ha hd
  have h9 := readBits_b32 (L := L) (g := g) hr (by decide : 9 < 2 ^ 32)
  have h128 := readBits_b32 (L := L) (g := g) hs (by decide : 128 < 2 ^ 32)
  simp [eventTmpl, barTmpl, h9, h128, hpre.block]

/-- The first row-sum barrier protects the handoff from maxima to half-sums in shared memory. -/
theorem step_lseBar (hpre : Pre P L mem0) (d : D) (hd : d.site = .lseBar) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    have hsite : d.site.pc = 1154 := by rw [hd]; rfl
    have hsub := lse_sub_zero hi (by rw [hd]; rfl)
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1154)
    rw [event_lseBar hpre ha (Or.inl hd)] at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := {d with site := .lseStore0}
    have hn : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, d']
    have ht := at_next_of ha hsite hsub
    have hkeep : (Flow.live 1155).filter tracked.contains ⊆
        (Flow.live 1154).filter tracked.contains := by decide +kernel
    refine Or.inl (Or.inr ⟨d', PTX.next t, hn, .refl,
      ⟨ht.1, ht.2.1.trans hsub.symm, ht.2.2.1, ht.2.2.2.1,
        holds_factsFrom_mono ht.2.2.2.2 hkeep⟩, ?_⟩)
    have hi' := inv_setSite hi .lseStore0 (fun _ => hi.epilogueLast (by rw [hd]; rfl))
      (by simp [Site.inRescale]) (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
    simpa [code, d', hsub] using hi'

/-- The aligned half-sum store can only write its shared row slot. -/
theorem fired_lseStore0 (hpre : Pre P L mem0)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .lseStore0) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a, e.kind = .wr a ((if d.peak = ⊥ then b32 0 else halfSumVal d).toBytes) ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)) ∧ a.size = 4 ∧
      o = some (PTX.next t) := by
  have hsite : d.site.pc = 1155 := by rw [hd]; rfl
  have hsub := ha.2.1.trans (lse_sub_zero hi (by rw [hd]; rfl))
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1155)
  let base := L.sharedBase + 4 * (tidOf L g % 128)
  let a : Loc := ⟨.shared, g / L.block, base + 221184⟩
  let v : Value := if d.peak = ⊥ then b32 0 else halfSumVal d
  have hr : t.regs 471 = some (b32 base) :=
    reg_value ha (by rw [hd]; decide +kernel)
  have hv : t.regs 1727 = some v := reg_value ha (by rw [hd]; decide +kernel)
  have hbase := sharedBase_lt hpre
  have hb : base + 221184 < 2 ^ 32 := by dsimp [base]; omega
  have hal : a.addr % 4 = 0 := by
    have hh := sharedBase_mod8 hpre
    change (L.sharedBase + 4 * (tidOf L g % 128) + 221184) % 4 = 0
    omega
  have hsz : v.bytes = 4 := by
    dsimp [v]
    split
    · rfl
    · unfold halfSumVal
      split <;> rfl
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := 471) (w := 32) (by rfl) rfl rfl
    rfl (by simp)] at hf
  have haddr := effAddr_b32_off (L := L) (g := g) (off := 221184) hr hb
  change effAddr L g t .shared 471 221184 = .ok a at haddr
  have hstore := storeValue_of_bytes (w := 32) hsz
  simp [DType.width, storeTmpl, haddr, elemAcc, hsub, hal, hv, hstore, readValue, readReg,
    afterStore, bind, Except.bind, pure, Except.pure, Loc.at, Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  refine ⟨_, rfl, ?_, rfl, ?_⟩
  · simp [a, base, shLoc, ctaOf, rowMaxBase, Nat.add_comm, Nat.add_left_comm]
  · simpa [PTX.next, hsub] using hu

/-- The 32-bit half-sum store writes one word at this thread's slot in the shared row array. -/
theorem fires_lseStore0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .lseStore0) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a, e.kind = .wr a ((if d.peak = ⊥ then b32 0 else halfSumVal d).toBytes) ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)) ∧ a.size = 4 ∧
      u = PTX.next t := by
  obtain ⟨a, he, hl, hs, hu⟩ := fired_lseStore0 hpre hd ha hi hc hf
  exact ⟨a, he, hl, hs, Option.some.inj hu⟩

/-- After writing its half-sum, each lane reaches the second row-sum barrier. -/
theorem step_lseStore0 (hpre : Pre P L mem0) (d : D) (hd : d.site = .lseStore0) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨a, he, hl, hs, rfl⟩ := fires_lseStore0 hpre hd ha hi hc hf
    have hsite : d.site.pc = 1155 := by rw [hd]; rfl
    have hsub := lse_sub_zero hi (by rw [hd]; rfl)
    let d' : D := {d with site := .lseBar2, sub := 0}
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, writeStep, hd, he, hl, hs, siteLoc, Site.elemBytes, Site.elems,
        hsub, d']
    have ht := at_next_of ha hsite hsub
    have hkeep : (Flow.live 1156).filter tracked.contains ⊆
        (Flow.live 1155).filter tracked.contains := by decide +kernel
    refine Or.inl (Or.inr ⟨d', PTX.next t, hn, .refl,
      ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, holds_factsFrom_mono ht.2.2.2.2 hkeep⟩, ?_⟩)
    exact inv_setSite hi .lseBar2 (fun _ => hi.epilogueLast (by rw [hd]; rfl))
      (by simp [Site.inRescale]) (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)

/-- The second row-sum barrier makes the other half's sum visible before the load. -/
theorem step_lseBar2 (hpre : Pre P L mem0) (d : D) (hd : d.site = .lseBar2) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    have hsite : d.site.pc = 1156 := by rw [hd]; rfl
    have hsub := lse_sub_zero hi (by rw [hd]; rfl)
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1156)
    rw [event_lseBar hpre ha (Or.inr hd)] at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := {d with site := .lseRead}
    have hn : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, d']
    have ht := at_next_of ha hsite hsub
    have hkeep : (Flow.live 1157).filter tracked.contains ⊆
        (Flow.live 1156).filter tracked.contains := by decide +kernel
    refine Or.inl (Or.inr ⟨d', PTX.next t, hn, .refl,
      ⟨ht.1, ht.2.1.trans hsub.symm, ht.2.2.1, ht.2.2.2.1,
        holds_factsFrom_mono ht.2.2.2.2 hkeep⟩, ?_⟩)
    have hi' := inv_setSite hi .lseRead (fun _ => hi.epilogueLast (by rw [hd]; rfl))
      (by simp [Site.inRescale]) (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
    simpa [code, d', hsub] using hi'

/-- A shared scalar word address preserves the XOR of bit six in the thread index. -/
private theorem lse_peer_word_offset (n : Nat) : (4 * n) ^^^ 256 = 4 * (n ^^^ 64) := by
  have h := Nat.shiftLeft_xor_distrib (a := n) (b := 64) (i := 2)
  simpa [Nat.shiftLeft_eq, Nat.mul_comm _ 4] using h.symm

/-- The half-sum read can only read the paired lane's shared slot. -/
theorem fired_lseRead (hpre : Pre P L mem0)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .lseRead) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)) ∧ a.size = 4 ∧
      bs.length = 4 ∧ o = some (afterLoad t [1728] bs) := by
  have hsite : d.site.pc = 1157 := by rw [hd]; rfl
  have hsub := ha.2.1.trans (lse_sub_zero hi (by rw [hd]; rfl))
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1157)
  let j := tidOf L g % 128 ^^^ 64
  let base := L.sharedBase + 4 * j
  let a : Loc := ⟨.shared, g / L.block, base + 221184⟩
  have hr : t.regs 472 = some (b32 base) := by
    have hh : t.regs 472 = some (b32 (L.sharedBase + (4 * (tidOf L g % 128) ^^^ 256))) :=
      reg_value ha (by rw [hd]; decide +kernel)
    simpa only [base, j, lse_peer_word_offset] using hh
  have hj : j < 128 := Nat.xor_lt_two_pow (n := 7) (Nat.mod_lt _ (by decide)) (by decide)
  have hb : base + 221184 < 2 ^ 32 := by
    have hh := sharedBase_lt hpre
    dsimp [base]
    omega
  have hal : a.addr % 4 = 0 := by
    have hh := sharedBase_mod8 hpre
    change (L.sharedBase + 4 * j + 221184) % 4 = 0
    omega
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 472) (w := 32) (by rfl) rfl rfl
    rfl rfl] at hf
  have haddr := effAddr_b32_off (L := L) (g := g) (off := 221184) hr hb
  change effAddr L g t .shared 472 221184 = .ok a at haddr
  simp [MemAccess.regs, DType.width, loadTmpl, haddr, elemAcc, hsub, hal, bind,
    Except.bind, pure, Except.pure, Loc.at, Fires] at hf
  obtain ⟨bs, hsize, rfl, hu⟩ := hf
  refine ⟨_, bs, rfl, ?_, rfl, hsize, hu⟩
  simp [a, base, j, shLoc, ctaOf, rowMaxBase, Nat.add_comm, Nat.add_left_comm]

/-- The row-sum load addresses the other half's word and captures the actual bytes it returns. -/
theorem fires_lseRead (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .lseRead) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a bs, e.kind = .rd a bs ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)) ∧ a.size = 4 ∧
      bs.length = 4 ∧ u = afterLoad t [1728] bs := by
  obtain ⟨a, bs, he, hl, hs, hn, hu⟩ := fired_lseRead hpre hd ha hi hc hf
  exact ⟨a, bs, he, hl, hs, hn, Option.some.inj hu⟩

private def lseLive : List Nat := (Flow.live 1157).filter tracked.contains

private def lseOwnWord (d : D) : Value := if d.peak = ⊥ then b32 0 else halfSumVal d

private theorem lseOwnWord_real (d : D) :
    valFloat .f32 (lseOwnWord d) = .ok (lseOwnSum d) := by
  by_cases hp : d.peak = ⊥ <;> cases hm : d.sumUpd <;>
    simp [lseOwnWord, lseOwnSum, halfSumVal, hp, hm, valFloat_z0, valFloat_float, fl]

private theorem lse_afterLoad {d : D} {t : TState} {bs : List (Option Byte)} {v : Value}
    (hd : d.site = .lseRead) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hv : rebuild 3 bs = .ok v) :
    At (afterLoad t [1728] bs) 1158 ((1728, v) :: factsFrom lseLive (valueOf P L g d)) := by
  have hsite : d.site.pc = 1157 := by rw [hd]; rfl
  have hsub := lse_sub_zero hi (by rw [hd]; rfl)
  have hnext := at_next_of ha hsite hsub
  have hat : At t 1157 (factsFrom lseLive (valueOf P L g d)) :=
    ⟨ha.1.trans hsite, hnext.2.1, hnext.2.2.1, hnext.2.2.2.1, hnext.2.2.2.2⟩
  have hh : afterLoad t [1728] bs = PTX.next (setReg t 1728 v) := by
    simp [afterLoad, hv, hat.2.1, hat.2.2.1, setRegs, PTX.next, setReg]
  rw [hh]
  exact hat.set (not_mem_factsFrom (by decide +kernel))

private theorem read_lse_real {t : TState} {r : Nat} {v : Value} {x : ℝ}
    (hr : t.regs r = some v) (hx : valFloat .f32 v = .ok x) :
    Assumption.readERealOpnd t .f32 (.reg r) = some (.ok (x : EReal)) :=
  (readERealOpnd_reg hr).trans (readEReal_of_valFloat hx)

private theorem run_lse_add (d : D) {t : TState} {v : Value} {peer : ℝ}
    (hv : valFloat .f32 v = .ok peer)
    (ha : At t 1158 ((1728, v) :: factsFrom lseLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u 1159 ((482, fl (lseOwnSum d + peer)) :: factsFrom lseLive (valueOf P L g d)) := by
  let op : Op := .float {
    op := .add, ty := ⟨.f32, 1⟩, ftz := true, dsts := [some 482],
    srcs := [.reg 1727, .reg 1728] }
  have hc : kernel.code[1158]? = some ⟨none, op⟩ := Flow.code_1158
  have hown : t.regs 1727 = some (lseOwnWord d) :=
    holds_mem ha.2.2.2.2.2 (mem_factsFrom (r := 1727) (by decide +kernel))
  have hA := read_lse_real hown (lseOwnWord_real d)
  have hB := read_lse_real ha.2.2.2.2.1 hv
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 482 (fl (lseOwnSum d + peer)))) := by
    apply Assumption.execLocalA_idealReal
      (f := .add .f32) rfl (by decide)
      (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
        (List.mem_cons_of_mem _ ha))
    change Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 1727)) (fun x =>
      Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 1728)) fun y =>
        (Assumption.addEReal x y).map (fun r =>
          .ok (PTX.next (setReg t 482 (Assumption.erealValue .f32 r))))) = _
    rw [hA, hB]
    have hsum : Assumption.addEReal (lseOwnSum d : EReal) (peer : EReal) =
        some ((lseOwnSum d + peer : ℝ) : EReal) := by
      simp [Assumption.addEReal]
    have hval : Assumption.erealValue .f32 ((lseOwnSum d + peer : ℝ) : EReal) =
        fl (lseOwnSum d + peer) := by
      unfold Assumption.erealValue
      rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe]
      rfl
    simp only [Assumption.bindRead, hsum, Option.map_some, hval]
  have hat := ha.mono ha.2.2.2.2.2
  exact ⟨_, run_local hc rfl ha he, hat.set (not_mem_factsFrom (by decide +kernel))⟩

private theorem run_lse_param (hpre : Pre P L mem0) {pc off w dst : Nat} {t : TState}
    {F : List (Nat × Value)} (ha : At t pc F) (hnew : ∀ q ∈ F, q.1 ≠ dst)
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad (.int .b w) off 2991 dst)⟩)
    (hptr : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0))
    (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsize : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (hNoAdd : pc ∉ paramAdds) (hNoPrefetch : pc ∉ prefetchTensorMapSites)
    (hrule : (Thread.paramLoad (.int .b w) off 2991 dst).rule = some .threadMove) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (pc + 1) ((dst, paramElem w w (paramNat L (param "0") off (w / 8))) :: F) := by
  have hl : ∀ a ∈ asms,
      a.localRule L g t (.mem (Thread.paramLoad (.int .b w) off 2991 dst)) = none := by
    exact Thread.asms_localRule_mem (t := t) (by rw [ha.1]; exact hNoAdd)
      (by rw [ha.1]; exact hNoPrefetch)
  have hsf : Assumption.SegFreePc asms t.pc := fun a ha l i state _ =>
    asms_segment_free (L := l) (g := i) state a ha
  refine ⟨_, ?_, ha.set hnew⟩
  exact run_local hc rfl ha
    (Thread.exec_ldParamReg (A := asms) (L := L) (g := g)
      (w := w) (off := off) (r := 2991) (d := dst) (t := t) (p := param "0") (ty := .int .b w)
      (decl := scalarsParam) (base := P.param0Base) hptr hpre.param0Object
      ⟨by omega, hsize⟩ hal hsup hsf hl rfl hrule)

private theorem run_lse_test (hpre : Pre P L mem0) (d : D) {t : TState}
    (ha : At t 1159 ((482, fl d.li) :: factsFrom lseLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 3 t = some u ∧
      At u (if tidOf L g % 128 < 64 then 1162 else 1179)
        ((482, fl d.li) :: factsFrom lseLive (valueOf P L g d)) := by
  have hptr : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) :=
    holds_mem ha.2.2.2.2.2 (mem_factsFrom (r := 2991) (by decide +kernel))
  have hnot : ∀ p ∈ (482, fl d.li) :: factsFrom lseLive (valueOf P L g d), p.1 ≠ 1729 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · change (482 : Nat) ≠ 1729
      decide
    · exact not_mem_factsFrom (by decide +kernel) p hp
  obtain ⟨t₁, hr₁, ha₁⟩ := run_lse_param (dst := 1729) hpre ha hnot Flow.code_1159
    hptr (supplied_int hpre.paramHq (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  have hparam : paramElem 32 32 (paramNat L (param "0") 8 4) = b32 64 := by
    change b32 (paramWord L 8 4) = b32 64
    rw [paramWord_8 hpre]
  rw [hparam] at ha₁
  obtain ⟨t₂, hr₂, ha₂⟩ : ∃ u, run kernel asms L g 1 t₁ = some u ∧
      At u 1161 ((118, .pred (decide (64 ≤ tidOf L g % 128))) ::
        (482, fl d.li) :: factsFrom lseLive (valueOf P L g d)) := by
    simp only [lseLive] at ha₁ ⊢
    seg_fp ha₁ using norm_signed []
  obtain ⟨v, hr₃, hav⟩ := run_bra Flow.code_1161 _ ha₂ ha₂.2.2.2.2.1
    (Thread.asms_localRule_bra (by rw [ha₂.1]; decide) (by rw [ha₂.1]; decide))
  refine ⟨v, run_comp (run_comp hr₁ hr₂) hr₃, ?_⟩
  by_cases hfirst : tidOf L g % 128 < 64
  · have hge : ¬64 ≤ tidOf L g % 128 := by omega
    simpa [hfirst, hge] using hav.mono hav.2.2.2.2.2
  · have hge : 64 ≤ tidOf L g % 128 := by omega
    simpa [hfirst, hge] using hav.mono hav.2.2.2.2.2

private theorem lse_addr_lt (hpre : Pre P L mem0)
    (hb : eOf L g < P.b) (hq : qOf L g < P.s_q) :
    (lseLocOf P L g).addr < 2 ^ 64 := by
  have hrow : eOf L g * P.s_q + qOf L g < P.b * P.s_q := calc
    _ < eOf L g * P.s_q + P.s_q := Nat.add_lt_add_left hq _
    _ = (eOf L g + 1) * P.s_q := by simp [Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hb
  have hh := head_lt L g
  change P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + head L g) < 2 ^ 64
  have hR' := hpre.tensorRange.2.2
  rw [lseBytes, show 4 * P.b * P.s_q * 64 = 4 * ((P.b * P.s_q) * 64) by ac_rfl] at hR'
  omega

/-- The final LSE store can only emit its aligned global write. -/
theorem fired_lseStore (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .lseStore) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a, e.kind = .wr a (lseReg d).toBytes ∧ a.loc = lseLocOf P L g ∧ a.size = 4 ∧
      o = some (PTX.next t) := by
  have hsite : d.site.pc = 1178 := by rw [hd]; rfl
  have hsub := ha.2.1.trans (lse_sub_zero hi (by rw [hd]; rfl))
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1178)
  let a := lseLocOf P L g
  have hr : t.regs 3574 = some (b64 a.addr) := reg_value ha (by rw [hd]; decide +kernel)
  have hv : t.regs 1733 = some (lseReg d) := reg_value ha (by rw [hd]; decide +kernel)
  have haddr : effAddr L g t .global 3574 0 = .ok a :=
    effAddr_global hr (lse_addr_lt hpre hb hq)
  have hal : a.addr % 4 = 0 := by
    have hh := hpre.lseAlign
    change (P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + head L g)) % 4 = 0
    omega
  have hsz : (lseReg d).bytes = 4 := by
    unfold lseReg
    split <;> rfl
  rw [eventTmpl, memTmpl_store (sp := .global) (base := 3574) (w := 64) (by rfl) rfl rfl
    rfl (by simp)] at hf
  have hstore := storeValue_of_bytes (w := 32) hsz
  simp [DType.width, storeTmpl, haddr, elemAcc, hsub, hal, hv, hstore, readValue, readReg,
    afterStore, bind, Except.bind, pure, Except.pure, Loc.at, Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  exact ⟨_, rfl, rfl, rfl, by simpa [PTX.next, hsub] using hu⟩

/-- The global LSE write stores the four bytes of the role's selected LSE value. -/
theorem fires_lseStore (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .lseStore) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a, e.kind = .wr a (lseReg d).toBytes ∧ a.loc = lseLocOf P L g ∧ a.size = 4 ∧
      u = PTX.next t := by
  obtain ⟨a, he, hl, hs, hu⟩ := fired_lseStore hpre hb hq hd ha hi hc hf
  exact ⟨a, he, hl, hs, Option.some.inj hu⟩

private def lseWaitLive : List Nat := (Flow.live 1179).filter tracked.contains

/-- Both warp halves compute the address of the same last-slot PV completion poll. -/
private theorem run_lse_wait_addr (hpre : Pre P L mem0) (d : D) {t : TState}
    (ha : At t 1179 (factsFrom lseWaitLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 5 t = some u ∧
      At u 1184 (facts P L g {d with site := .svDone}) := by
  have hbase := sharedBase_lt hpre
  have hslot : d.block % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [lseWaitLive] at ha
  change ∃ u, run kernel asms L g 5 t = some u ∧ At u 1184
    (factsFrom ((Flow.live 1184).filter tracked.contains) (valueOf P L g d))
  seg_fp ha using
    (change _ = sb L (222936 + 8 * (d.block % 2)))
    (norm_bits [sb])

/-- After the global store, the writing half joins its peer at the last PV completion poll. -/
theorem step_lseStore (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (d : D) (hd : d.site = .lseStore) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨a, he, hl, hs, rfl⟩ := fires_lseStore hpre hb hq hd ha hi hc hf
    have hsite : d.site.pc = 1178 := by rw [hd]; rfl
    have hsub := lse_sub_zero hi (by rw [hd]; rfl)
    have hkeep : lseWaitLive ⊆ (Flow.live 1178).filter tracked.contains := by decide +kernel
    have ha₁ := at_next_of ha hsite hsub
    obtain ⟨v, hr, hav⟩ := run_lse_wait_addr hpre d (ha₁.mono
      (holds_factsFrom_mono ha₁.2.2.2.2 hkeep))
    let d' : D := {d with site := .svDone, sub := 0}
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, he, hl, hs, d']
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr,
      ⟨hav.1, hav.2.1, hav.2.2.1, hav.2.2.2.1, hav.2.2.2.2⟩, ?_⟩)
    exact inv_setSite hi .svDone (fun _ => hi.epilogueLast (by rw [hd]; rfl))
      (by simp [Site.inRescale]) (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
      (fun _ => hi.rowTotal (by rw [hd]; rfl))

private theorem lse_read_frame (d : D) (s : Site) (x y : ℝ) :
    factsFrom lseLive (valueOf P L g { d with site := s, sub := 0, li := x, lp := y }) =
      factsFrom lseLive (valueOf P L g d) := by
  have hLive : lseLive =
      [459, 460, 463, 465, 469, 472, 481, 1727, 2880, 2953, 2954, 2991, 2992,
        2993, 2994, 2995, 2996, 2997, 2998, 2999, 3001] := by decide +kernel
  unfold factsFrom
  apply List.map_congr_left
  intro r hr
  rw [hLive] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Decode the shared half-sum and prove which half reaches the global LSE calculation. -/
private theorem lseRead_branch (hpre : Pre P L mem0) (d : D) (hd : d.site = .lseRead)
    {t u : TState} {e : Event} {ins : Instr}
    (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    next P L g d e = some none ∨
      ∃ d' v, next P L g d e = some (some d') ∧ Inv P L g d' ∧
        d'.site = (if tidOf L g % 128 < 64 then .lseStore else .svDone) ∧ d'.sub = 0 ∧
        run kernel asms L g 4 u = some v ∧
        At v (if tidOf L g % 128 < 64 then 1162 else 1179)
          ((482, fl d'.li) :: factsFrom lseLive (valueOf P L g d')) := by
  obtain ⟨a, bs, he, hl, hs, _, rfl⟩ := fires_lseRead hpre hd ha hi hc hf
  cases hb : rebuild 3 bs with
  | error err =>
    exact Or.inl (by simp [next, nextSite, hd, he, hl, hs, siteLoc, Site.elemBytes, hb,
      Except.toOption])
  | ok x =>
    cases hval : valFloat .f32 x with
    | error err =>
      exact Or.inl (by simp [next, nextSite, hd, he, hl, hs, siteLoc, Site.elemBytes, hb, hval,
        Except.toOption])
    | ok peer =>
      let row : D := {d with li := lseOwnSum d + peer, lp := peer}
      let nextSite := if tidOf L g % 128 < 64 then Site.lseStore else Site.svDone
      let d' : D := {row with site := nextSite, sub := 0}
      have hn : next P L g d e = (if RowTotal d' then some (some d') else some none) := by
        simp [next, Wg0.nextSite, hd, he, hl, hs, siteLoc, Site.elemBytes, hb, hval,
          Except.toOption, d', row, nextSite]
      by_cases hrow : RowTotal d'
      · have hirow : Inv P L g row := {hi with rowTotal := fun _ => hrow}
        have hi' : Inv P L g d' := by
          refine inv_setSite hirow nextSite (fun _ => hi.epilogueLast (by rw [hd]; rfl))
            ?_ ?_ ?_ ?_ (fun _ => hrow) ?_
          all_goals by_cases ht : tidOf L g % 128 < 64 <;>
            simp [nextSite, ht, Site.inRescale]
        have hstart := lse_afterLoad hd ha hi hb
        obtain ⟨u₁, hr₁, ha₁⟩ := run_lse_add d hval hstart
        have ha₁' : At u₁ 1159
            ((482, fl d'.li) :: factsFrom lseLive (valueOf P L g d')) := by
          rw [show factsFrom lseLive (valueOf P L g d') =
              factsFrom lseLive (valueOf P L g d) from lse_read_frame d _ _ _]
          exact ha₁
        obtain ⟨v, hr₂, hav⟩ := run_lse_test hpre d' ha₁'
        exact Or.inr ⟨d', v, by simpa only [hrow, ite_true] using hn,
          hi', rfl, rfl, run_comp hr₁ hr₂, hav⟩
      · exact Or.inl (by simpa only [hrow, ite_false] using hn)

private def lseAddrLive : List Nat := (Flow.live 1162).filter tracked.contains

private def lseAddrFacts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (1733, lseReg d) :: factsFrom lseAddrLive (valueOf P L g d)

private theorem lse_addr_ptr {d : D} {t : TState} {pc : Nat} {R : List (Nat × Value)}
    (ha : At t pc (R ++ lseAddrFacts P L g d)) :
    t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
  have hr := (holds_append t.regs R (lseAddrFacts P L g d)).mp ha.2.2.2.2
  exact holds_mem hr.2.2 (mem_factsFrom (r := 2991) (by decide +kernel))

private theorem signed_lse_operand {a : Nat} (ha : a < 2 ^ 31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) = (a : Int) := by
  have h32 : a < 2 ^ 32 := by omega
  have h64 : a < 2 ^ 64 := by omega
  rw [truncBits_ofNat h32 (by decide)]
  rw [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32]
  change (if a < 2 ^ 31 then (a : Int) else (a : Int) - 2 ^ 32) = (a : Int)
  rw [ite_eq_left ha]

private theorem run_lse_addr (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hf : tidOf L g % 128 < 64) (d : D) {t : TState}
    (ha : At t 1167 (lseAddrFacts P L g d)) :
    ∃ u, run kernel asms L g 11 t = some u ∧
      At u 1178 (facts P L g {d with site := .lseStore}) := by
  have hidx : head L g = tidOf L g % 128 := by
    rw [head_tid, Nat.mod_eq_of_lt hf]
  have hsum : eOf L g * (P.s_q * 64) + tidOf L g % 128 + qOf L g * 64 =
      (eOf L g * P.s_q + qOf L g) * 64 + head L g := by
    simp only [← Nat.mul_assoc, Nat.add_mul, hidx, Nat.add_right_comm]
  have hfull := lse_addr_lt hpre hb hq
  change P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + head L g) < 2 ^ 64 at hfull
  have haddr : P.lseBase + 4 * (eOf L g * (P.s_q * 64) + tidOf L g % 128 + qOf L g * 64)
      < 2 ^ 64 := hsum.symm ▸ hfull
  have hbase : P.lseBase < 2 ^ 64 := by omega
  have hs : P.s_q * 64 < 2 ^ 31 := by
    have hh := hpre.qoBatchStrideRange
    omega
  have he : eOf L g < 2 ^ 31 := lt_trans hb hpre.bLt
  have hq31 : qOf L g < 2 ^ 31 := lt_trans hq hpre.sqLt
  have hewide : eOf L g * (P.s_q * 64) < 2 ^ 64 := by omega
  have hqwide : qOf L g * 64 < 2 ^ 64 := by omega
  have hp96 : paramElem 64 64 (paramNat L (param "0") 96 8) = b64 P.lseBase := by
    change b64 (Thread.paramWord L 96 8) = b64 P.lseBase
    rw [Thread.paramWord_eight (fun i hi => hpre.paramLse i hi), Nat.mod_eq_of_lt hbase]
  have hp180 : paramElem 32 32 (paramNat L (param "0") 180 4) = b32 (P.s_q * 64) := by
    change b32 (Thread.paramWord L 180 4) = b32 (P.s_q * 64)
    rw [Thread.paramWord_four (fun i hi => hpre.paramStrideLseB i hi),
      Nat.mod_eq_of_lt (by omega : P.s_q * 64 < 2 ^ 32)]
  have hp184 : paramElem 32 32 (paramNat L (param "0") 184 4) = b32 64 := by
    change b32 (Thread.paramWord L 184 4) = b32 64
    rw [Thread.paramWord_four (fun i hi => hpre.paramStrideLseSq i hi)]
    rfl
  have hnot96 : ∀ p ∈ lseAddrFacts P L g d, p.1 ≠ 3566 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · change (1733 : Nat) ≠ 3566
      decide
    · exact not_mem_factsFrom (by decide +kernel) p hp
  obtain ⟨t₁, hr₁, ha₁⟩ := run_lse_param (dst := 3566) hpre ha hnot96 Flow.code_1167
    (lse_addr_ptr (R := []) ha) (supplied_ptr hpre.paramLse (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  rw [hp96] at ha₁
  obtain ⟨t₂, hr₂, ha₂⟩ : ∃ u, run kernel asms L g 1 t₁ = some u ∧
      At u 1169 ((3567, b64 P.lseBase) :: lseAddrFacts P L g d) := by
    simp only [lseAddrFacts, lseAddrLive] at ha₁ ⊢
    seg_fp ha₁ using norm_bits []
  have hnot180 : ∀ p ∈ (3567, b64 P.lseBase) :: lseAddrFacts P L g d, p.1 ≠ 1734 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · change (3567 : Nat) ≠ 1734
      decide
    rcases List.mem_cons.mp hp with rfl | hp
    · change (1733 : Nat) ≠ 1734
      decide
    exact not_mem_factsFrom (by decide +kernel) p hp
  obtain ⟨t₃, hr₃, ha₃⟩ := run_lse_param (dst := 1734) hpre ha₂ hnot180 Flow.code_1169
    (lse_addr_ptr (R := [(3567, b64 P.lseBase)]) ha₂)
    (supplied_int hpre.paramStrideLseB (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  rw [hp180] at ha₃
  obtain ⟨t₄, hr₄, ha₄⟩ : ∃ u, run kernel asms L g 1 t₃ = some u ∧
      At u 1171 ((3568, b64 (eOf L g * (P.s_q * 64))) :: (3567, b64 P.lseBase) ::
        lseAddrFacts P L g d) := by
    simp only [lseAddrFacts, lseAddrLive] at ha₃ ⊢
    seg_fp ha₃ using
      (change Value.bits 64 (truncBits 64 (BitVec.ofInt 64
        (toSigned 32 (truncBits 32 (BitVec.ofNat 64 (P.s_q * 64))) *
          toSigned 32 (truncBits 32 (BitVec.ofNat 64 (eOf L g)))))) =
        b64 (eOf L g * (P.s_q * 64)))
      (rw [signed_lse_operand hs, signed_lse_operand he, ← Int.natCast_mul, BitVec.ofInt_natCast,
        Nat.mul_comm (P.s_q * 64) (eOf L g), truncBits_ofNat hewide (by decide)]; rfl)
  have hnot184 : ∀ p ∈ (3568, b64 (eOf L g * (P.s_q * 64))) :: (3567, b64 P.lseBase) ::
      lseAddrFacts P L g d, p.1 ≠ 1735 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · change (3568 : Nat) ≠ 1735
      decide
    rcases List.mem_cons.mp hp with rfl | hp
    · change (3567 : Nat) ≠ 1735
      decide
    rcases List.mem_cons.mp hp with rfl | hp
    · change (1733 : Nat) ≠ 1735
      decide
    exact not_mem_factsFrom (by decide +kernel) p hp
  obtain ⟨t₅, hr₅, ha₅⟩ := run_lse_param (dst := 1735) hpre ha₄ hnot184 Flow.code_1171
    (lse_addr_ptr (R := [(3568, b64 (eOf L g * (P.s_q * 64))), (3567, b64 P.lseBase)]) ha₄)
    (supplied_int hpre.paramStrideLseSq (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  rw [hp184] at ha₅
  obtain ⟨v, hr₆, hav⟩ : ∃ u, run kernel asms L g 6 t₅ = some u ∧
      At u 1178 (factsFrom ((Flow.live 1178).filter tracked.contains) (valueOf P L g d)) := by
    simp only [lseAddrFacts, lseAddrLive] at ha₅
    seg_fp ha₅ using
      (change _ = b64 (P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + head L g)))
      (rw [← hsum])
      (norm_signed [])
  exact ⟨v, run_comp (run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅) hr₆, hav⟩

private def lseScalar (d : D) (x : ℝ) : Value := if d.li = 0 then negInf else fl x

private def lseExtended (d : D) (x : ℝ) : EReal := if d.li = 0 then ⊥ else (x : EReal)

private def lseLogReal (d : D) : ℝ := Real.log d.li / Real.log 2

private theorem lseFactor_pos : 0 < lseLog2Factor := by norm_num [lseLog2Factor]

private theorem lse_factor_immediate (t : TState) :
    Assumption.readERealOpnd t .f32 (.f32imm 1060205080) =
      some (.ok (lseLog2Factor : EReal)) := by
  have h := valFloat_b32 (b := 1060205080) (q := (1453635 : ℚ) / 2097152)
    (by decide) (by
      norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
        FloatFmt.expBits, FloatFmt.bias, FloatFmt.layout])
  have hf : valFloat .f32 (b32 1060205080) = .ok lseLog2Factor := by
    simpa [lseLog2Factor] using h
  exact readEReal_of_valFloat hf

private theorem lse_negative_immediate (t : TState) :
    Assumption.readERealOpnd t .f32 (.f32imm 4286578688) = some (.ok (⊥ : EReal)) := rfl

private theorem lse_scalar_read {t : TState} {d : D} {r : Nat} {x : ℝ}
    (hr : t.regs r = some (lseScalar d x)) :
    Assumption.readERealOpnd t .f32 (.reg r) = some (.ok (lseExtended d x)) := by
  rw [readERealOpnd_reg hr]
  by_cases hz : d.li = 0
  · simp only [lseScalar, lseExtended, hz, ite_true]
    rfl
  · simp only [lseScalar, lseExtended, hz, ite_false]
    exact readEReal_of_valFloat (valFloat_fl x)

private theorem lse_ref_read {t : TState} {d : D} (hrow : RowTotal d)
    (hr : t.regs 481 = some (lseRefVal d)) :
    Assumption.readERealOpnd t .f32 (.reg 481) = some (.ok (lseExtended d (reference d))) := by
  rw [readERealOpnd_reg hr]
  by_cases hz : d.li = 0
  · simp only [lseRefVal, lseExtended, hrow.2.mp hz, hz, ite_true]
    rfl
  · have hp : d.peak ≠ ⊥ := fun h => hz (hrow.2.mpr h)
    simp only [lseRefVal, lseExtended, hp, hz, ite_false]
    exact readEReal_of_valFloat (valFloat_miVal d)

private theorem lse_scalar_value (d : D) (x : ℝ) :
    Assumption.erealValue .f32 (lseExtended d x) = lseScalar d x := by
  by_cases hz : d.li = 0
  · simp only [lseExtended, lseScalar, hz, ite_true]
    rw [Assumption.erealValue, ite_eq_right (by exact bot_ne_top), ite_eq_left rfl]
    rfl
  · simp only [lseExtended, lseScalar, hz, ite_false]
    rw [Assumption.erealValue, ite_eq_right (EReal.coe_ne_top _),
      ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe]
    rfl

private theorem lse_scalar_mul (d : D) (x : ℝ) :
    Assumption.mulEReal (lseExtended d x) (lseLog2Factor : EReal) =
      some (lseExtended d (x * lseLog2Factor)) := by
  by_cases hz : d.li = 0
  · have hpos := EReal.coe_pos.mpr lseFactor_pos
    simp [lseExtended, hz, Assumption.mulEReal, EReal.bot_mul_of_pos hpos, ne_of_gt hpos]
  · simp [lseExtended, hz, Assumption.mulEReal]

private theorem lse_scalar_add (d : D) (x y : ℝ) :
    Assumption.addEReal (lseExtended d x) (lseExtended d y) = some (lseExtended d (x + y)) := by
  by_cases hz : d.li = 0 <;> simp [lseExtended, hz, Assumption.addEReal]

private theorem lse_scalar_isInf (d : D) (x : ℝ) :
    Assumption.erealCompare .eq (lseExtended d x) ⊥ = decide (d.li = 0) := by
  by_cases hz : d.li = 0 <;> simp [lseExtended, Assumption.erealCompare, hz, EReal.coe_ne_bot]

private theorem classify_lse_zero : classify .f32 (fl 0) = .ok (.zero false) := by
  have h : FloatFmt.f32.representable 0 := ⟨0, 0, rfl, by norm_num⟩
  obtain ⟨q, hq, hc⟩ := classify_float_repr h
  have hzero : q = 0 := by exact_mod_cast hq
  simpa [fl, hzero, FVal.ofRat] using hc

private theorem run_lse_log (d : D) (hrow : RowTotal d) {t : TState}
    (ha : At t 1162 (factsFrom lseAddrLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u 1163 ((1730, lseScalar d (lseLogReal d)) ::
        factsFrom lseAddrLive (valueOf P L g d)) := by
  let op : Op := .float {
    op := .lg2, ty := ⟨.f32, 1⟩, mode := .approx, ftz := true, dsts := [some 1730],
    srcs := [.reg 482] }
  have hc : kernel.code[1162]? = some ⟨none, op⟩ := Flow.code_1162
  have hr : t.regs 482 = some (fl d.li) :=
    holds_mem ha.2.2.2.2 (mem_factsFrom (r := 482) (by decide +kernel))
  have hread : readValue L g t 32 (.reg 482) = .ok (fl d.li) := by
    simp [readValue, readReg, hr, pure, Except.pure]
  have hsrc : Assumptions.f32ValueOf L g t (.reg 482) = some d.li := by
    simp [Assumptions.f32ValueOf, hread, valFloat_fl, Except.toOption]
  have hlg : Assumptions.lg2Exact.localRule L g t op =
      (if 0 < d.li then some (.ok (PTX.next (setReg t 1730 (fl (Real.log d.li / Real.log 2)))))
        else none) := by
    change (match Assumptions.f32ValueOf L g t (.reg 482) with
      | some x => if 0 < x then
          some (Except.ok (PTX.next (setReg t 1730 (fl (Real.log x / Real.log 2)))))
        else none
      | none => none) = _
    rw [hsrc]
  have hfind : asms.findSome? (fun a => a.localRule L g t op) =
      Assumptions.lg2Exact.localRule L g t op := by
    have hpc := ha.1
    have ht : {t with pc := 1162} = t := by cases t; simp_all
    rw [← ht]
    cases h : Assumptions.lg2Exact.localRule L g {t with pc := 1162} op <;>
      simp only [Assumptions.all, List.findSome?_cons, h] <;> rfl
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 1730 (lseScalar d (lseLogReal d)))) := by
    rw [execLocalA_noSegment (asms_segment_free t), execLocalRule, hfind, hlg]
    by_cases hz : d.li = 0
    · simp only [lseScalar, hz, ite_true, lt_irrefl, ite_false]
      change execFloat L g t {
        op := .lg2, ty := ⟨.f32, 1⟩, mode := .approx, ftz := true, dsts := [some 1730],
        srcs := [.reg 482] } = _
      simp [execFloat, boolCombine, FloatFmt.bytes, floatLane, pure, Except.pure, bind,
        Except.bind, classify_lse_zero, *]
      rfl
    · have hpos : 0 < d.li := lt_of_le_of_ne hrow.1 (Ne.symm hz)
      simp [hpos, lseScalar, lseLogReal, hz]
  exact ⟨_, run_local hc rfl ha he, ha.set (not_mem_factsFrom (by decide +kernel))⟩

private theorem run_lse_log_scale (d : D) {t : TState}
    (ha : At t 1163 ((1730, lseScalar d (lseLogReal d)) ::
      factsFrom lseAddrLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u 1164 ((1731, lseScalar d (lseLogReal d * lseLog2Factor)) ::
        factsFrom lseAddrLive (valueOf P L g d)) := by
  let op : Op := .float {
    op := .mul, ty := ⟨.f32, 1⟩, ftz := true, dsts := [some 1731],
    srcs := [.reg 1730, .f32imm 1060205080] }
  have hc : kernel.code[1163]? = some ⟨none, op⟩ := Flow.code_1163
  have hr := lse_scalar_read ha.2.2.2.2.1
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 1731 (lseScalar d (lseLogReal d * lseLog2Factor)))) := by
    apply Assumption.execLocalA_idealReal
      (f := .mul .f32) rfl (by decide)
      (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
        (List.mem_cons_of_mem _ ha))
    change Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 1730)) (fun x =>
      Assumption.bindRead (Assumption.readERealOpnd t .f32 (.f32imm 1060205080)) fun y =>
        (Assumption.mulEReal x y).map (fun z =>
          .ok (PTX.next (setReg t 1731 (Assumption.erealValue .f32 z))))) = _
    rw [hr, lse_factor_immediate]
    simp only [Assumption.bindRead, lse_scalar_mul, Option.map_some, lse_scalar_value]
  have hat := ha.mono ha.2.2.2.2.2
  exact ⟨_, run_local hc rfl ha he, hat.set (not_mem_factsFrom (by decide +kernel))⟩

private theorem run_lse_fma (d : D) (hrow : RowTotal d) {t : TState}
    (ha : At t 1164 ((1731, lseScalar d (lseLogReal d * lseLog2Factor)) ::
      factsFrom lseAddrLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u 1165 ((1732, lseScalar d (lseValue d)) ::
        factsFrom lseAddrLive (valueOf P L g d)) := by
  let op : Op := .float {
    op := .fma, ty := ⟨.f32, 1⟩, rnd := some .rn, ftz := true, dsts := [some 1732],
    srcs := [.reg 481, .f32imm 1060205080, .reg 1731] }
  have hc : kernel.code[1164]? = some ⟨none, op⟩ := Flow.code_1164
  have hr481 : t.regs 481 = some (lseRefVal d) :=
    holds_mem ha.2.2.2.2.2 (mem_factsFrom (r := 481) (by decide +kernel))
  have hr := lse_ref_read hrow hr481
  have hs := lse_scalar_read ha.2.2.2.2.1
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 1732 (lseScalar d (lseValue d)))) := by
    apply Assumption.execLocalA_idealReal
      (f := .fma .f32) rfl (by decide)
      (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
        (List.mem_cons_of_mem _ ha))
    change Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 481)) (fun x =>
      Assumption.bindRead (Assumption.readERealOpnd t .f32 (.f32imm 1060205080)) fun y =>
        Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 1731)) fun z =>
          ((Assumption.mulEReal x y).bind (fun xy => Assumption.addEReal xy z)).map (fun w =>
            .ok (PTX.next (setReg t 1732 (Assumption.erealValue .f32 w))))) = _
    rw [hr, lse_factor_immediate, hs]
    simp only [Assumption.bindRead, lse_scalar_mul, Option.bind_some, lse_scalar_add,
      Option.map_some, lse_scalar_value]
    rfl
  have hat := ha.mono ha.2.2.2.2.2
  exact ⟨_, run_local hc rfl ha he, hat.set (not_mem_factsFrom (by decide +kernel))⟩

private theorem run_lse_select (d : D) (hrow : RowTotal d) {t : TState}
    (ha : At t 1165 ((1732, lseScalar d (lseValue d)) :: factsFrom lseAddrLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 2 t = some u ∧ At u 1167 (lseAddrFacts P L g d) := by
  let op : Op := .float {
    op := .setp (.ord .eq) none, ty := ⟨.f32, 1⟩, ftz := true,
    dsts := [some 119], srcs := [.reg 1732, .f32imm 4286578688] }
  have hc : kernel.code[1165]? = some ⟨none, op⟩ := Flow.code_1165
  have hr := lse_scalar_read ha.2.2.2.2.1
  have he : execLocalA asms L g t op =
      .ok (PTX.next (setReg t 119 (.pred (decide (d.li = 0))))) := by
    apply Assumption.execLocalA_idealReal
      (f := .setpInf .f32) rfl (by decide)
      (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
        (List.mem_cons_of_mem _ ha))
    change Assumption.bindRead (Assumption.readERealOpnd t .f32 (.reg 1732)) (fun x =>
      Assumption.bindRead (Assumption.readERealOpnd t .f32 (.f32imm 4286578688)) fun y =>
        some (.ok (PTX.next (setReg t 119 (.pred (Assumption.erealCompare .eq x y)))))) = _
    rw [hr, lse_negative_immediate]
    simp only [Assumption.bindRead, lse_scalar_isInf]
  have hnot : ∀ p ∈ (1732, lseScalar d (lseValue d)) :: factsFrom lseAddrLive (valueOf P L g d),
      p.1 ≠ 119 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · change (1732 : Nat) ≠ 119
      decide
    · exact not_mem_factsFrom (by decide +kernel) p hp
  let u := PTX.next (setReg t 119 (.pred (decide (d.li = 0))))
  have hrun : run kernel asms L g 1 t = some u := run_local hc rfl ha he
  have hat : At u 1166 ((119, .pred (decide (d.li = 0))) ::
      (1732, lseScalar d (lseValue d)) :: factsFrom lseAddrLive (valueOf P L g d)) :=
    ha.set hnot
  let i : IntInstr := {
    op := .selp, ty := .float .f32, dsts := [some 1733],
    srcs := [.f32imm 2139095040, .reg 1732, .reg 119] }
  have hc' : kernel.code[1166]? = some ⟨none, .int i⟩ := Flow.code_1166
  have hpeer : Assumptions.peerPackRule u (.int i) = none :=
    Assumptions.peerPackRule_of_none (Assumptions.peerPack_none_of_outside
      (Or.inr (by rw [hat.1]; decide)))
  have hnone := Thread.asms_localRule_int (t := u) (i := i) (L := L) (g := g)
    (by rw [hat.1]; decide) (by rw [hat.1]; decide) (by rw [hat.1]; decide) hpeer
  have hpr : u.regs 119 = some (.pred (decide (d.li = 0))) := hat.2.2.2.2.1
  have hraw : u.regs 1732 = some (lseScalar d (lseValue d)) := hat.2.2.2.2.2.1
  have hval : readValue L g u 32
      (if decide (d.li = 0) then .f32imm 2139095040 else .reg 1732) = .ok (lseReg d) := by
    by_cases hz : d.li = 0
    · have hp := hrow.2.mp hz
      simp only [hz, decide_true, ite_true, lseReg, hp]
      rfl
    · have hp : d.peak ≠ ⊥ := fun h => hz (hrow.2.mpr h)
      simp [hz, hp, readValue, readReg, hraw, lseReg, lseScalar, fl, pure, Except.pure]
  have hsize : (lseReg d).bytes = 4 := by
    unfold lseReg
    split <;> rfl
  have he' : execLocalA asms L g u (.int i) = .ok (PTX.next (setReg u 1733 (lseReg d))) := by
    rw [execLocalA_noSegment (asms_segment_free u), execLocalRule_of_none hnone]
    change execMove L g u (.int i) = _
    simp only [i, execMove, DType.width, readReg, hpr, pure, Except.pure, bind, Except.bind]
    rw [hval]
    simp [hsize]
  have hrun' := run_local hc' rfl hat he'
  have hat' := hat.mono hat.2.2.2.2.2.2
  exact ⟨_, run_comp hrun hrun', hat'.set (not_mem_factsFrom (by decide +kernel))⟩

private theorem lse_branch_facts {d : D} {t : TState} {live : List Nat}
    (h : Holds t.regs ((482, fl d.li) :: factsFrom lseLive (valueOf P L g d)))
    (hkeep : ∀ r ∈ live, r = 482 ∨ r ∈ lseLive) :
    Holds t.regs (factsFrom live (valueOf P L g d)) := by
  refine holds_of_pointwise fun r hr => ?_
  rcases hkeep r hr with rfl | hs
  · exact h.1
  · exact holds_mem h.2 (mem_factsFrom hs)

/-- The completed row sum feeds either an LSE store or the shared PV-completion wait. -/
theorem step_lseRead (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (d : D) (hd : d.site = .lseRead) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    rcases lseRead_branch hpre d hd ha hi hc hf with hn | ⟨d', v, hn, hi', hs, hsub, hr, hv⟩
    · exact Or.inl (Or.inl hn)
    by_cases hf : tidOf L g % 128 < 64
    · simp only [hf, ite_true] at hs hv
      have hrow := hi'.rowTotal (by rw [hs]; rfl)
      have hv' := hv.mono (lse_branch_facts hv.2.2.2.2
        (show ∀ r ∈ lseAddrLive, r = 482 ∨ r ∈ lseLive by decide +kernel))
      obtain ⟨t₁, hr₁, ha₁⟩ := run_lse_log d' hrow hv'
      obtain ⟨t₂, hr₂, ha₂⟩ := run_lse_log_scale d' ha₁
      obtain ⟨t₃, hr₃, ha₃⟩ := run_lse_fma d' hrow ha₂
      obtain ⟨t₄, hr₄, ha₄⟩ := run_lse_select d' hrow ha₃
      obtain ⟨v', hr₅, hav⟩ := run_lse_addr hpre hb hq hf d' ha₄
      have hpc : (code P L g).pc d' = 1178 := by change d'.site.pc = 1178; rw [hs]; rfl
      refine Or.inl (Or.inr ⟨d', v', hn, run_rtg (run_comp (run_comp (run_comp (run_comp
        (run_comp hr hr₁) hr₂) hr₃) hr₄) hr₅), ⟨?_, hi'⟩⟩)
      have hupdate : {d' with site := .lseStore} = d' := by
        cases d'
        cases hs
        rfl
      refine ⟨hav.1.trans hpc.symm, hav.2.1.trans hsub.symm, ?_, hav.2.2.2.1, ?_⟩
      · rw [← hupdate]
        exact hav.2.2.1
      · simpa only [code, hupdate] using hav.2.2.2.2
    · simp only [hf, ite_false] at hs hv
      have hv' := hv.mono (lse_branch_facts hv.2.2.2.2
        (show ∀ r ∈ lseWaitLive, r = 482 ∨ r ∈ lseLive by decide +kernel))
      obtain ⟨v', hR, hav⟩ := run_lse_wait_addr hpre d' hv'
      have hpc : (code P L g).pc d' = 1184 := by change d'.site.pc = 1184; rw [hs]; rfl
      refine Or.inl (Or.inr ⟨d', v', hn, run_rtg (run_comp hr hR), ⟨?_, hi'⟩⟩)
      have hupdate : {d' with site := .svDone} = d' := by
        cases d'
        cases hs
        rfl
      refine ⟨hav.1.trans hpc.symm, hav.2.1.trans hsub.symm, ?_, hav.2.2.2.1, ?_⟩
      · rw [← hupdate]
        exact hav.2.2.1
      · simpa only [code, hupdate] using hav.2.2.2.2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
