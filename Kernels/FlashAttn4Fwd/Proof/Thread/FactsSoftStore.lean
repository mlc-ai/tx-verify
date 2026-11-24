-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftP2
public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats
public import Lemmas.Flow.StoreValue
public import Lemmas.Flow.BarRegAny

@[expose] public section

/-! # The softmax warps' statistics words

A softmax thread's only memory accesses are its 4-byte stores of its statistics word, at the
sites `alphaSt` (the rescale factor's register) and `lSt` (the row sum's register)
(`soft_wr`). At such a store it has one more successful credit poll than arrivals on its
statistics barrier, and its next event is the arrival (the site `gen 1` or `gen 2`): the
softmax part of `StatsFacts.stats_access`. The stores of an item are of distinct generations
of the barrier, and each store site is passed once per trip (`FloatFacts_soft_store_one`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A softmax thread's write** is a 4-byte store of its statistics word, of the rescale
factor at `alphaSt` or of the row sum at `lSt`. -/
theorem soft_wr {g i pc : Nat} {a : Acc} {bs : List Byte} (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) :
    ∃ d : Softmax.D, Frame.stateAt (code L) X g i = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take i) ∧ Softmax.Inv L g d ∧
      a.loc = Softmax.statsWord L g ∧ a.size = 4 ∧
      ((d.site = .alphaSt ∧ bs = (Softmax.alphaV L d).toBytes) ∨
        (d.site = .lSt ∧ ∃ v, storeValue 32 d.l = .ok v ∧ bs = v.toBytes)) := by
  obtain ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  refine ⟨d, hσ, hc, hi, ?_⟩
  have h4 := hat.2.2.2.2
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have htid : Softmax.tidOf L g < 512 := by
    simp only [Softmax.tidOf, hpre.block]; exact Nat.mod_lt _ (by decide)
  have key : ∀ {r src : Nat} {ik : IType} {v : Value}, t.sub = 0 →
      kernel.code[d.site.pc]? = some ⟨none, .mem
        { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
          addr := ⟨.reg r 32, 332⟩, srcs := [.reg src] }⟩ →
      t.regs r = some (Prologue.sb L (4 * Softmax.tidOf L g)) → t.regs src = some v →
      a.loc = Softmax.statsWord L g ∧ a.size = 4 ∧
        ∃ v', storeValue 32 v = .ok v' ∧ bs = v'.toBytes := by
    intro r src ik v hsub hcd hr hv
    obtain rfl := Option.some.inj (hcode.symm.trans hcd)
    simp only [Prologue.sb] at hr
    obtain ⟨v', hsv, acc, hk, hl, hsz⟩ := fires_st_val (off := 332) hr (by omega) hsub hv hf
    injection hk with h1 h2
    subst h1 h2
    refine ⟨?_, hsz, v', hsv, rfl⟩
    rw [hl]
    simp only [Softmax.statsWord, Softmax.ownLoc, Softmax.sb, Loc.mk.injEq, true_and]
    constructor
    · rfl
    · omega
  cases hsd : d.site with
  | alphaSt =>
    obtain ⟨r1, r2⟩ := Softmax.regs_alphaSt hsd h4
    obtain ⟨h1, h2, v', hsv, h3⟩ := key (by rw [hat.2.1, hsd]; rfl)
      (by rw [hsd]; exact Flow.code_store_0) r1 r2
    rw [storeValue_of_bytes (Softmax.alphaV_bytes L d)] at hsv
    obtain rfl := (Except.ok.inj hsv).symm
    exact ⟨h1, h2, .inl ⟨rfl, h3⟩⟩
  | lSt =>
    obtain ⟨r1, r2⟩ := Softmax.regs_lSt hsd h4
    obtain ⟨h1, h2, h3⟩ := key (by rw [hat.2.1, hsd]; rfl)
      (by rw [hsd]; exact Flow.code_store_1) r1 r2
    exact ⟨h1, h2, .inr ⟨rfl, h3⟩⟩
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

/-- At a statistics store the thread has one more credit poll than arrivals on its statistics
barrier, and it is generation `(n + 1) i + t + 1` of trip `t`. -/
theorem soft_wr_counts {g i : Nat} {d : Softmax.D} (hw : warpOf L g < 8)
    (hc : Softmax.Counts L g d ((X.tr g).take i)) (hi : Softmax.Inv L g d)
    (hs : d.site = .alphaSt ∨ d.site = .lSt) :
    okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take i) =
      barOrd X g i (warpOf L g + 3) + 1 ∧
    barOrd X g i (warpOf L g + 3) = (Softmax.trips L + 1) * d.i + d.t + 1 ∧
    writesAt (Softmax.statsWord L g) ((X.tr g).take i) = Softmax.trips L * d.i + d.t := by
  rw [soft_barOrd_gen hpre hX ht hw hc, soft_statsBar, hc.stats, hc.word]
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs ⊢
  rcases hs with rfl | rfl <;>
    simp [Softmax.statsPos, Softmax.genPos, Softmax.wrPos, Softmax.tileNo, Softmax.Site.inItem,
      Softmax.Site.tile0, Softmax.Site.inTrip, Softmax.Site.afterGen, Softmax.Site.afterAlpha] <;>
    omega

/-- **`StatsFacts.stats_access`, softmax part.** -/
theorem Facts.Soft.stats_access {g i : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hw : warpOf L g < 8) (hacc : X.Access (g, i) a w) (_hcov : a.Covers l)
    (_hin : InStatsArea L l) :
    (warpOf L g < 8 ∧ SoftStore L X g i a w) ∨
      (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ ∃ st < 2, CorrLoad L X g i a w st) := by
  rcases hacc with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · exfalso
    obtain ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩ :=
      soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
    obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
    cases site <;> simp [Softmax.Ev] at hev
  swap
  · exfalso
    obtain ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩ :=
      soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
    obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
    cases site <;> simp [Softmax.Ev] at hev
  refine .inl ⟨hw, rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d, -, -, -, hl, -⟩ := soft_wr hpre hX ht hw he
    rw [hl]
    have hb := hpre.block
    simp only [Softmax.statsWord, Softmax.ownLoc, Softmax.sb, statsWord, rowOf, Softmax.tidOf,
      Loc.mk.injEq, true_and]
    simp only [warpOf] at hw ⊢
    omega
  · obtain ⟨d, -, -, -, -, hsz, -⟩ := soft_wr hpre hX ht hw he
    exact hsz
  · obtain ⟨d, -, hc, hi, -, -, hs⟩ := soft_wr hpre hX ht hw he
    exact (soft_wr_counts hpre hX ht hw hc hi (hs.imp (·.1) (·.1))).1
  · intro hlen
    obtain ⟨d, hσ, -, hi, -, -, hs⟩ := soft_wr hpre hX ht hw he
    obtain ⟨x, hx⟩ : ∃ x, X.get (g, i + 1) = some x := ⟨_, List.getElem?_eq_getElem hlen⟩
    have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
    have hσ' := soft_succ hσ he
    obtain ⟨j, d', hσ'', hs'⟩ : ∃ (j : Fin 3) (d' : Softmax.D),
        Frame.stateAt (code L) X g (i + 1) = some (some (.inr (.softmax d'))) ∧
          d'.site = .gen j := by
      rcases hs with ⟨hs, -⟩ | ⟨hs, -⟩
      · refine ⟨1, { d with site := .gen 1 }, ?_, rfl⟩
        rw [hσ']
        simp only [Softmax.next, hs]
        rfl
      · refine ⟨2, { d with site := .gen 2 }, ?_, rfl⟩
        rw [hσ']
        simp only [Softmax.next, hs]
        rfl
    obtain ⟨t, ins, o, hat, -, hcd, hf⟩ := Frame.fired_site hC hX hx hσ''
    have hr := Softmax.regs_gen hs' hat.2.2.2.2
    rw [soft_statsId] at hr
    have hcode : ∃ al, ins.op = .barArrive (.reg 1017) (.imm 64) al := by
      change kernel.code[d'.site.pc]? = some ins at hcd
      rw [hs'] at hcd
      rcases Softmax.fin3_cases j with rfl | rfl | rfl
      · exact ⟨_, congrArg Instr.op (Option.some.inj (hcd.symm.trans Flow.code_barArrive_0))⟩
      · exact ⟨_, congrArg Instr.op (Option.some.inj (hcd.symm.trans Flow.code_barArrive_1))⟩
      · exact ⟨_, congrArg Instr.op (Option.some.inj (hcd.symm.trans Flow.code_barArrive_2))⟩
    obtain ⟨al, hop⟩ := hcode
    rw [hop] at hf
    have := fires_barArrive_reg_any hr (by omega) (by decide) (by decide) (by decide)
      (by rw [hpre.block]; decide) hf
    exact ⟨_, by rw [hx, this]⟩

/-- **`FloatFacts.soft_store_one`**: a softmax thread stores its statistics word once per
generation of its statistics barrier. -/
theorem FloatFacts_soft_store_one {g i i' pc pc' : Nat} {a a' : Acc} {ws ws' : List Byte}
    (_hg : g < L.threads) (hw : warpOf L g < 8) (he : X.get (g, i) = some ⟨pc, .wr a ws⟩)
    (he' : X.get (g, i') = some ⟨pc', .wr a' ws'⟩) (_hs : SoftStore L X g i a true)
    (_hs' : SoftStore L X g i' a' true)
    (hb : barOrd X g i (warpOf L g + 3) = barOrd X g i' (warpOf L g + 3)) : i = i' := by
  obtain ⟨d, -, hc, hi, hl, -, hs⟩ := soft_wr hpre hX ht hw he
  obtain ⟨d', -, hc', hi', hl', -, hs'⟩ := soft_wr hpre hX ht hw he'
  have hs1 : d.site = .alphaSt ∨ d.site = .lSt := hs.imp (·.1) (·.1)
  have hs2 : d'.site = .alphaSt ∨ d'.site = .lSt := hs'.imp (·.1) (·.1)
  obtain ⟨-, hb1, hw1⟩ := soft_wr_counts hpre hX ht hw hc hi hs1
  obtain ⟨-, hb2, hw2⟩ := soft_wr_counts hpre hX ht hw hc' hi' hs2
  have htr1 : d.t + 1 < Softmax.trips L ∨ d.t + 1 = Softmax.trips L := by
    rcases hs1 with h | h
    · exact .inl (hi.trip (by rw [h]; rfl))
    · exact .inr (hi.last (.inl h))
  have htr2 : d'.t + 1 < Softmax.trips L ∨ d'.t + 1 = Softmax.trips L := by
    rcases hs2 with h | h
    · exact .inl (hi'.trip (by rw [h]; rfl))
    · exact .inr (hi'.last (.inl h))
  rw [hb1, hb2] at hb
  have hit : d.i = d'.i ∧ d.t = d'.t := by
    have := tile_inj (n := Softmax.trips L + 1) (i := d.i) (i' := d'.i) (T := d.t + 1)
      (T' := d'.t + 1) (by omega) (by omega) (by omega)
    omega
  have hP : ∀ {x y : Nat} {e : Event} {b : Acc} {v : List Byte}, X.get (g, x) = some e →
      e.kind = .wr b v → b.loc = Softmax.statsWord L g → x < y →
      writesAt (Softmax.statsWord L g) ((X.tr g).take x) + 1 ≤
        writesAt (Softmax.statsWord L g) ((X.tr g).take y) := by
    intro x y e b v hx hk hbl hxy
    refine countP_take_lt hx ?_ hxy
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    simp [writeAt, hbl]
  rw [hit.1, hit.2] at hw1
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have := hP he rfl hl hlt
    omega
  · exact heq
  · have := hP he' rfl hl' hgt
    omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
