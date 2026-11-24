-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Lemmas.Step.WarpLanes

@[expose] public section

/-! # The index producer's butterfly shuffle operands and delivery -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index

open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem bfly_template {g src dst pred value shift : Nat}
    {t : TState}
    (hb : L.block % 32 = 0) (hr : t.regs src = some (b32 value))
    (hshift : shift = 1 ∨ shift = 2) :
    eventTmpl asms L g t
      (.warp ⟨.shfl .bfly, some (.int .b 32), [some dst, some pred],
        [.reg src, .imm shift, .imm 31], some (.imm (-1))⟩) =
      .shfl .bfly (b32 value) shift 31
        (fun recv ok => PTX.next (setReg (setReg t dst recv) pred (.pred ok))) := by
  have hw : warpTmpl L g t ⟨.shfl .bfly, some (.int .b 32), [some dst, some pred],
        [.reg src, .imm shift, .imm 31], some (.imm (-1))⟩ =
      shflTmpl L g t .bfly dst (some pred) (.reg src) (.imm shift) (.imm 31) (.imm (-1)) := rfl
  simp only [eventTmpl, hw, shflTmpl, readBits, readValue, readReg, hr, b32,
    Value.bytes, hb, pure, Except.pure]
  have hn : (truncBits 32 (BitVec.ofInt 64 shift)).toNat = shift := by
    rcases hshift with rfl | rfl <;> decide
  rw [ite_eq_left (by decide), ite_eq_left trivial, hn,
    show (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 by decide]

private theorem fire_bfly {g src dst pred pc value shift : Nat}
    {t : TState} {e : Event} {o : Option TState}
    (hb : L.block % 32 = 0) (hr : t.regs src = some (b32 value))
    (hshift : shift = 1 ∨ shift = 2)
    (hf : Fires pc (eventTmpl asms L g t
      (.warp ⟨.shfl .bfly, some (.int .b 32), [some dst, some pred],
        [.reg src, .imm shift, .imm 31], some (.imm (-1))⟩)) e o) :
    ∃ recv ok, e = ⟨pc, .shfl .bfly (b32 value) shift 31 recv ok⟩ := by
  rw [bfly_template hb hr hshift] at hf
  obtain ⟨recv, ok, he, _⟩ := hf
  exact ⟨recv, ok, he⟩

private theorem shuffle_site {g : Nat} {d : D} {e : Event} {o : Option TState} {ins : Instr}
    (hf : (Machine.machine P L g).Fired (some (.index d)) e o)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ t, AtD P L g d t ∧ Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change AtD P L g d t at hat
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hc, hat.1] at hf
  exact ⟨t, hat, hf⟩

/-- The first butterfly sends this lane's sign-extended validity word. -/
theorem quad1_fired_shape {g : Nat} {d : D} {extra : Bool} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hs : d.site = .quad1 extra)
    (hf : (Machine.machine P L g).Fired (some (.index d)) e o) :
    ∃ recv ok, e = ⟨d.site.pc, .shfl .bfly (b32 (laneWord P L g d.block (laneOf L g))) 1 31
      recv ok⟩ := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  cases extra
  · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hs).trans Flow.code_2464
    obtain ⟨t, hat, hf⟩ := shuffle_site hf hc
    have hr := hat.reg (r := 606) (by rw [hs]; decide +kernel)
    exact fire_bfly hb hr (.inl rfl) hf
  · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hs).trans Flow.code_2553
    obtain ⟨t, hat, hf⟩ := shuffle_site hf hc
    have hr := hat.reg (r := 645) (by rw [hs]; decide +kernel)
    exact fire_bfly hb hr (.inl rfl) hf

/-- The second butterfly sends this lane's pair's combined validity word. -/
theorem quad2_fired_shape {g : Nat} {d : D} {extra : Bool} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hs : d.site = .quad2 extra)
    (hf : (Machine.machine P L g).Fired (some (.index d)) e o) :
    ∃ recv ok, e = ⟨d.site.pc, .shfl .bfly (b32 (pairWord P L g d.block (laneOf L g))) 2 31
      recv ok⟩ := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  cases extra
  · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hs).trans Flow.code_2467
    obtain ⟨t, hat, hf⟩ := shuffle_site hf hc
    have hr := hat.reg (r := 609) (by rw [hs]; decide +kernel)
    exact fire_bfly hb hr (.inr rfl) hf
  · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hs).trans Flow.code_2556
    obtain ⟨t, hat, hf⟩ := shuffle_site hf hc
    have hr := hat.reg (r := 648) (by rw [hs]; decide +kernel)
    exact fire_bfly hb hr (.inr rfl) hf

/-- The pending butterfly uses the same actual operand and continuation as its firing. -/
theorem quad_template {g : Nat} {d : D} {extra second : Bool} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (hd : d.site = if second then .quad2 extra else .quad1 extra)
    (ha : AtD P L g d t) (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl asms L g t ins.op =
      .shfl .bfly (b32 (if second then pairWord P L g d.block (laneOf L g)
        else laneWord P L g d.block (laneOf L g))) (if second then 2 else 1) 31 k := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  cases second <;> cases extra
  · rw [hd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2464)
    have hr := ha.reg (r := 606) (by rw [hd]; decide +kernel)
    exact ⟨_, bfly_template hb hr (.inl rfl)⟩
  · rw [hd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2553)
    have hr := ha.reg (r := 645) (by rw [hd]; decide +kernel)
    exact ⟨_, bfly_template hb hr (.inl rfl)⟩
  · rw [hd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2467)
    have hr := ha.reg (r := 609) (by rw [hd]; decide +kernel)
    exact ⟨_, bfly_template hb hr (.inr rfl)⟩
  · rw [hd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2556)
    have hr := ha.reg (r := 648) (by rw [hd]; decide +kernel)
    exact ⟨_, bfly_template hb hr (.inr rfl)⟩

/-- The lane with the butterfly-selected source index in the receiver's warp. -/
def butterflyPeer (L : Launch) (g shift : Nat) : Nat :=
  g - laneOf L g + (laneOf L g ^^^ shift)

private theorem proof_lane {g : Nat} (hpre : Pre P L mem0) :
    PTX.laneOf L g = laneOf L g := by
  rw [PTX.laneOf, Proof.laneOf, tidOf_eq hpre, hpre.block]

private theorem warp_butterfly {g shift : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hshift : shift < 32) :
    SameWarp L g (butterflyPeer L g shift) ∧
      laneOf L (butterflyPeer L g shift) = laneOf L g ^^^ shift := by
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have h := Step.sameWarp_lane (by rw [hpre.block]) hg (Nat.xor_lt_two_pow (n := 5) hl hshift)
  simpa only [proof_lane hpre, butterflyPeer] using h

private theorem shflSource_eq {l shift : Nat} (hl : l < 32) (hshift : shift < 32) :
    shflSource .bfly l shift 31 = (l ^^^ shift, true) := by
  have h := Nat.xor_lt_two_pow (n := 5) hl hshift
  simp [shflSource, Nat.mod_eq_of_lt hshift, show l ^^^ shift ≤ 31 by omega]

private theorem same_cta_words {g h b l : Nat} (hw : SameWarp L g h) :
    laneWord P L h b l = laneWord P L g b l ∧ pairWord P L h b l = pairWord P L g b l := by
  have hcta : ctaOf L h = ctaOf L g := hw.1.2.2.symm
  simp only [pairWord, laneWord, laneByte, laneMask, validBit, slotIdx, eOf, qOf, ctaidX, ctaidY,
    hcta]
  exact ⟨rfl, rfl⟩

/-- The butterfly receives from its warp peer. Matching the stage and block is the remaining
cross-thread trace condition; the event template fixes the mask, selector and sending operand. -/
theorem butterfly_received {X : Execution} {g i n pc shift : Nat} {a recv : Value} {ok : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hshift : shift < 32) (he : X.get (g, i) = some ⟨pc, .shfl .bfly a shift 31 recv ok⟩)
    (hn : X.ShflK (g, i) n) (hnoexit : ¬ ShflExited X (butterflyPeer L g shift) n) :
    ok = true ∧ ∃ j pc' b' c' recv' ok', X.ShflK (butterflyPeer L g shift, j) n ∧
      X.get (butterflyPeer L g shift, j) = some ⟨pc', .shfl .bfly recv b' c' recv' ok'⟩ := by
  obtain ⟨hok, hpeer⟩ := hX.shfl g i n pc .bfly a shift 31 recv ok he hn
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hsource := shflSource_eq hl hshift
  rw [proof_lane hpre, hsource] at hok hpeer
  exact ⟨hok, hpeer.resolve_right hnoexit⟩

/-- At this ordinal the source lane has its shuffle at the receiver's site and block. -/
def MatchingButterfly (P : Params) (L : Launch) (X : Execution)
    (g n shift : Nat) (d : D) : Prop :=
  let h := butterflyPeer L g shift
  ¬ ShflExited X h n ∧
    ∀ j e, X.ShflK (h, j) n → X.get (h, j) = some e →
      ∃ d', Frame.stateAt (Machine.code P L) X h j = some (some (.index d')) ∧
        d'.site = d.site ∧ d'.block = d.block

variable {X : Execution} {g i n : Nat} {d : D} {extra : Bool} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
include hpre hX hs

/-- In a matching first butterfly, the source event certifies the received lane word. -/
theorem quad1_received (hd : d.site = .quad1 extra) (he : X.get (g, i) = some e)
    (hn : X.ShflK (g, i) n) (hf : (Machine.machine P L g).Fired (some (.index d)) e o)
    (hm : MatchingButterfly P L X g n 1 d) :
    e.kind = .shfl .bfly (b32 (laneWord P L g d.block (laneOf L g))) 1 31
      (b32 (laneWord P L g d.block (laneOf L g ^^^ 1))) true := by
  obtain ⟨recv, ok, rfl⟩ := quad1_fired_shape hpre hd hf
  obtain ⟨rfl, j, pc, b, c, r, ok, hj, hget⟩ :=
    butterfly_received hpre hX (shift := 1) (by decide) he hn hm.1
  obtain ⟨hw, hlane⟩ := warp_butterfly (shift := 1) hpre (Frame.lt_of_get hX he) (by decide)
  obtain ⟨d', hstate, hsite, hblock⟩ := hm.2 _ _ hj hget
  obtain ⟨o, hfire⟩ := RingEvents.fired_of_trace hX (hs _ hw.1.2.1) hget hstate
  obtain ⟨recv', ok', hshape⟩ := quad1_fired_shape hpre (hsite.trans hd) hfire
  have hkind := Kind.shfl.inj (congrArg Event.kind hshape)
  have hrecv := hkind.2.1
  rw [hrecv, hblock, hlane, (same_cta_words (P := P) hw).1]

/-- In a matching second butterfly, the source event certifies the received pair word. -/
theorem quad2_received (hd : d.site = .quad2 extra) (he : X.get (g, i) = some e)
    (hn : X.ShflK (g, i) n) (hf : (Machine.machine P L g).Fired (some (.index d)) e o)
    (hm : MatchingButterfly P L X g n 2 d) :
    e.kind = .shfl .bfly (b32 (pairWord P L g d.block (laneOf L g))) 2 31
      (b32 (pairWord P L g d.block (laneOf L g ^^^ 2))) true := by
  obtain ⟨recv, ok, rfl⟩ := quad2_fired_shape hpre hd hf
  obtain ⟨rfl, j, pc, b, c, r, ok, hj, hget⟩ :=
    butterfly_received hpre hX (shift := 2) (by decide) he hn hm.1
  obtain ⟨hw, hlane⟩ := warp_butterfly (shift := 2) hpre (Frame.lt_of_get hX he) (by decide)
  obtain ⟨d', hstate, hsite, hblock⟩ := hm.2 _ _ hj hget
  obtain ⟨o, hfire⟩ := RingEvents.fired_of_trace hX (hs _ hw.1.2.1) hget hstate
  obtain ⟨recv', ok', hshape⟩ := quad2_fired_shape hpre (hsite.trans hd) hfire
  have hkind := Kind.shfl.inj (congrArg Event.kind hshape)
  have hrecv := hkind.2.1
  rw [hrecv, hblock, hlane, (same_cta_words (P := P) hw).2]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index
