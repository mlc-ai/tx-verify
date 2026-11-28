-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Softmax.Soft.RescaleState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Step
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Early
import Kernels.InklingRelDecode.Proof.Softmax.PollStep
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Typed
import Kernels.InklingRelDecode.Proof.Softmax.Export.SentWord
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Softmax.Export.Value
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Proof.Softmax.Data.Round
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Softmax.LateStep
import Kernels.InklingRelDecode.Proof.Softmax.LateHalf
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Close
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Lemmas.Kernel.CountClosed
import Lemmas.Kernel.FrameU
import Lemmas.Flow.TcLdKind
import Lemmas.Flow.TcStWord
import Lemmas.Flow.TcStValsAny
import Kernels.InklingRelDecode.Flow.Code.Part035

@[expose] public section

/-! # The rescale factor a lane sends at pc 2242, from the words of its rounds

The value state of the softmax holds the running maximum and the round's new maximum, and the
rescale factor of the round follows from them (`Softmax.Data`). Along the trace these are functions
of the words the lane's shuffles of pc 1838 sent and received (`roundWords`): the value state
before the shuffle at pc 2242 carries `mRound` and `mxRound`, so the factor it sends is
`alphaWord` of them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem word_nil {e : Event} (h : e.pc ≠ 1838) : wordOf e = [] := by
  obtain ⟨p, k⟩ := e
  cases k <;> simp_all [wordOf]

/-- The words of the accumulator load stay in the state from the load to the store. -/
private def OvInv (X : Execution) (g k : Nat) (y : Data.D) : Prop :=
  (y.c.site = .waitLdO ∨ y.c.site = .bar24 ∨ y.c.site = .stO) →
    ∃ j < k, ∃ a sh, X.get (g, j) = some ⟨2260, .tc (.ld a y.v.ov sh)⟩ ∧ y.v.ov.length = 64 ∧
      pollRound 1257 ((X.tr g).take j) = pollRound 1257 ((X.tr g).take k)

private theorem next_ov {e : Entry} {d dn : Control.D} {ev : Event}
    (step : Control.next e L g d ev = some (some dn)) :
    (dn.site = .waitLdO → d.site = .ldO) ∧ (dn.site = .bar24 → d.site = .waitLdO) ∧
      (dn.site = .stO → d.site = .bar24) := by
  obtain ⟨s, i, v⟩ := d
  have loop : ∀ t i, loopSite e t i ≠ .waitLdO ∧ loopSite e t i ≠ .bar24 ∧
      loopSite e t i ≠ .stO := by
    intro t i
    unfold loopSite
    split <;> first | decide | (split <;> decide)
  cases s <;> simp only [Control.next, advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals dsimp only
  all_goals first
    | exact ⟨fun h => absurd h (loop _ _).1, fun h => absurd h (loop _ _).2.1,
        fun h => absurd h (loop _ _).2.2⟩
    | simp_all

/-- One step keeps the words of the load, given the event of the load site. -/
private theorem ov_step {e : Entry} {X : Execution} {k : Nat} {old y : Data.D} {ev : Event}
    (he : X.get (g, k) = some ev) (inv : OvInv X g k old) (pc : ev.pc = old.c.site.pc)
    (hn : succ e L g old ev = some (some y))
    (ld : old.c.site = .ldO → ∃ a vals sh, ev = ⟨2260, .tc (.ld a vals sh)⟩ ∧
      vals.length = 64) : OvInv X g (k + 1) y := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  obtain ⟨n1, n2, n3⟩ := next_ov hnc
  intro hy
  rcases hy with h | h | h
  · obtain ⟨a, vals, sh, rfl, hl⟩ := ld (n1 h)
    refine ⟨k, by omega, a, sh, ?_, ?_, ?_⟩
    · simp [record, n1 h, he]
    · simp [record, n1 h, hl]
    · rw [poll_same he (by simp)]
  · have hs := n2 h
    obtain ⟨j, hj, a, sh, hg, hl, rd⟩ := inv (.inl hs)
    refine ⟨j, by omega, a, sh, ?_, ?_, ?_⟩
    · simp_all [record]
    · simp_all [record]
    · rw [poll_same he (by rw [pc, hs]; decide), rd]
  · have hs := n3 h
    obtain ⟨j, hj, a, sh, hg, hl, rd⟩ := inv (.inr (.inl hs))
    refine ⟨j, by omega, a, sh, ?_, ?_, ?_⟩
    · simp_all [record]
    · simp_all [record]
    · rw [poll_same he (by rw [pc, hs]; decide), rd]

private theorem round_inv {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → (Early s → roundWords X g k = []) ∧
        ∀ w ent y n, s = softDState w ent y n →
          RoundInv L (roundWords X g k) y ∧ OvInv X g k y := by
  have key := Frame.stateAt_inv (C := threadD Q L) (X := X) (g := g)
    (fun k s => Frame.NoUbBefore X g k → (Early s → roundWords X g k = []) ∧
      ∀ w ent y n, s = softDState w ent y n →
        RoundInv L (roundWords X g k) y ∧ OvInv X g k y)
    (by
      intro nub
      refine ⟨fun _ => by simp [roundWords], fun w ent y n h => ?_⟩
      have h1 := congrArg Prod.fst h
      change Code.enter (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at h1
      simp [Code.enter, Code.gatedExit, enterOf_init] at h1)
    (by
      intro k e s s' he hs IH hn nub'
      have nub0 : Frame.NoUbBefore X g k := fun j hj => nub' j (by omega)
      have he' : X.get (g, k) = some e := he
      have hu : ∀ f, e.kind ≠ .ub f := nub' k (by omega) e he'
      obtain ⟨E1, E2⟩ := IH nub0
      have words := roundWords_succ he'
      have pc := Frame.event_pcU (fun g h => threadD_sound hp h) hX he' hs hu
      refine ⟨fun hearly => ?_, fun w ent y n hsd => ?_⟩
      · have es := early_pred hn hearly
        rw [words, E1 es, word_nil (pc ▸ (early_pc es).2)]
        rfl
      · subst hsd
        rcases softD_pred hn with ⟨rfl, d, cnt, rfl⟩ | ⟨old, cnt, rfl, hv⟩
        · have es : Early (proDState (Q := Q) (L := L) (g := g) w d cnt) := .inr ⟨w, d, rfl⟩
          rw [words, E1 es, word_nil (pc ▸ (early_pc es).2)]
          exact ⟨round_init L, fun h => by rcases h with h | h | h <;> cases h⟩
        · rw [words]
          change e.pc = old.c.site.pc at pc
          refine ⟨round_step (E2 w ent old cnt rfl).1 hv pc fun h5 => ?_,
            ov_step he' (E2 w ent old cnt rfl).2 pc hv fun hld => ?_⟩
          · have p : e.pc = 1838 := by rw [pc, h5]; rfl
            have iss : Execution.isShfl e = true := by
              rw [Lib.shfl_event hX he' hu, p]
              decide
            obtain ⟨pc0, kind⟩ := e
            cases kind <;> simp [Execution.isShfl] at iss
            exact ⟨_, _, _, _, _, _, rfl⟩
          · obtain ⟨t, ins, o, ht, -, hc, fire⟩ :=
              Frame.fired_siteU (fun g h => threadD_sound hp h) hX he' hs hu
            change (Data.codeS ent L g).AtD old t at ht
            have ht := atS_code ht
            have pc2 : old.c.site.pc = 2260 := by rw [hld]; rfl
            change kernel.code[old.c.site.pc]? = some ins at hc
            change Fires old.c.site.pc (eventTmpl Assumptions.all L g t ins.op) e o at fire
            rw [pc2] at hc fire
            obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_1)
            have hw : Assumptions.all.any (·.tcLdWait t.pc) = false := by
              rw [ht.1.trans pc2]; decide +kernel
            obtain ⟨a, vals, hl, rfl⟩ :=
              fires_tcLd_kind (sh := .s16x32bx2 64) (fun s h => nomatch h) fire hw hu
            exact ⟨a, vals, _, rfl, by rw [hl]; rfl⟩)
  exact fun k hk s hs nub => key k s hk hs nub

/-- **The rescale factor a lane sends at pc 2242** is the one the words of its rounds leave: the
running maximum before the round and the round's new maximum are functions of the words the
shuffles of pc 1838 before sent and received. -/
theorem alpha_operand {m : Mem0} {X : Execution} {j : Nat} {a r : Value}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (st : Stage X 0 g j a r) :
    a = alphaWord (scaleW L) (mRound L X g j) (mxRound L X g j) := by
  obtain ⟨ok, get⟩ := st
  have clean : ∀ f, (Event.mk (2242 + 2 * 0) (.shfl .bfly a (8 >>> 0) 31 r ok)).kind ≠ .ub f :=
    fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by show 574 < 2242 + 2 * 0; omega)
    (by show 2242 + 2 * 0 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have inv := ((round_inv hp hX j len _ hs nub).2 w ent y n rfl).1
  have site : y.c.site = .shfl7 := by
    have h7 : y.c.site.pc = 2242 := by
      have := atpc
      rw [← hy] at this
      exact this.symm
    revert h7
    cases y.c.site <;> repeat' first | decide +kernel | (rename_i i; revert i)
  have round : inRound y.c.site = true := by rw [site]; rfl
  obtain ⟨ps0, p, hps, hm, hmx⟩ := inv.2.2 round
  obtain ⟨t, ins, o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t at ht
  have ht := atS_code ht
  change kernel.code[y.c.site.pc]? = some ins at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  have h7 : y.c.site.pc = 2242 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2242)
  obtain ⟨same, -, -, -⟩ := Lib.shfl_operand (n := 8) (m := (8 : Nat)) (bv := 8) rfl rfl fire rfl
  have reg : t.regs 507 = some (alphaWord (scaleW L) y.v.m y.v.mx) := by
    refine holds_mem (atD_dF ht) ?_
    exact round_sub round y.v _ (by simp [alphaFacts, alphaWord])
  have eq : a = alphaWord (scaleW L) y.v.m y.v.mx := Option.some.inj (same.symm.trans reg)
  rw [eq, hm, hmx]
  have last : (roundWords X g j).getLast? = some p := by rw [hps]; simp
  have drop : (roundWords X g j).dropLast = ps0 := by rw [hps]; simp
  simp only [mRound, mxRound, last, drop]
  rw [hm]

/-- **The words a lane stores at pc 2328** are the rescale factor of its round times the words
the accumulator load of pc 2260 returned. -/
theorem rescale_store {m : Mem0} {X : Execution} {k a : Nat} {vals : List Value} {sh : TcShape}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g, k) = some ⟨2328, .tc (.st a vals sh)⟩) :
    vals.length = 64 ∧ ∃ j < k, ∃ a' ov sh', X.get (g, j) = some ⟨2260, .tc (.ld a' ov sh')⟩ ∧
      ov.length = 64 ∧ ∀ i < 64, vals[i]? = some (okVal (.bits 32 0)
        (mulE false (alphaWord (scaleW L) (mRound L X g k) (mxRound L X g k))
          (ov.getD i (b32 0)))) := by
  have clean : ∀ f, (Event.mk 2328 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by show 574 < 2328; omega)
    (by show 2328 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  obtain ⟨rinv, oinv⟩ := (round_inv hp hX k len _ hs nub).2 w ent y n rfl
  have site : y.c.site = .stO := by
    have h7 : y.c.site.pc = 2328 := by
      have := atpc
      rw [← hy] at this
      exact this.symm
    revert h7
    cases y.c.site <;> repeat' first | decide +kernel | (rename_i i; revert i)
  have round : inRound y.c.site = true := by rw [site]; rfl
  obtain ⟨ps0, p, hps, hm, hmx⟩ := rinv.2.2 round
  obtain ⟨j, hj, a', sh', hg, hl, -⟩ := oinv (.inr (.inr site))
  obtain ⟨t, ins, o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t at ht
  change kernel.code[y.c.site.pc]? = some ins at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  obtain ⟨hl64, hwords⟩ :=
    rs_site_words (ent := ent) (a := a) (vals := vals) (sh := sh) ht hc fire site
  refine ⟨hl64, j, hj, a', y.v.ov, sh', hg, hl, ?_⟩
  intro i hi
  have last : (roundWords X g k).getLast? = some p := by rw [hps]; simp
  have drop : (roundWords X g k).dropLast = ps0 := by rw [hps]; simp
  rw [hwords i hi]
  simp only [mRound, mxRound, last, drop, hm, hmx]

/-- **A rescale store follows the accumulator load of its own round** in its thread. -/
theorem rescale_round {m : Mem0} {X : Execution} {k a : Nat} {vals : List Value} {sh : TcShape}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g, k) = some ⟨2328, .tc (.st a vals sh)⟩) :
    ∃ j < k, ∃ a' ov sh', X.get (g, j) = some ⟨2260, .tc (.ld a' ov sh')⟩ ∧
      pollRound 1257 ((X.tr g).take j) = pollRound 1257 ((X.tr g).take k) := by
  have clean : ∀ f, (Event.mk 2328 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by show 574 < 2328; omega)
    (by show 2328 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  obtain ⟨-, oinv⟩ := (round_inv hp hX k len _ hs nub).2 w ent y n rfl
  have site : y.c.site = .stO := by
    have h7 : y.c.site.pc = 2328 := by
      have := atpc
      rw [← hy] at this
      exact this.symm
    revert h7
    cases y.c.site <;> repeat' first | decide +kernel | (rename_i i; revert i)
  obtain ⟨j, hj, a', sh', hg, -, rd⟩ := oinv (.inr (.inr site))
  exact ⟨j, hj, a', y.v.ov, sh', hg, rd⟩

/-- A shuffle of pc 1838 is a butterfly shuffle of the lane 16 away. -/
public theorem shfl5_shape {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}
    {mode a b c recv ok} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g, k) = some ⟨1838, .shfl mode a b c recv ok⟩) :
    mode = .bfly ∧ b = 16 ∧ c = 31 := by
  have clean : ∀ f, (Event.mk 1838 (.shfl mode a b c recv ok)).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hs, at_pc⟩ := at_site hp hX get clean (by show 574 < 1838; omega)
    (by show 1838 < 2331; omega)
  obtain ⟨-, hm, hb, hc⟩ := operand hX hp get rfl at_pc.symm hs Flow.code_shfl_5
    (fun _ => ⟨_, rfl, rfl⟩)
  exact ⟨hm, hb, hc⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
