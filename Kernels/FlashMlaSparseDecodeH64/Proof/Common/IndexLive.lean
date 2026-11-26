-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Measure
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Words

@[expose] public section

/-! # The index warp does not stop at its length loads
-- domain: consistent

The index warp is at a length load only when the load's pointer is set (`ixLenOk`, kept along the
thread by `ix_ok`: the first state `ixFirst` and the step after the first length `ixAfterA`
test the pointers, no other step goes to a length load). There the load reads the row's 32-bit
word in a consistent execution (`ix_topk`, `ix_extra`, `Index/Nc.lean`), so the machine goes on
(`ix_live`, `Common/IndexNoStop.lean`). So the recorded length words
are the launch's (`ixLenOk` off the length loads, `Index.words_step` for the other steps) and the
role's block count is the CTA's (`ix_rounds`: `roundsOf d.c.l0 d.c.l1 = blocksOf`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The words an index state has recorded**: at a length load its pointer is set and the
other length is the parameter or the loaded word; elsewhere both words are the launch's. -/
def ixLenOk (P : Params) (L : Launch) (g : Nat) (d : Index.D) : Prop :=
  match d.site with
  | .lenA => eqz64 (pw8 (P.topkLenBase.getD 0)) = false ∧ d.c.l1 = pw P.extra_topk
  | .lenB => eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false ∧ d.c.l0 = lenWA P L (g / L.block)
  | _ => d.c.l0 = lenWA P L (g / L.block) ∧ d.c.l1 = lenWB P L (g / L.block)

/-- The words of a state off the length loads. -/
theorem ix_words_of {d : Index.D} (hA : d.site ≠ .lenA) (hB : d.site ≠ .lenB)
    (h : ixLenOk P L g d) :
    d.c.l0 = lenWA P L (g / L.block) ∧ d.c.l1 = lenWB P L (g / L.block) := by
  obtain ⟨site, el, ac, c⟩ := d
  cases site with
  | lenA => exact absurd rfl hA
  | lenB => exact absurd rfl hB
  | _ => exact h

private theorem ok_of {d : Index.D} (hA : d.site ≠ .lenA) (hB : d.site ≠ .lenB)
    (h0 : d.c.l0 = lenWA P L (g / L.block)) (h1 : d.c.l1 = lenWB P L (g / L.block)) :
    ixLenOk P L g d := by
  obtain ⟨site, el, ac, c⟩ := d
  cases site with
  | lenA => exact absurd rfl hA
  | lenB => exact absurd rfl hB
  | _ => exact ⟨h0, h1⟩

private theorem ok_lens {c : IxCtl} (h0 : c.l0 = lenWA P L (g / L.block))
    (h1 : c.l1 = lenWB P L (g / L.block)) : ixLenOk P L g (ofC (ixLens c)) := by
  obtain ⟨k0, k1, kA, kB⟩ := kw_lens c
  exact ok_of kA kB (k0.trans h0) (k1.trans h1)

/-- After the top-k length (the parameter or the loaded word `a`). -/
private theorem ok_afterA {c : IxCtl} (h0 : c.l0 = lenWA P L (g / L.block))
    (h1 : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true → c.l1 = lenWB P L (g / L.block)) :
    ixLenOk P L g (ofC (ixAfterA P c)) := by
  unfold ixAfterA
  split
  · exact ok_lens h0 (h1 ‹_›)
  · rename_i h
    exact ⟨by simpa using h, h0⟩

/-- The index warp's first state. -/
theorem ix_ok_init (hp : Pre P L m) : ixLenOk P L g (ofC (ixFirst P L g)) := by
  unfold ixFirst
  simp only [batch_in hp g, Bool.false_eq_true, ite_false]
  split
  · rename_i hA
    exact ok_afterA (by simp only [lenWA, hA, ite_true]) fun hB => by
      simp only [lenWB, hB, ite_true]
  · rename_i h
    exact ⟨by simpa using h, rfl⟩

/-- **The thread state behind an index event.** -/
theorem ix_fired (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Index.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n))) :
    ∃ t ins o, (Index.code P L g).AtD d t ∧ (Index.code P L g).inv d ∧
      kernel.code[(Index.code P L g).pc d]? = some ins ∧
      Fires ((Index.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  exact ⟨t, ins, o, hat, hi.1, hc, hf⟩

/-- **A step keeps `ixLenOk`**, in a consistent execution (the length loads read the row's
words). -/
private theorem ix_ok_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d d' : Index.D} {n : Cls → Nat} {i : Nat} {f : Event}
    (hσ : Frame.stateAt (thread P L) X g i =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)))
    (hf : (X.tr g)[i]? = some f) (hok : ixLenOk P L g d) (h : succ P L g d f = some (some d')) :
    ixLenOk P L g d' := by
  have hget : X.get (g, i) = some f := hf
  have nc {s : IxSite} (hs : d.site = s) (hs' : s = .lenA ∨ s = .lenB) : ∀ fl, f.kind ≠ .ub fl := by
    intro fl hk
    rcases hs' with rfl | rfl <;> simp [succ, lenNext, hs, hk] at h
  by_cases hA : d.site = .lenA
  · obtain ⟨t, ins, o, hat, hi, hc, hf'⟩ := ix_fired hp hX hget (nc hA (.inl rfl)) hσ
    have hok' := hok
    simp only [ixLenOk, hA] at hok'
    rw [ix_topk hp hX hget hat hi hc hf' hok'.1 hA, Option.some.injEq, Option.some.injEq] at h
    subst h
    refine ok_afterA (by simp [lenWA, hok'.1, rowOf_cta]) fun hB => ?_
    simp only [lenWB, hB, ite_true]
    exact hok'.2
  by_cases hB : d.site = .lenB
  · obtain ⟨t, ins, o, hat, hi, hc, hf'⟩ := ix_fired hp hX hget (nc hB (.inr rfl)) hσ
    have hok' := hok
    simp only [ixLenOk, hB] at hok'
    rw [ix_extra hp hX hget hat hi hc hf' hok'.1 hB, Option.some.injEq, Option.some.injEq] at h
    subst h
    exact ok_lens hok'.2 (by simp [lenWB, hok'.1, rowOf_cta])
  obtain ⟨k0, k1, kA, kB⟩ := words_step h hA hB
  obtain ⟨w0, w1⟩ := ix_words_of hA hB hok
  exact ok_of kA kB (k0.trans w0) (k1.trans w1)

/-- Only lanes `0 mod 4` reach the validity byte's store. -/
def IxSkip (L : Launch) (g : Nat) (d : Index.D) : Prop :=
  d.site = .bA ∨ d.site = .bB → ixSkipB L g = false

/-- A site before a block's poll is no validity byte's store. -/
private theorem skip_of_zero {d : Index.D} (h : incW d.site = 0) : IxSkip L g d := by
  rintro (h' | h') <;> simp [h', incW] at h

/-- A site other than the validity byte's store. -/
private theorem skip_ne {d : Index.D} (h1 : d.site ≠ .bA) (h2 : d.site ≠ .bB) : IxSkip L g d := by
  rintro (h | h) <;> simp_all

private theorem w_lens (c : IxCtl) : incW (ixLens c).1 = 0 := by
  unfold ixLens
  dsimp only
  split
  · obtain ⟨-, -, h⟩ := zero_noMain { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 }
    exact h
  · rfl

private theorem w_afterA (c : IxCtl) : incW (ixAfterA P c).1 = 0 := by
  unfold ixAfterA
  split
  · exact w_lens c
  · rfl

/-- A length load's successor is its continuation at the loaded word. -/
private theorem len_succ {f : Event} {F : BitVec 64 → Index.D} {d' : Index.D}
    (h : lenNext f F = some (some d')) : ∃ x, d' = F x := by
  unfold lenNext at h
  split at h
  · unfold Code.ncNext at h
    split at h
    · simp only [Option.some.injEq] at h
      exact ⟨_, h.symm⟩
    all_goals cases h
  · cases h

/-- **The validity byte's store is reached only through `afterSt`.** -/
private theorem skip_step {d d' : Index.D} {f : Event} (hs : IxSkip L g d)
    (h : succ P L g d f = some (some d')) : IxSkip L g d' := by
  obtain ⟨site, el, ac, c⟩ := d
  have hz : ∀ p : IxSite × IxCtl, incW p.1 = 0 → IxSkip L g (ofC p) := fun _ h => skip_of_zero h
  have hpair : ∀ {s : IxSite} {nx : BitVec 64 → BitVec 64 → Index.D}, s ≠ .bA → s ≠ .bB →
      (∀ y0 y1, IxSkip L g (nx y0 y1)) → ncPair f ⟨s, el, ac, c⟩ nx = some (some d') →
      IxSkip L g d' := by
    intro s nx h1 h2 hn h
    obtain ⟨y, rfl⟩ := ncPair_some h
    rcases ldNext_cases ⟨s, el, ac, c⟩ y nx with ⟨h3, -⟩ | ⟨y0, y1, h3⟩
    · exact skip_ne (by rw [h3]; exact h1) (by rw [h3]; exact h2)
    · rw [h3]
      exact hn y0 y1
  have hpoll : ∀ {s t : IxSite}, s ≠ .bA → s ≠ .bB → t ≠ .bA → t ≠ .bB →
      poll f ⟨s, el, ac, c⟩ t = some (some d') → IxSkip L g d' := by
    intro s t h1 h2 h3 h4 h
    simp only [poll] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · exact skip_ne h3 h4
      · exact skip_ne h1 h2
    · cases h
  cases site <;> simp only [succ] at h
  · obtain ⟨x, rfl⟩ := len_succ h
    exact hz _ (w_afterA _)
  · obtain ⟨x, rfl⟩ := len_succ h
    exact hz _ (w_lens _)
  · exact hpair (by decide) (by decide) (fun y0 y1 => by
      obtain ⟨-, -, hw⟩ := zero_afterPre { c with m0 := y0, m1 := y1 }
      exact hz _ hw) h
  · exact hpair (by decide) (by decide) (fun _ _ => hz _ rfl) h
  · exact hpoll (by decide) (by decide) (by decide) (by decide) h
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact skip_ne (by simp) (by simp)
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact skip_ne (by simp) (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    rcases stNext_cases ⟨.stA, el, ac, c⟩ (ofC (afterSt L g .bA .arrA, c)) with ⟨h3, -⟩ | h3
    · exact skip_ne (by rw [h3]; simp) (by rw [h3]; simp)
    · rw [h3]
      unfold afterSt
      split
      · exact skip_ne (by simp) (by simp)
      · intro _
        simp_all
  · simp only [Option.some.injEq] at h
    subst h
    exact skip_ne (by simp) (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, hw, -⟩ := keeps_mainEnd c
    exact hz _ hw
  · exact hpair (by decide) (by decide) (fun y0 y1 => by
      obtain ⟨-, -, hw, -⟩ := keeps_afterXpre { c with e0 := y0, e1 := y1 }
      exact hz _ hw) h
  · exact hpair (by decide) (by decide) (fun _ _ => hz _ rfl) h
  · exact hpoll (by decide) (by decide) (by decide) (by decide) h
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact skip_ne (by simp) (by simp)
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact skip_ne (by simp) (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    rcases stNext_cases ⟨.stB, el, ac, c⟩ (ofC (afterSt L g .bB .arrB, c)) with ⟨h3, -⟩ | h3
    · exact skip_ne (by rw [h3]; simp) (by rw [h3]; simp)
    · rw [h3]
      unfold afterSt
      split
      · exact skip_ne (by simp) (by simp)
      · intro _
        simp_all
  · simp only [Option.some.injEq] at h
    subst h
    exact skip_ne (by simp) (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, hw, -⟩ := keeps_xEnd c
    exact hz _ hw
  · simp only [Option.some.injEq] at h
    subst h
    exact skip_ne (by simp) (by simp)
  · cases h

/-- The index states with `ixLenOk` at an element of their site. -/
def IxR (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  ∀ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) →
    ixLenOk P L g d ∧ d.el < d.site.elems ∧ IxSkip L g d

/-- Warpgroup 1's head enters the index warp at its first state. -/
private theorem enter_sub (hp : Pre P L m) {p : (wg1HeadCode P L g).D} {d : Index.D}
    (h : Code.enter (wg1HeadCode P L g) (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
      (Code.gatedExit (wg1Enter P L g) (subSel P L g)) p = .inr ⟨.inl .index, d⟩) :
    ixLenOk P L g d ∧ d.el < d.site.elems ∧ IxSkip L g d := by
  unfold Code.enter at h
  split at h
  · rename_i i _
    simp only [Sum.inr.injEq] at h
    cases i with
    | inl e =>
      cases e <;> simp only [Sigma.mk.inj_iff, Sum.inl.injEq, reduceCtorEq, false_and] at h
      obtain ⟨-, h2⟩ := h
      cases eq_of_heq h2
      obtain ⟨-, -, hz⟩ := zero_first P L g
      exact ⟨ix_ok_init hp, IxSite.elems_pos _, skip_of_zero hz⟩
    | inr r => simp at h
  · simp at h

/-- The startup enters warpgroup 1 at its first state. -/
private theorem enter_top (hp : Pre P L m) {s : (startupCode P L g).D} {d : Index.D}
    {n n' : Cls → Nat}
    (h : (Code.enter (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) s, n) =
      (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n')) :
    ixLenOk P L g d ∧ d.el < d.site.elems ∧ IxSkip L g d := by
  unfold Code.enter at h
  split at h
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at h
    obtain ⟨h1, -⟩ := h
    rename_i i _
    cases i with
    | inl e =>
      cases e <;> simp only [Sigma.mk.inj_iff, Sum.inl.injEq, reduceCtorEq, false_and] at h1
      obtain ⟨-, h2⟩ := h1
      exact enter_sub hp (eq_of_heq h2)
    | inr r => simp at h1
  · simp at h

/-- **The index warp's states have `ixLenOk`**, at an element of their site. -/
theorem ix_ok (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) : IxR P L g σ := by
  refine region_stays_ev (IxR P L g) (j := 0) ?_ (Frame.stateAt_zero ..) ?_ k
    (Nat.zero_le k) σ hσ
  · rintro i ⟨s | ⟨r, x⟩, n⟩ σ' f - hσi hR hf hn d' n' rfl
    · simp only [Code.toMachine, Code.glue] at hn
      cases hs : Startup.succ L g s f with
      | none => simp [hs] at hn
      | some o =>
        cases o with
        | none => simp [hs] at hn
        | some s' =>
          simp only [hs, Option.map_some, Option.some.injEq] at hn
          exact enter_top hp hn
    · simp only [Code.toMachine, Code.glue] at hn
      cases hs : (Code.withStubs (frag P L g) Entry.pc r).next x f with
      | none => simp [hs] at hn
      | some o =>
        cases o with
        | none => simp [hs] at hn
        | some a =>
          simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq,
            Sigma.mk.inj_iff] at hn
          obtain ⟨⟨rfl, ha⟩, -⟩ := hn
          cases eq_of_heq ha
          rcases x with h0 | ⟨j, d⟩
          · simp only [Code.withStubs, frag, wg1Code, Code.roleLoop, Code.loopGlue,
              Option.map_eq_some_iff] at hs
            obtain ⟨a, -, a1, rfl, ha⟩ := hs
            exact enter_sub hp ha
          · simp only [Code.withStubs, frag, wg1Code, Code.roleLoop, Code.loopGlue,
              Option.map_eq_some_iff] at hs
            obtain ⟨a, hj, a1, rfl, ha⟩ := hs
            unfold Code.backEnter at ha
            split at ha
            · exact enter_sub hp ha
            · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at ha
              obtain ⟨rfl, h2⟩ := ha
              cases eq_of_heq h2
              obtain ⟨hok, hel, hsk⟩ := hR _ _ rfl
              exact ⟨ix_ok_step hp hX hσi hf hok hj, el_step hj hel, skip_step hsk hj⟩
  · rintro d n h
    exact enter_top (s := (startupCode P L g).init) (n := fun _ => 0) hp h

/-- **The index lane's block count is the CTA's**: away from the length loads the blocks of its
recorded words are `blocksOf P L (g / L.block)`. -/
theorem ix_rounds (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Index.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)))
    (hA : d.site ≠ .lenA) (hB : d.site ≠ .lenB) :
    roundsOf d.c.l0 d.c.l1 = blocksOf P L (g / L.block) := by
  obtain ⟨h0, h1⟩ := ix_words_of hA hB (ix_ok hp hX hσ d n rfl).1
  rw [h0, h1]
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
