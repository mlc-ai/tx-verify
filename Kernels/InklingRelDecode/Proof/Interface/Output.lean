-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Writes
public import Kernels.InklingRelDecode.Proof.Geometry
public import Lemmas.Kernel.Memory

@[expose] public section

/-!
# What the thread layer exports for the output stores

Every global write of an execution is a store of the default partition's epilogue. The statement
is about the abstract state of the thread before the event: `Frame.stateAt (code L Q) X g k` is
`.d (.epi d)` with `d.site` the store of `LsePart` (`Epi.Site.stLse`) or of word `j` of `OPart`
(`Epi.Site.stO j`), the epilogue's registers `d.pr` mean what `Epi.Means` says, the row is valid
(`d.pr.rv`), and the event is the shape `Epi.shape` gives, in the specification's terms: the
footprint is `Spec.oLoc`/`Spec.lseLoc` of the thread's split, token, head and column, and the
bytes are those of the word `Epi.D.word`/`Epi.Prm.lseWord` stores (`storeValue 32`).

* `global_wr_state`: the statement, from the thread machines' soundness, `Tracked`, and `Pre`.
* `no_other_global_writer` (`global_write_thread`): no atomic, copy or tensor store writes
  global memory, and a tensor load writes shared memory, so a global write of the execution is
  a thread's generic store.
* `global_write_in_arrays`, `post_frame`: every global write covers a byte of `OPart` or
  `LsePart`; every other global byte keeps its launch content (`Post`'s last conjunct).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

/-- The abstract state of thread `g` before its `k`-th event. -/
abbrev St (Q : Params) (L : Launch) (X : Execution) (g k : Nat) : Option (Option TSt) :=
  Frame.stateAt (code L Q) X g k

/-! ### An event fired from a component's state -/

theorem fired_epi {d : Epi.D} {e : Event} {o : Option TState}
    (h : (threadCode L g Q).toMachine.Fired (some (.d (.epi d))) e o) : Epi.Fired L g d e o := by
  obtain ⟨t, ⟨ha, hi⟩, hf⟩ := h
  exact ⟨t, ha, hi.2.1, hf⟩

theorem fired_pro {d : ProA.D} {e : Event} {o : Option TState}
    (h : (threadCode L g Q).toMachine.Fired (some (.d (.pro d))) e o) : ProA.Fired L g d e o := by
  obtain ⟨t, ⟨ha, hi⟩, hf⟩ := h
  exact ProA.Fired_of_machine (P := d.dt.pro) ⟨t, ⟨ha, hi.2.1⟩, hf⟩

theorem fired_sm {d : Sm.D} {e : Event} {o : Option TState}
    (h : (threadCode L g Q).toMachine.Fired (some (.d (.sm d))) e o) : Sm.Fired L g d e o := by
  obtain ⟨t, ⟨ha, hi⟩, hf⟩ := h
  exact ⟨t, ha, hi.2, hf⟩

/-- A continuing event is a fired event with a continuation: a write does not end the thread. -/
theorem fired_some {σ : Option TSt} {e : Event} {o : Option TState}
    (h : (threadCode L g Q).toMachine.Fired σ e o) {a : Acc} {bs : List Byte}
    (hk : e.kind = .wr a bs) : ∃ u, o = some u := by
  obtain ⟨t, -, hf⟩ := h
  cases o with
  | some u => exact ⟨u, rfl⟩
  | none =>
    exfalso
    rcases fires_none_ends hf with ⟨f, hf'⟩ | hx
    · rw [hk] at hf'
      cases hf'
    · rw [hk] at hx
      cases hx

/-- **A global write is an epilogue store** (the abstract statement). Thread `g`'s machine is,
before the event, at the epilogue's store of `LsePart` or of word `j` of `OPart`; the epilogue's
registers mean what `Epi.Means` says, the row is valid, and the event is the store of the
word, at the footprint of `Spec`. -/
theorem global_wr_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k pc : Nat} {a : Acc} {bs : List Byte} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hsp : a.loc.space = .global) :
    ∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ pc = Epi.evPc d.site ∧
      Epi.Means Q L g d.pr ∧ d.pr.rv = true ∧
      ((∃ j : Fin 64, d.site = .stO j ∧ ∃ v, storeValue 32 (d.word j) = .ok v ∧
          bs = v.toBytes ∧ a = EvD.wordAcc (oLoc Q (Epi.outSplit L g) (Epi.outToken Q L g)
            (Epi.outHead L g) (Epi.outCol0 L g + j.val))) ∨
        (d.site = .stLse ∧ ∃ v, storeValue 32 d.pr.lseWord = .ok v ∧ bs = v.toBytes ∧
          a = EvD.wordAcc (lseLoc Q (Epi.outSplit L g) (Epi.outToken Q L g)
            (Epi.outHead L g)))) := by
  have hk : (⟨pc, .wr a bs⟩ : Event).kind = .wr a bs := rfl
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (by intro pc f h; cases h)
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hpw : TSt.pc s ∈ writePcs := write_pc hc hf hk hsp
  have he' : (X.tr g)[k]? = some ⟨pc, .wr a bs⟩ := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  obtain ⟨u, rfl⟩ := fired_some hF hk
  have hr := treach_stateAt hpre hg hσ
  rcases write_state hpw with ⟨d, rfl, hsite⟩ | ⟨d, rfl, hsite⟩
  · have hFe := fired_epi hF
    have hm : Epi.Means Q L g d.pr := hr.2
    have hi : Epi.Inv d := hinv.2.1
    rcases hsite with hs | hs | ⟨j, hs⟩
    · have hrv : d.pr.rv = true := hi.rv (by rw [hs]; trivial)
      obtain ⟨v, hv, he2⟩ := Epi.shape_stLse_loc hpre hg hm hFe hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨h1, h2, h3⟩ := he2
      exact ⟨d, hσ, h1, hm, hrv, .inr ⟨hs, v, hv, h3, h2⟩⟩
    · obtain ⟨v, hv, he2⟩ := Epi.shape_stTab hFe hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      simp [EvD.wordAcc] at hsp
    · have hrv : d.pr.rv = true := hi.rv (by rw [hs]; trivial)
      obtain ⟨v, hv, he2⟩ := Epi.shape_stO_loc hpre hg hm hFe hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨h1, h2, h3⟩ := he2
      exact ⟨d, hσ, h1, hm, hrv, .inl ⟨j, hs, v, hv, h3, h2⟩⟩
  · have hFp := fired_pro hF
    rcases hsite with hs | hs | hs
    · obtain ⟨v, hv, he2⟩ := ProA.shape_st8 hFp hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      simp [EvD.wordAcc] at hsp
    · obtain ⟨v, hv, he2⟩ := ProA.shape_st9_0 hFp hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      simp [EvD.wordAcc] at hsp
    · obtain ⟨v, hv, he2⟩ := ProA.shape_st9_1 hFp hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      simp [EvD.wordAcc] at hsp

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
