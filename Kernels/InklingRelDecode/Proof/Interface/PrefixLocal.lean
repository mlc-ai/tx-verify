-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixOrder
public import Kernels.InklingRelDecode.Proof.Interface.Reads
public import Kernels.InklingRelDecode.Proof.Interface.OutputFrame

@[expose] public section

/-!
# The local form of the thread facts used by the prefix induction

The lemmas of `Output.lean`, `OutputFrame.lean` and `Reads.lean` take `ThreadFacts`, which contains
`Frame.Tracked`, the statement that every thread of the execution is followed by its machine at
every event. The prefix induction (`PrefixOrder.lean`) proves that statement, so it cannot use
them. Here are their forms that ask for the tracking of the one write they are about:

* `event_state_at`: an event that is not undefined behaviour and that the machine tracked through
  is fired from a followed state;
* `global_wr_at`: a global write whose thread's machine is at a state before it is an epilogue
  store (`global_wr_state` with the state given);
* `write_in_arrays_at`: a global write by a thread tracked through the write covers a byte of
  `OPart` or `LsePart` only;
* `read_launch_src`: a read of an input byte whose reads-from source, if it is a write, is a thread
  write that its machine tracked through, returns the launch byte.

Nothing here is about the other events of the execution.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

/-- The machine of thread `g` is tracked through its event `k`: it follows the thread after the
event (it may be dead, which only an undefined-behaviour event after it can tell). -/
def TT (Q : Params) (L : Launch) (X : Execution) (e : EvId) : Prop :=
  St Q L X e.1 (e.2 + 1) ≠ some none

/-- Tracked through an event is tracked before it. -/
theorem TT.before {e : EvId} {ev : Event}
    (hg : g = e.1) (he : X.get e = some ev) (h : TT Q L X e) :
    St Q L X g e.2 ≠ some none := by
  subst hg
  intro hn
  apply h
  have he' : (X.tr e.1)[e.2]? = some ev := he
  have := Frame.stateAt_succ (C := code L Q) (X := X) (g := e.1) (k := e.2) he'
  have hn' : Frame.stateAt (code L Q) X e.1 e.2 = some none := hn
  rw [hn'] at this
  exact this

/-- **An event the machine tracked through, which is not undefined behaviour, is fired from a
followed state.** -/
theorem event_state_at (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (h : TT Q L X (g, k)) :
    ∃ d, St Q L X g k = some (some d) := by
  have hn := TT.before rfl he h
  rcases Frame.fired hS hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hσ hn
    | some d => exact ⟨d, hσ⟩
  · exact absurd rfl (hub pc f)

theorem global_wr_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    {g k pc : Nat} {a : Acc} {bs : List Byte} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) {s : TSt}
    (hσ : St Q L X g k = some (some s)) (hsp : a.loc.space = .global) :
    ∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ pc = Epi.evPc d.site ∧
      Epi.Means Q L g d.pr ∧ d.pr.rv = true ∧
      ((∃ j : Fin 64, d.site = .stO j ∧ ∃ v, storeValue 32 (d.word j) = .ok v ∧
          bs = v.toBytes ∧ a = EvD.wordAcc (oLoc Q (Epi.outSplit L g) (Epi.outToken Q L g)
            (Epi.outHead L g) (Epi.outCol0 L g + j.val))) ∨
        (d.site = .stLse ∧ ∃ v, storeValue 32 d.pr.lseWord = .ok v ∧ bs = v.toBytes ∧
          a = EvD.wordAcc (lseLoc Q (Epi.outSplit L g) (Epi.outToken Q L g)
            (Epi.outHead L g)))) := by
  have hk : (⟨pc, .wr a bs⟩ : Event).kind = .wr a bs := rfl
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


/-- **A global write by a thread tracked through the write is inside an output array.** -/
theorem write_in_arrays_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs)
    (hsp : a.loc.space = .global) {l : Loc} (hc : a.Covers l)
    (htr : ∀ g n, w = .thread (g, n) → ∃ s, St Q L X g n = some (some s)) :
    (Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) ∨
      (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q) := by
  obtain ⟨g, n, pc, rfl, hget⟩ := global_write_thread hX hw hsp
  have hg := Frame.lt_of_get hX hget
  obtain ⟨s, hσ⟩ := htr g n rfl
  obtain ⟨d, -, -, hm, hrv, hcases⟩ := global_wr_at hpre hX hS hg hget hσ hsp
  obtain ⟨hx, -, ht', hh⟩ := Epi.row_coords hpre hg hm hrv
  obtain ⟨-, -, h1, h2⟩ := hc
  rcases hcases with ⟨j, -, v, -, -, hacc⟩ | ⟨-, v, -, -, hacc⟩
  · subst hacc
    have hd : Epi.outCol0 L g + j.val < headDim := by
      have : Epi.halfM (g % L.block) ≤ 1 := by unfold Epi.halfM; omega
      have := j.isLt
      unfold Epi.outCol0 headDim
      omega
    have := oLoc_range (Q := Q) (Epi.outSplit L g) (Epi.outToken Q L g) (Epi.outHead L g) _ hx ht'
      hh hd
    left
    simp only [EvD.wordAcc] at h1 h2
    omega
  · subst hacc
    have := lseLoc_range (Q := Q) (Epi.outSplit L g) (Epi.outToken Q L g) (Epi.outHead L g) hx
      ht' hh
    right
    simp only [EvD.wordAcc] at h1 h2
    omega

/-- **A read of an input byte returns the launch byte, if its source is tracked.** The read's
source for the byte is the initial write, or a write; the global writes of the kernel are the
epilogue's stores, and a store by a thread tracked through it is inside an output array, which no
input byte is in (`Pre.outputsApart`). -/
theorem read_launch_src (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (hr : X.MemReads e a bs) (hsp : a.loc.space = .global)
    (hcta : a.loc.cta = 0) {k : Nat} (hk : k < a.size) (hrd : Q.reads (a.loc.at k).addr)
    (hsrc : ∀ w, X.rf e k = some w → ∀ g n, w = .thread (g, n) →
      ∃ s, St Q L X g n = some (some s)) :
    ∃ c, mem0 (a.loc.at k) = some (some c) ∧ bs[k]? = some (some c) := by
  have heq : a.loc.at k = ⟨.global, 0, (a.loc.at k).addr⟩ := by
    simp only [Loc.at, hsp, hcta]
  obtain ⟨c, hc⟩ : ∃ c, mem0 (a.loc.at k) = some (some c) := by
    obtain ⟨c, hc⟩ := reads_mem0 hpre hrd
    exact ⟨c, by rw [heq]; exact hc⟩
  refine ⟨c, hc, ?_⟩
  have hrf := (hX.rf e a bs hr).2 k hk
  cases hs : X.rf e k with
  | none =>
    rw [hs] at hrf
    rw [hrf _ hc]
    rfl
  | some w =>
    rw [hs] at hrf
    obtain ⟨a', bs', hw, hcov, -⟩ := hrf
    exfalso
    have hsp' : a'.loc.space = .global := hcov.1.symm.trans (by simpa [Loc.at] using hsp)
    have hap := hpre.outputsApart _ hrd
    rcases write_in_arrays_at hpre hX hS hw hsp' hcov (hsrc w hs) with h | h
    · exact hap.1 h
    · exact hap.2 h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
