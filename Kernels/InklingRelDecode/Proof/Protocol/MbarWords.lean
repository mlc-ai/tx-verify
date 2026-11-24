-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPro
public import Kernels.InklingRelDecode.Proof.Interface.TmCode

@[expose] public section

/-!
# The prologue's loaded words are the request's (`ProWordsMatch`)

The premise of `Interface.early_stores_same`: at the prologue's early stores (`st8`, `st9_0`,
`st9_1`) the three words the prologue loaded (`cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`,
`seq_lens[req]`) are the request's (`ProA.WordsMatch`). In an execution whose machines follow
every thread every read of an input byte returns the launch byte (`launchRead_of_facts`), so
`WordsSo` holds at every state (`wordsSo_all`, from `Interface.wordsSo_all_at`).
`proWordsMatch` is the statement `Interface.ProWordsMatch` exactly.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mbar
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every read of an input byte returns the launch byte** when the machines follow every
thread: a source write is a write of a followed thread (`read_launch_src`). -/
theorem launchRead_of_facts (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : ∀ e, LaunchRead Q mem0 X e := by
  intro e pc a bs he hsp hcta k hk hrd
  have hr : X.MemReads (.thread e) a bs := Or.inl ⟨pc, he⟩
  refine read_launch_src hpre hX hf.sound hr hsp hcta hk hrd ?_
  intro w hw g n hwn
  subst hwn
  have hrf := (hX.rf _ a bs hr).2 k hk
  rw [hw] at hrf
  obtain ⟨a', bs', hw', -, -⟩ := hrf
  rcases hw' with ⟨pc', hh⟩ | ⟨old, pc', hh⟩
  · exact event_state_at hf.sound hX hh (by intro pc f h; cases h)
      (hf.tracked g (n + 1) (Frame.lt_of_get hX hh))
  · exact absurd hh (no_rmw hX)

/-- **The earlier events of a followed thread are `Good`** when the machines follow every
thread. -/
theorem good_before (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {s : TSt} (hσ : St Q L X g k = some (some s)) :
    ∀ j < k, Good Q L mem0 X (g, j) := by
  intro j hj
  refine ⟨fun hn => ?_, launchRead_of_facts hpre hX hf _⟩
  have := someNone_mono hn (show j + 1 ≤ k by omega)
  have hσ' : Frame.stateAt (code L Q) X g k = some (some s) := hσ
  rw [hσ'] at this
  cases this

/-- **A word load returns the launch's word** (`Interface.loaded_word_at`). -/
theorem loaded_word (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc A x : Nat} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd (EvD.wordAcc ⟨.global, 0, A⟩) bs⟩)
    (hx32 : x < 2 ^ 32)
    (hx : ∀ j < 4, Q.reads (A + j) ∧ mem0 ⟨.global, 0, A + j⟩ = some (some (i32Byte x j)))
    {a' : Acc} {bs' : List (Option Byte)} {v : Value} {x' : Nat}
    (hk : (⟨pc, .rd (EvD.wordAcc ⟨.global, 0, A⟩) bs⟩ : Event).kind = .rd a' bs')
    (hrb : rebuild 3 bs' = .ok v) (hw : ProA.word32 v = some x') : x' = x :=
  loaded_word_at hX (launchRead_of_facts hpre hX hf _) he hx32 hx hk hrb hw

/-- **The request words are the request's at every state of a thread.** -/
theorem wordsSo_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → WordsSo Q L g s := by
  intro k s hσ
  exact wordsSo_all_at hpre hX hf.sound (tmplOk hpre) k s hσ (good_before hpre hX hf hσ)

/-- **`Interface.ProWordsMatch`**: at the prologue's early stores the three loaded words are the
request's. -/
theorem proWordsMatch (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : ProWordsMatch Q L X := by
  intro g k d hσ hE
  have hI := wordsSo_all hpre hX hf k _ hσ
  obtain ⟨h0, h1, h2⟩ := hI
  have hk : d.site.afterSk = true := by
    rcases hE with h | h | h <;> rw [h] <;> rfl
  refine ⟨h0 ?_ ?_, h1 (Or.inl hk), h2 hk⟩ <;>
    (intro h; rw [h] at hk; simp [ProA.Site.afterSk] at hk)

end
end PTX.Kernels.InklingRelDecode.Proof.Mbar
