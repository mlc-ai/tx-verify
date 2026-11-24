-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Thread.ShapeSameValue

@[expose] public section

/-!
# The early shared words are written with one value

The default partition's threads each store the role table (`ProA.Site.st8`) and the pair
`(num_pre, num_iters)` (`st9_0`, `st9_1`) into the CTA's shared window. Two store events of one
such site from two threads of one CTA are the same event: the same footprint and the same bytes
(`early_stores_same`, from `ProA.early_store_same`), so they are two writes of the same value
(`SameValueWrites`), and the safety layer does not have to order them.

The one premise is `ProWordsMatch`: at the prologue's store sites the three words the prologue
loaded (`cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`) are the request's. The
machine only follows the thread past the `bar.sync 1` after the stores if they are
(`DComp.proNext`), so it does not give the words at the stores themselves; it is the reads-from
fact of `Pre.cuInput` and `Pre.seqInput`, owed by the protocol layer (a row of "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The loaded words are the request's at the early stores.** At a prologue state at a store of
the early shared words, the three loaded words are the request's own. -/
def ProWordsMatch (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : ProA.D}, St Q L X g k = some (some (.d (.pro d))) →
    ProA.EarlySite d.site → ProA.WordsMatch Q (ProA.cta L g .z) d.dt

/-- **Two stores of an early shared word by two threads of one CTA write the same value.** Two
events of threads of one CTA, at prologue states at the same early store site, are the same write
event. -/
theorem early_stores_same (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hw : ProWordsMatch Q L X) {g k g' k' : Nat} {e e' : Event}
    {d d' : ProA.D} (he : X.get (g, k) = some e) (he' : X.get (g', k') = some e')
    (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hσ' : St Q L X g' k' = some (some (.d (.pro d'))))
    (hsite : d.site = d'.site) (hE : ProA.EarlySite d.site) (hc : g / L.block = g' / L.block) :
    (∃ pc a bs, e = ⟨pc, .wr a bs⟩) ∧ e = e' := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hg' : g' < L.threads := Frame.lt_of_get hX he'
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨u', hF'⟩ := fired_cont hX hf hg' he' hσ' (by simp [ExitState])
  obtain ⟨hdef, tm, -, hpro⟩ := hf.reach hg hσ
  obtain ⟨hdef', tm', -, hpro'⟩ := hf.reach hg' hσ'
  exact ⟨ProA.early_store_wr (fired_pro hF) hE,
    ProA.early_store_same hpre hg hg' hdef hdef' hpro hpro' (hw hσ hE)
      (hw hσ' (hsite ▸ hE)) (fired_pro hF) (fired_pro hF') hsite hE hc⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
