-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.PWords
public import Kernels.InklingRelDecode.Proof.Protocol.Values.Results
public import Kernels.InklingRelDecode.Proof.Iface.RescaleWords
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdoWord
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryTile
import Kernels.InklingRelDecode.Proof.Protocol.Values.PElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.StoreElement
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleWordsAt
import Kernels.InklingRelDecode.Proof.Top.Safe.ValEnv
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Lemmas.Tcgen05.ValuesByTcOrder

@[expose] public section

/-! # The rescale store writes numbers

One induction along the tcgen05 order (`Frame.values_by_tcStep`): the words of a rescale store are
the factor times the words of the accumulator load before it (`rescale_event`). The load's cells
were written by MMAs and rescale stores with a path to the load, and the MMAs' results are numbers
given the elements they read (`ld_o_word`), which include the words of the stores before them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The elements the MMAs read** are numbers, given the words of the rescale stores they read
(the probability words are proved). -/
theorem Safe.elementsOf (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) {Dom : EvId → Prop}
    (store : ∀ {i src cell old}, Dom i → X.MmaReadCell i cell → ReadSource L X .acc src i cell →
      StoreValue L X src cell old → ∃ r : ℝ, valFloat .f32 old = .ok r) : Elements Dom L X := by
  obtain ⟨base, words, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf safe rows init
  exact
    { b := fun _ hi _ hops hrow hk => elements_b hp hX hf rows init words hou nub form base hi hops
        hrow hk
      q := fun _ hi hat _ hops hrow hk => elements_q hp hX hf (query_tile hp hX hf words) base hi
        hat hops hrow hk
      p := fun _ hi hat _ hops hrow hk => p_element hp hX hf hou safe base rows init hG hws ht hmd
        (Safe.pWords hp hX hf hou safe rows init nub) hi hat hops hrow hk
      store := store }

/-- **The rescale store writes f32 numbers**, as `.float` words. -/
theorem Safe.rescaleFloat (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ {t sk a vals sh}, X.get (t, sk) = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r := by
  obtain ⟨base, words, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf safe rows init
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  have key := Frame.values_by_tcStep hX hG
    (fun i => ∀ {a vals sh}, X.get i = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) ?_
  · exact fun {t sk a vals sh} get => key (t, sk) _ get get
  intro ⟨g, k⟩ e he IH a vals sh get
  refine Softmax.Export.rescale_event hp hX
    (fun lane => Protocol.Shared.roundWords_ni hp hX hf hS lane) ?_ get
  intro j hj a' ov sh' hg x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have po : Relation.TransGen (TcStep L X) (g, j) (g, k) :=
    .single (.inl (.single (.inl (po_of_not_access rfl hj (List.getElem?_eq_some_iff.mp get).1
      (by simp [get, Event.acc])))))
  obtain ⟨r, hr⟩ := ld_o_word hp hX hf hou safe base rows init hG hws ht hmd hg (.inl rfl) hi
    (Safe.elementsOf hp hX hf hou safe rows init nub fun {i src cell old} hd hrd hs hv =>
      store_element hp hX hf hou hG safe base rows init hrd hs hv fun hst =>
        IH src _ hst (((readSource_acc.mp hs).2.2.1.tcStep.trans hd).trans po) hst)
    fun src hsrc _ _ _ hst => IH src _ hst (hsrc.trans po) hst
  rw [List.getElem?_eq_getElem hi] at hr
  exact ⟨r, Option.some.inj hr⟩

/-- **The rescale store writes numbers** (`Iface.RescaleWords`). -/
theorem Safe.rescaleWords (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) : Iface.RescaleWords X :=
  fun {_ _ _ _ _} get v hv =>
    let ⟨r, h⟩ := Safe.rescaleFloat hp hX hf hou safe rows init nub get v hv
    ⟨r, by rw [h]; rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
