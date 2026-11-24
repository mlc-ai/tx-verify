-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWrite
import Kernels.FlashMlaSparseDecodeH64.Audit.PeerScores
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Data
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Flow.Async
import Lemmas.Flow.PollFacts

public section

/-! # Counted ordinary writes of the softmax role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The ordinary writes of softmax, including its final LSE and output staging. -/
inductive SoftmaxWriteSite : Wg0.Site → Prop where
  | exchStore (j : Fin 8) : SoftmaxWriteSite (.exchStore j)
  | rowMax : SoftmaxWriteSite .rowMax
  | pStore (j : Fin 4) : SoftmaxWriteSite (.pStore j)
  | lseStore0 : SoftmaxWriteSite .lseStore0
  | lseStore : SoftmaxWriteSite .lseStore
  | oStage (j : Fin 4) (k : Fin 8) : SoftmaxWriteSite (.oStage j k)

private def IsWeakStore (a : MemAccess) :=
  ∃ sp base width, a.rule = some .threadAccess ∧ a.locSpace? = some sp ∧
    a.addr.base = .reg base width ∧ a.kind = .store ∧ a.sem = .weak

private theorem wg0_store_code {s : Wg0.Site} (hd : SoftmaxWriteSite s) :
    (∃ a, kernel.code[s.pc]? = some ⟨none, .mem a⟩ ∧ IsWeakStore a ∧ UbWg0.DataSite s) ∨
      ∃ j k, s = .oStage j k := by
  cases hd with
  | exchStore j =>
    refine .inl ⟨_, (Audit.peerPack_stores j).2, ?_, trivial⟩
    exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩
  | rowMax =>
    exact .inl ⟨_, Flow.code_566, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | pStore j =>
    refine .inl ?_
    fin_cases j
    · exact ⟨_, Flow.code_704, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_705, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_706, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_707, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | lseStore0 =>
    exact .inl ⟨_, Flow.code_1155, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | lseStore =>
    exact .inl ⟨_, Flow.code_1178, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | oStage j k =>
    exact .inr ⟨j, k, rfl⟩

private theorem wg0_store_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg0.D} {u : TState} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hd : SoftmaxWriteSite d.site) (ha : (Wg0.code P L g).AtD d u) (hi : Wg0.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ a bs v, a.release = false ∧ eventTmpl Assumptions.all L g u ins.op = .write a bs v := by
  rcases wg0_store_code hd with ⟨ma, hcode, hweak, hData⟩ | ⟨j, k, hsite⟩
  · obtain rfl := Option.some.inj (hc.symm.trans hcode)
    obtain ⟨sp, base, width, hr, hl, hb, hk, hs⟩ := hweak
    have hn := UbWg0.data_tmpl_ok hpre hg ha hi hc hData
    rw [eventTmpl, memTmpl_direct_weakStore hr hl hb hk hs] at hn ⊢
    rcases storeTmpl_cases (L := L) (g := g) (t := u) (sp := sp) (w := ma.elem.width)
      (base := base) (off := ma.addr.off) (srcs := ma.srcs) with ⟨f, h⟩ | ⟨a, bs, h⟩
    · exact (hn f h).elim
    · exact ⟨a, bs, _, storeTmpl_noRelease h, h⟩
  · have hcode := Wg0.stage_code j k
    rw [← hsite] at hcode
    obtain rfl := Option.some.inj (hc.symm.trans hcode)
    exact ⟨_, _, _, rfl, Wg0.event_oStage hpre hg ha hi hsite⟩

/-- The actual pending softmax write is weak and has a defined payload. -/
theorem softmax_write_out {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {t : TState} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hg : g < L.threads) (hr : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxWriteSite d.site) :
    ∃ u a bs v, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      a.release = false ∧ out kernel Assumptions.all L g u = .ev (.write a bs v) := by
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hg hr hσ
  obtain ⟨a, bs, v, hWeak, hWrite⟩ := wg0_store_template hpre hg hd ha hi hc
  rw [hWrite] at hout
  exact ⟨u, a, bs, v, hTau, hWeak, hout⟩

/-- A released softmax lane can append the ordinary write at its represented site. -/
theorem softmax_write_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxWriteSite d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, a, bs, v, hTau, hWeak, hout⟩ := softmax_write_out hpre hs hp.1 hRun hσ hd
  exact role_write_extension hpre hs hX ht hub hp.1 hrel hσ (fun _ h => by cases h)
    hRun hTau hWeak hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
