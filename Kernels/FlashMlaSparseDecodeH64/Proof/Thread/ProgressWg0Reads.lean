-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressData
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Data
import Lemmas.Flow.Next

public section

/-! # Counted ordinary reads of the softmax role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The ordinary shared reads of softmax. -/
inductive SoftmaxReadSite : Wg0.Site → Prop where
  | maskRead : SoftmaxReadSite .maskRead
  | peerRead (j : Fin 8) : SoftmaxReadSite (.peerRead j)
  | maxRead : SoftmaxReadSite .maxRead
  | lseRead : SoftmaxReadSite .lseRead

private def IsSharedLoad (a : MemAccess) :=
  ∃ base width, a.rule = some .threadAccess ∧ a.locSpace? = some .shared ∧
    a.addr.base = .reg base width ∧ a.kind = .load ∧ a.sem = .weak ∧ a.nc = false

private theorem wg0_load_code {s : Wg0.Site} (hd : SoftmaxReadSite s) :
    ∃ a, kernel.code[s.pc]? = some ⟨none, .mem a⟩ ∧ IsSharedLoad a ∧ UbWg0.DataSite s := by
  cases hd with
  | maskRead =>
    exact ⟨_, Flow.code_289, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | peerRead j =>
    fin_cases j
    · exact ⟨_, Flow.code_477, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_482, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_487, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_492, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_497, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_502, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_507, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · exact ⟨_, Flow.code_512, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | maxRead =>
    exact ⟨_, Flow.code_572, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  | lseRead =>
    exact ⟨_, Flow.code_1157, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

private theorem wg0_load_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg0.D} {u : TState} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hd : SoftmaxReadSite d.site) (ha : (Wg0.code P L g).AtD d u) (hi : Wg0.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ a k, eventTmpl Assumptions.all L g u ins.op = .read a k := by
  obtain ⟨ma, hcode, ⟨base, width, hr, hl, hb, hk, hs, hnc⟩, hData⟩ := wg0_load_code hd
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hn := UbWg0.data_tmpl_ok hpre hg ha hi hc hData
  rw [eventTmpl, memTmpl_direct_weakLoad hr hl hb hk hs, hnc] at hn ⊢
  rcases loadTmpl_cases (A := Assumptions.all) (L := L) (g := g) (t := u)
      (sp := .shared) (w := ma.elem.width) (ds := ma.regs) (base := base)
      (off := ma.addr.off) with ⟨f, h⟩ | ⟨a, h⟩
  · exact (hn f h).elim
  · exact ⟨a, _, h⟩

/-- The pending ordinary read has a defined shared-memory template. -/
theorem softmax_read_out {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {t : TState} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hg : g < L.threads) (hr : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxReadSite d.site) :
    ∃ u a k, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      out kernel Assumptions.all L g u = .ev (.read a k) := by
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hg hr hσ
  obtain ⟨a, k, hRead⟩ := wg0_load_template hpre hg hd ha hi hc
  rw [hRead] at hout
  exact ⟨u, a, k, hTau, hout⟩

/-- A released softmax lane can append its ordinary read with consistent read sources. -/
theorem softmax_read_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hsg : SyncGuarded L kernel X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxReadSite d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, a, k, hTau, hout⟩ := softmax_read_out hpre hs hp.1 hRun hσ hd
  exact shared_read_extension hX hp.1 hne hrel hRun hTau hout hsg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
