-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.AccTiles
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemDefs
public import Lemmas.Flow.EndSite

@[expose] public section

/-! # A consumer's warp-collective `tcgen05` events at its trace's end

The warp-collective `tcgen05` events of a thread are its paired Tensor Memory operations and its
data events (loads, stores and their waits). A consumer's data events at its trace's end are the
thirty-two per accumulator it has released, plus its position in the tile it is loading
(`TcTile`, a conjunct of `ConsInv`); the accumulators it has released are its accumulator-full
polls less the one it holds. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A thread's warp-collective `tcgen05` events are its paired Tensor Memory operations and its data
events. -/
theorem tcColl_count (es : List Event) : es.countP isTcColl = tmemOps es + dataOps es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.countP_cons, tmemOps, dataOps] at ih ⊢
    obtain ⟨pc, k⟩ := e
    cases k <;> first
      | (simp [isTcColl, isTmemOp, isTcData]; omega)
      | rename_i k
        cases k <;> simp [isTcColl, isTmemOp, isTcData] <;> omega

/-- **A consumer's warp-collective `tcgen05` events at its trace's end.** -/
theorem cons_tc_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) :
    (X.tr g).countP isTcColl + 32 * Consumer.holds c =
      tmemOps (X.tr g) + 32 * consCount L g (X.tr g) + c.tcPos := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have h3 := consInv hpre hg htr (X.tr g).length _ hσ
  rw [List.take_length] at h3
  have h4 : Consumer.TcTile L g c (X.tr g) := h3.2.2.2.2.2.2.1
  have h5 := Consumer.cons_acc_count hpre hX hg hσ
  unfold Consumer.TcTile at h4
  rw [tcColl_count]
  omega

/-- **A consumer's state after a data event is in its task loop**: the successors of a load and of
a wait are a wait, a load and the accumulator release; no other role's state and no prologue state
fires a data event. -/
theorem cons_after_tc_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {e : Event}
    {d0 : ThreadD} {c : Consumer.D} (he : X.get (g, k) = some e) (hd : isTcData e = true)
    (hσ0 : Frame.stateAt (code L) X g k = some (some d0))
    (hσ1 : Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c)))) :
    Consumer.exitOff c = none ∧ c.site ≠ .setMaxReg := by
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ0
  have hn : (code L g).next d0 e = some (some (.inr (.cons c))) := by
    have h1 := Frame.stateAt_succ (C := code L) he
    rw [hσ0] at h1
    rw [h1] at hσ1
    exact hσ1
  rcases d0 with p | (l | m | s | c0)
  · change kernel.code[p.site.pc]? = some ins at hc
    change Fires p.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
    exact absurd hd (by simp [Prologue.not_tcData hc hfire])
  · obtain ⟨l', -, h'⟩ := next_of_loader hn; cases h'
  · obtain ⟨m', -, h'⟩ := next_of_mma hn; cases h'
  · obtain ⟨s', -, h'⟩ := next_of_sched hn; cases h'
  · obtain ⟨c', hn', h'⟩ := next_of_cons hn
    cases h'
    change kernel.code[c0.site.pc]? = some ins at hc
    change Fires c0.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
    have hs := Consumer.data_site hc hfire hd
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c0
    rcases hs with ⟨s, hs⟩ | ⟨s, hs⟩ <;> simp only at hs <;> subst hs <;>
      simp only [Consumer.next] at hn' <;> (try split_ifs at hn') <;>
      (try split at hn') <;> simp at hn' <;> subst hn' <;> simp [Consumer.exitOff]

/-- **A consumer at a load's wait fires the wait**: its run reaches the wait instruction, whose
template is the wait event (the block is a multiple of the warp size). -/
theorem cons_wait_fire_fact (hpre : Pre P L mem0) (hg : g < L.threads) {c : Consumer.D} {t : TState}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))))
    (hs : ∃ j, c.site = .loadWait j) (hr : Run kernel Prod L g {} (X.tr g) (some t)) :
    ∃ t1 u, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨t1.pc, .tc .waitLd⟩ (some u) := by
  have hσ' : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
    some (some (.inr (.cons c))) := by
    have h := hσ
    simp only [Frame.stateAt, List.take_length] at h
    exact h
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ'
  have hout := Code.site_out (sound hpre hg) hgood
  obtain ⟨ins, hc, -, -⟩ := ((sound hpre hg).steps _).site hgood.2
  obtain ⟨j, hj⟩ := hs
  simp only [Code.tmpl, hc] at hout
  change kernel.code[c.site.pc]? = some ins at hc
  rw [hj] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_wait j))
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  refine ⟨t1, next t1, hl, _, hout, ?_⟩
  simp [eventTmpl, tcTmpl, hblk, ofExec, pure, Except.pure, Fires]

end
end PTX.Kernels.Fp16Gemm8192.Proof
