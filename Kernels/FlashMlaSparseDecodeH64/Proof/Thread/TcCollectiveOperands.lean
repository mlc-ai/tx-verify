-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreBytes
import Lemmas.Flow.Final
import Lemmas.Flow.NotTcData

public section

/-! # Static operands of the Tensor Memory warp-collective sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcCollectiveSites

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The static operands of a data collective come from the column and shape of its site. -/
@[expose] def dataOperands : Wg0.Site → Option TcKind
  | .scoreLoad _ k => some (.ld (400 + 32 * k.val) [] .s32x32b)
  | .rescaleLoad j | .oLoad j => some (.ld (64 * j.val) [] .s32x32b)
  | .rescaleStore j => some (.st (64 * j.val) [] .s32x32b)
  | .scoreWait | .rescaleWait _ | .oWait _ => some .waitLd
  | .rescaleWaitSt _ => some .waitSt
  | _ => none

private theorem waitLd_code {s : Wg0.Site}
    (hs : s = .scoreWait ∨ (∃ j, s = .rescaleWait j) ∨ ∃ j, s = .oWait j) :
    kernel.code[s.pc]? = some ⟨none, .tcWaitLd⟩ := by
  rcases hs with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact Flow.code_286
  · fin_cases j
    · exact Flow.code_717
    · exact Flow.code_818
    · exact Flow.code_919
    · exact Flow.code_1020
  · fin_cases j
    · exact Flow.code_1202
    · exact Flow.code_1362
    · exact Flow.code_1520
    · exact Flow.code_1677

private theorem waitSt_code (j : Fin 4) :
    kernel.code[(Wg0.Site.rescaleWaitSt j).pc]? = some ⟨none, .tcWaitSt⟩ := by
  fin_cases j
  · exact Flow.code_815
  · exact Flow.code_916
  · exact Flow.code_1017
  · exact Flow.code_1118

private theorem rescale_attribute {s : Wg0.Site}
    (hs : (∃ j, s = .rescaleLoad j) ∨ ∃ j, s = .rescaleStore j) :
    ∃ ins, kernel.code[s.pc]? = some ins := by
  rcases hs with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · fin_cases j
    · exact ⟨_, Flow.code_716⟩
    · exact ⟨_, Flow.code_817⟩
    · exact ⟨_, Flow.code_918⟩
    · exact ⟨_, Flow.code_1019⟩
  · fin_cases j
    · exact ⟨_, Flow.code_814⟩
    · exact ⟨_, Flow.code_915⟩
    · exact ⟨_, Flow.code_1016⟩
    · exact ⟨_, Flow.code_1117⟩

/-- An actual typed softmax load-wait site fires the load completion event. -/
theorem waitLd_operands {d : Wg0.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hs : d.site = .scoreWait ∨ (∃ j, d.site = .rescaleWait j) ∨ ∃ j, d.site = .oWait j) :
    e.kind = .tc .waitLd := by
  obtain ⟨_, _, hf'⟩ := RingGateEvents.fired_at_code hf (waitLd_code hs)
  exact congrArg Event.kind (fires_tcWaitLd (by rw [hpre.block]) hf')

/-- A data collective of the same typed site has the same static operands in every lane. -/
theorem data_operands {d : Wg0.D} {e : Event} {o : Option TState} {k : TcKind}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hs : DataSite d.site) (hk : e.kind = .tc k) :
    some (tcStatic k) = dataOperands d.site := by
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | none =>
      obtain ⟨t, _, hf⟩ := hf
      have he := fires_none_ends hf
      simp [Ends, hk] at he
    | some u => exact ⟨u, rfl⟩
  have hfRole : (Wg0.code P L g).toMachine.Fired (some d) e (some u) := hf
  have core {a : TcKind} (h : e.kind = .tc a) : k = a := Kind.tc.inj (hk.symm.trans h)
  generalize hsite : d.site = s at hs ⊢
  cases hs
  case scoreLoad a j =>
    obtain ⟨words, _, he⟩ := Wg0.fired_scoreLoad_event hpre hsite hfRole
    rw [core he]
    rfl
  case scoreWait =>
    rw [core (waitLd_operands hpre hf (.inl hsite))]
    rfl
  case rescaleLoad j =>
    obtain ⟨ins, hc⟩ := rescale_attribute (.inl ⟨j, hsite⟩)
    obtain ⟨t, hat, he⟩ := RingGateEvents.fired_at_code hf hc
    obtain ⟨words, _, hkind, _⟩ := Wg0.fires_rescaleLoad hpre hsite hat hc he
    rw [core hkind]
    rfl
  case rescaleWait j =>
    rw [core (waitLd_operands hpre hf (.inr (.inl ⟨j, hsite⟩)))]
    rfl
  case rescaleStore j =>
    obtain ⟨ins, hc⟩ := rescale_attribute (.inr ⟨j, hsite⟩)
    obtain ⟨t, hat, he⟩ := RingGateEvents.fired_at_code hf hc
    rw [core (Wg0.fires_rescaleStore hpre hsite hat hc he).1]
    rfl
  case rescaleWaitSt j =>
    have hc : kernel.code[d.site.pc]? = _ := hsite ▸ waitSt_code j
    obtain ⟨t, _, he⟩ := RingGateEvents.fired_at_code hf hc
    rw [core (Wg0.fires_rescaleWaitSt hsite hc he).1]
    rfl
  case outputLoad j =>
    obtain ⟨words, _, he⟩ := Wg0.fired_outputLoad hpre hsite hfRole
    rw [core he]
    rfl
  case outputWait j =>
    rw [core (waitLd_operands hpre hf (.inr (.inr ⟨j, hsite⟩)))]
    rfl

/-- Classify the full payload of every load in the followed trace. -/
theorem load_fields {i address : Nat} {words : List Value} {shape : TcShape} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TLd (g, i) address words shape) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧ shape = .s32x32b ∧
      ((∃ arm part, d.site = .scoreLoad arm part ∧
        address = Wg0.scoreLoadColumn part ∧ words.length = 32) ∨
      ∃ tile, (d.site = .rescaleLoad tile ∨ d.site = .oLoad tile) ∧
        address = 64 * tile.val ∧ words.length = 64) := by
  obtain ⟨tag, he⟩ := hi
  obtain ⟨q, o, hq, hf⟩ := RingSourceSites.fired_from_trace hX hs ht he (by simp)
  have hColl : isTcColl ⟨tag, .tc (.ld address words shape)⟩ = true := rfl
  rcases of_fired hpre hf hColl with ⟨d, rfl, hsite⟩ | ⟨_, _, _, hk, _⟩
  · have hOperands := data_operands hpre hf hsite rfl
    obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
      cases o with
      | none =>
        obtain ⟨t, _, hf⟩ := hf
        have hend := fires_none_ends hf
        simp [Ends] at hend
      | some u => exact ⟨u, rfl⟩
    have hfRole : (Wg0.code P L g).toMachine.Fired (some d) _ (some u) := hf
    generalize hD : d.site = site at hsite hOperands
    cases hsite
    case scoreLoad arm part =>
      obtain ⟨vs, hn, hk⟩ := Wg0.fired_scoreLoad_event hpre hD hfRole
      obtain ⟨rfl, rfl, rfl⟩ := TcKind.ld.inj (Kind.tc.inj hk)
      exact ⟨d, hq, rfl, .inl ⟨arm, part, hD, rfl, hn⟩⟩
    case rescaleLoad tile =>
      obtain ⟨ins, hc⟩ := rescale_attribute (.inl ⟨tile, hD⟩)
      obtain ⟨t, hAt, hFire⟩ := RingGateEvents.fired_at_code hf hc
      obtain ⟨vs, hn, hk, _⟩ := Wg0.fires_rescaleLoad hpre hD hAt hc hFire
      obtain ⟨rfl, rfl, rfl⟩ := TcKind.ld.inj (Kind.tc.inj hk)
      exact ⟨d, hq, rfl, .inr ⟨tile, .inl hD, rfl, hn⟩⟩
    case outputLoad tile =>
      obtain ⟨vs, hn, hk⟩ := Wg0.fired_outputLoad hpre hD hfRole
      obtain ⟨rfl, rfl, rfl⟩ := TcKind.ld.inj (Kind.tc.inj hk)
      exact ⟨d, hq, rfl, .inr ⟨tile, .inr hD, rfl, hn⟩⟩
    all_goals cases hOperands
  · cases hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcCollectiveSites
