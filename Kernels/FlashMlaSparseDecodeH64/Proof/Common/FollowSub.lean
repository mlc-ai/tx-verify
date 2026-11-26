-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowFeed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexPair
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Nc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.PairWord

@[expose] public section

/-! # The following, step by step: warpgroup 1's sub-roles

A step of a sub-role of warpgroup 1 (`sub_good`): the sub-role does not stop, and its successor
either stays in the sub-role with its slot's invariant, or (an MMA or TMA lane that lost its
election, at the idle code's first event) returns to the head's idle exit, which passes on to the
idle code's first state (`subBack`, the gate `subOk .idle` from the lane's warp 4 or 5).

* the MMA and TMA warps (`mma_step`, `tma_step`): the invariant by `Mma.ref_step` / `Tma.ref_next`
  (void after an undefined behaviour: the guard counts it), the site facts by `siteOk_next` /
  `siteOk_step`; the machines stop only at a returning state (none is a state of the machine:
  `fresh`) and at a length load that read no 32-bit word, which the launch's lengths exclude
  (`Mma.next_topk`, `Tma.tma_topk`, …); the TMA warp's coordinate reads continue on any payload;
* the idle code (`idle_step`): it never stops. -/

/-! # The index warp does not stop

The index machine stops (`some none`) at a length load whose word is not a 32-bit one and at a pair
load whose payload is not a 32-bit word. A length load reads the launch's word (`ix_topk`,
`ix_extra`); a pair load reads a word of the lane's index row, which `Pre` allocates and the
read-only assumption returns (`main_pair_core`, `extra_pair_core`, `main_pair_word`,
`extra_pair_word`), from the state alone (`pair_state`): so the machine goes on (`ix_live`, the
no-stop obligation of `Common/FollowProof.lean`), with no `Follow`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Away from the length loads and the pair loads the index machine never stops. -/
private theorem ix_ne_none {d : Index.D} {e : Event} (hA : d.site ≠ .lenA)
    (hB : d.site ≠ .lenB) (hP : ¬ (d.site = .pre ∨ d.site = .pf ∨ d.site = .xpre ∨
      d.site = .xpf)) : succ P L g d e ≠ some none := by
  intro h
  obtain ⟨site, el, ac, c⟩ := d
  cases site with
  | lenA => exact hA rfl
  | lenB => exact hB rfl
  | pre | pf | xpre | xpf => simp at hP
  | wA | wB => simp only [succ, poll] at h; split at h <;> simp at h
  | sA1 | sA2 | sB1 | sB2 => simp only [succ, shflNext] at h; split at h <;> simp at h
  | _ => simp [succ] at h

/-- **A pair load does not stop the machine**: its payload is the row's 32-bit word. -/
private theorem ix_pair_live (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Index.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)))
    (hJ : (table P L).J g (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n))
    (hP : d.site = .pre ∨ d.site = .pf ∨ d.site = .xpre ∨ d.site = .xpf) :
    succ P L g d e ≠ some none := by
  obtain ⟨pc, kd⟩ := e
  have hsucc : ∀ {y : BitVec 64}, ∀ a bs, kd = .nc a bs → rebuild 3 bs = .ok (.bits 32 y) →
      succ P L g d ⟨pc, kd⟩ ≠ some none := by
    intro y a bs hk hr
    subst hk
    rcases hP with hs | hs | hs | hs <;>
      simp [succ, hs, ncPair, hr]
  cases kd with
  | nc a bs =>
    have hub : ∀ f, (⟨pc, .nc a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
      Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
    have hev := ev_of_state hp hX he hσ hJ hub
    have hpcσ := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
    have hpcd : pc = d.site.pc := by
      have := EventFrame.fires_source_pc hf
      exact this
    have hpc4 : pc = 2403 ∨ pc = 2429 ∨ pc = 2501 ∨ pc = 2517 := by
      rcases hP with hs | hs | hs | hs <;> rw [hpcd, hs] <;> simp [IxSite.pc]
    obtain ⟨d', n', i, heq, -, hpd, hEv, hel, hct, -, h0, h1⟩ :=
      pair_state hp hX he hpc4 hσ hJ hi hev hpcσ
    obtain ⟨rfl, rfl⟩ : d = d' ∧ n = n' := by
      simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
      exact ⟨heq.1, heq.2⟩
    rcases hpc4 with h | h | h | h
    · obtain ⟨b, -, -, -, hlt, hsz, hloc⟩ :=
        main_pair_core hp hpd hEv hel hct h0 (Or.inl h)
      exact hsucc a bs rfl (main_pair_word hp hX he (Or.inl h) hlt hsz hloc)
    · obtain ⟨b, -, -, -, hlt, hsz, hloc⟩ :=
        main_pair_core hp hpd hEv hel hct h0 (Or.inr h)
      exact hsucc a bs rfl (main_pair_word hp hX he (Or.inr h) hlt hsz hloc)
    · obtain ⟨b, -, -, -, hlt, hsz, hloc⟩ :=
        extra_pair_core hp hpd hEv hel hct h0 h1 (Or.inl h)
      exact hsucc a bs rfl (extra_pair_word hp hX he (Or.inl h) hlt hsz hloc)
    · obtain ⟨b, -, -, -, hlt, hsz, hloc⟩ :=
        extra_pair_core hp hpd hEv hel hct h0 h1 (Or.inr h)
      exact hsucc a bs rfl (extra_pair_word hp hX he (Or.inr h) hlt hsz hloc)
  | _ => rcases hP with hs | hs | hs | hs <;> simp [succ, hs, ncPair]

/-- **The index warp's machine does not stop at its events** (the no-stop obligation of
`Common/FollowProof.lean`): its length loads read the launch's 32-bit words, its pair loads the
index row's. -/
theorem ix_live (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Index.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)))
    (hJ : (table P L).J g (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)) :
    succ P L g d e ≠ some none := by
  have hok := (ix_ok hp hX hσ d n rfl).1
  have nc {s : IxSite} (hs : d.site = s) (hs' : s = .lenA ∨ s = .lenB)
      (hu : ∃ fl, e.kind = .ub fl) : succ P L g d e ≠ some none := by
    obtain ⟨fl, hk⟩ := hu
    rcases hs' with rfl | rfl <;> simp [succ, lenNext, hs, hk]
  by_cases hA : d.site = .lenA
  · by_cases hu : ∃ fl, e.kind = .ub fl
    · exact nc hA (.inl rfl) hu
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := ix_fired hp hX he (fun fl h => hu ⟨fl, h⟩) hσ
    have hok' := hok
    simp only [ixLenOk, hA] at hok'
    rw [ix_topk hp hX he hat hi hc hf hok'.1 hA]
    simp
  by_cases hB : d.site = .lenB
  · by_cases hu : ∃ fl, e.kind = .ub fl
    · exact nc hB (.inr rfl) hu
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := ix_fired hp hX he (fun fl h => hu ⟨fl, h⟩) hσ
    have hok' := hok
    simp only [ixLenOk, hB] at hok'
    rw [ix_extra hp hX he hat hi hc hf hok'.1 hB]
    simp
  by_cases hP : d.site = .pre ∨ d.site = .pf ∨ d.site = .xpre ∨ d.site = .xpf
  · exact ix_pair_live hp hX he hσ hJ hP
  exact ix_ne_none hA hB hP


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {X : Execution}

theorem next_sub (i : SubEntry) (d : (subFrag P L g i).D) (n : Cls → Nat) (e : Event) :
    (thread P L g).next (.inr ⟨.inl .wg1, .inr ⟨.inl i, d⟩⟩, n) e =
      ((subFrag P L g i).next d e).map (Option.map fun d' =>
        (.inr ⟨.inl .wg1, Code.backEnter (wg1HeadCode P L g)
          (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
          (Code.gatedExit (wg1Enter P L g) (subSel P L g))
          (fun | .inl i => subBack P L g i | .inr _ => fun _ => none) (.inl i) d'⟩,
          Code.bump cls n e)) := by
  rw [next_frag]
  rcases h : (subFrag P L g i).next d e with _ | _ | d'
  · simp [frag, wg1Code, Code.roleLoop, Code.loopGlue, h]
  · simp [frag, wg1Code, Code.roleLoop, Code.loopGlue, h]
  · simp only [frag, wg1Code, Code.roleLoop, Code.loopGlue, h, Option.map_some]
    rfl

/-- A sub-role's slot counts three shuffles. -/
theorem wg1J_shfl {i : SubEntry} {d : (subFrag P L g i).D} {n : Cls → Nat}
    (h : wg1J P L g (.inr ⟨.inl i, d⟩) n) : 3 ≤ n .shfl := by
  cases i
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

/-- **A sub-role's step is good**, from its slot's invariant at a successor that stays and the
gate of the idle code at one that returns. -/
theorem sub_good {i : SubEntry} {d : (subFrag P L g i).D} {n : Cls → Nat} {e : Event}
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inr ⟨.inl i, d⟩⟩, n))
    (hns : (subFrag P L g i).next d e ≠ some none)
    (hstay : ∀ d', (subFrag P L g i).next d e = some (some d') → subBack P L g i d' = none →
      wg1J P L g (.inr ⟨.inl i, d'⟩) (Code.bump cls n e))
    (hret : subOk L g .idle = true ∨ ∀ d', subBack P L g i d' = none) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inr ⟨.inl i, d⟩⟩, n) e := by
  obtain ⟨⟨hb, hW, h2, hwg⟩, -⟩ := hJ
  have hb' := Nat.le_trans hb (bump_ge n e .bar0)
  have h2' := Nat.le_trans h2 (bump_ge n e .shfl)
  unfold Frame.StepGood
  rw [next_sub]
  rcases hs : (subFrag P L g i).next d e with _ | _ | d'
  · simp
  · exact absurd hs hns
  refine ⟨by simp, fun σ' h' => ?_⟩
  simp only [Option.map_some, Option.some.injEq] at h'
  subst h'
  cases hk : subBack P L g i d' with
  | none =>
    simp only [Code.backEnter, hk]
    exact ⟨⟨hb', hstay d' hs hk, h2', hwg⟩, hk⟩
  | some s =>
    have hok : subOk L g .idle = true := by
      rcases hret with h | h
      · exact h
      · rw [h d'] at hk
        cases hk
    have hs' : s = .idle := by
      cases i with
      | mma | tma =>
        simp only [subBack] at hk
        split_ifs at hk
        cases hk
        rfl
      | index | idle => cases hk
    subst hs'
    simp only [Code.backEnter, hk, Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf,
      Option.map_some, subSel, hok, ite_true]
    exact ⟨⟨hb', ⟨Nat.le_trans (wg1J_shfl hW) (bump_ge n e .shfl), hok⟩, h2', hwg⟩, rfl⟩

/-! ### The idle code -/

/-- The idle code never stops. -/
theorem idle_live (s : IdleSite) (e : Event) : Wg1.isucc P s e ≠ some none := by
  cases s with
  | ldA | ldB =>
    simp only [Wg1.isucc, Wg1.afterNc]
    split
    · split <;> simp
    · simp
  | bar | ret => simp [Wg1.isucc]

/-- **A step of the idle code is good.** -/
theorem idle_step {s : IdleSite} {n : Cls → Nat} {e : Event}
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, s⟩⟩, n)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, s⟩⟩, n) e := by
  obtain ⟨⟨-, ⟨h3, hok⟩, -, -⟩, -⟩ := id hJ
  exact sub_good hJ (idle_live s e)
    (fun _ _ _ => ⟨Nat.le_trans h3 (bump_ge n e .shfl), hok⟩) (.inr fun _ => rfl)

/-! ### The MMA warp -/

/-- **The MMA warp does not stop** at a state of the machine with its site facts: a returning
state is none (`fresh`), and a length load reads the launch's word. -/
theorem mma_live (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {e : Event} (hget : X.get i = some e) {d : Mma.D} (hok : Mma.SiteOk P L g d)
    (hback : subBack P L g .mma d = none)
    (hsite : (∀ f, e.kind ≠ .ub f) → ∃ t ins o, (Mma.code P L g).AtD d t ∧
      kernel.code[(Mma.code P L g).pc d]? = some ins ∧
      Fires ((Mma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    Mma.succ P L g d e ≠ some none := by
  intro h
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    cases site with
    | leave s =>
      obtain rfl := hok.2.2 s rfl
      simp [subBack] at hback
    | _ => simp [Mma.succ, Mma.ncWord, Mma.poll, hf] at h
  obtain ⟨t, ins, o, hat, hc, hf⟩ := hsite fun f h => hu ⟨f, h⟩
  cases site with
  | loadTopk => rw [Mma.next_topk hp hX hget hok hat hc hf] at h; cases h
  | loadExtra => rw [Mma.next_extra hp hX hget hok hat hc hf] at h; cases h
  | leave s =>
    obtain rfl := hok.2.2 s rfl
    simp [subBack] at hback
  | elect => simp only [Mma.succ] at h; split at h <;> cases h
  | qWait | qCopyWait | kvWait | soWait =>
    simp only [Mma.succ, Mma.poll] at h; split at h <;> cases h
  | _ => simp [Mma.succ] at h

/-- **A step of the MMA warp is good**, fed from the trace. -/
theorem mma_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Mma.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n) e := by
  obtain ⟨⟨-, ⟨h3, hw, ⟨hR, hok⟩, -⟩, -, -⟩, hback⟩ := id hJ
  have hsite := fun hu => Frame.fired_siteU (fun _ _ => thread_sound hp) hX he hσ hu
  refine sub_good hJ (mma_live hp hX he hok hback fun hu => ?_) (fun d' hn _ => ?_) (.inl ?_)
  · obtain ⟨t, ins, o, hat, -, hc, hf⟩ := hsite hu
    exact ⟨t, ins, o, hat, hc, hf⟩
  · have hok' := Mma.siteOk_next hn
    refine ⟨Nat.le_trans h3 (bump_ge n e .shfl), hw, ⟨fun h0 => ?_, hok'⟩, hok'.2.2⟩
    have hev := ev_of_state hp hX he hσ hJ.1 (not_ub_of_bump h0)
    exact Mma.ref_step (hR (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))) hev hn
  · simp only [subOk, beq_iff_eq] at hw
    simp [subOk, hw]

/-! ### The TMA warp and the index warp -/

/-- **The TMA warp does not stop** at a state of the machine with its site facts: a returning
state is none (`fresh`), a length load reads the launch's word, and a coordinate element continues
on any payload. -/
theorem tma_live (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {e : Event} (hget : X.get i = some e) {d : Tma.D} (hok : Tma.SiteOk P L g d)
    (hback : subBack P L g .tma d = none)
    (hsite : (∀ f, e.kind ≠ .ub f) → ∃ t ins o, (Tma.code P L g).AtD d t ∧
      kernel.code[(Tma.code P L g).pc d]? = some ins ∧
      Fires ((Tma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    Tma.succ P L g d e ≠ some none := by
  intro h
  obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    cases site with
    | leave s =>
      obtain rfl := hok.2.2 s rfl
      simp [subBack] at hback
    | _ => simp [Tma.succ, Tma.ncWord, Tma.rdAny, Tma.poll, Tma.electNext, hf] at h
  obtain ⟨t, ins, o, hat, hc, hf⟩ := hsite fun f h => hu ⟨f, h⟩
  cases site with
  | loadTopk => rw [Tma.tma_topk hp hX hget hok hat hc hf rfl] at h; cases h
  | loadExtra => rw [Tma.tma_extra hp hX hget hok hat hc hf rfl] at h; cases h
  | leave s =>
    obtain rfl := hok.2.2 s rfl
    simp [subBack] at hback
  | elect => simp only [Tma.succ, Tma.electNext] at h; split at h <;> cases h
  | qWait | storeWait | coordWait | rawWait =>
    simp only [Tma.succ, Tma.poll] at h; split at h <;> cases h
  | coord0 | coord1 | coord2 | coord3 =>
    simp only [Tma.succ, Tma.rdAny, Tma.afterQuad] at h; split at h <;> cases h
  | _ => simp [Tma.succ] at h

/-- **A step of the TMA warp is good**, fed from the trace. -/
theorem tma_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Tma.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n) e := by
  obtain ⟨⟨-, ⟨h3, hw, ⟨hR, hok⟩, -⟩, -, -⟩, hback⟩ := id hJ
  have hsite := fun hu => Frame.fired_siteU (fun _ _ => thread_sound hp) hX he hσ hu
  refine sub_good hJ (tma_live hp hX he hok hback fun hu => ?_) (fun d' hn _ => ?_) (.inl ?_)
  · obtain ⟨t, ins, o, hat, -, hc, hf⟩ := hsite hu
    exact ⟨t, ins, o, hat, hc, hf⟩
  · have hok' := Tma.siteOk_step hn
    refine ⟨Nat.le_trans h3 (bump_ge n e .shfl), hw, ⟨fun h0 => ?_, hok'⟩, hok'.2.2⟩
    have hev := ev_of_state hp hX he hσ hJ.1 (not_ub_of_bump h0)
    exact Tma.ref_next (hR (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))) hev hn
  · simp only [subOk, beq_iff_eq] at hw
    simp [subOk, hw]

/-- **A step of the index warp is good**: the machine does not stop at the event (`ix_live`,
`Common/IndexNoStop.lean`). -/
theorem index_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Index.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) e := by
  obtain ⟨⟨-, ⟨h3, hw, hR⟩, -, -⟩, -⟩ := id hJ
  refine sub_good hJ (ix_live hp hX he hσ hJ.1) (fun d' hn _ => ?_) (.inr fun _ => rfl)
  refine ⟨Nat.le_trans h3 (bump_ge n e .shfl), hw, fun h0 => ?_⟩
  have hev := ev_of_state hp hX he hσ hJ.1 (not_ub_of_bump h0)
  exact Index.ref_step hp (hR (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))) hev hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
