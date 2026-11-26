-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Start0
import Kernels.TmlFa4Fwd.Flow.Code.Part000
import Kernels.TmlFa4Fwd.Flow.Code.Part001
import Kernels.TmlFa4Fwd.Flow.Code.Part002
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Lemmas.Flow.MemAl
import Lemmas.Flow.Arith32WordAlign
import Lemmas.Flow.TmplOkSync

@[expose] public section

/-! # The startup of warp 0 is no undefined behaviour and does not die

A lane of warp 0 at a startup state of `StartAt0` fires the three shuffles, the sixteen
elections, the initializations of the elected lane, the fence and the CTA barrier. An election
has the immediate full mask (`elect_imm_ok`). An initialization (`mbarrier.init [r + o], c`)
addresses the shared base or the base plus a constant, plus an offset, all multiples of 8, and its
count register holds a constant between 1 and `2 ^ 20` (`mbarInit_bits_ok`). The startup machine
dies only on an event of another kind than its site's. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **No event of a startup state of warp 0 is undefined behaviour.** -/
theorem start0_safe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt0 L s n)
    (f : Fault) : e.kind ≠ .ub f := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    strict_fired_site hp hX he hσ rfl
  have hreg : ∀ r ∈ Flow.live s.site.pc, t.regs r = some (Startup.valueOf p L g s r) :=
    fun r hr => holds_mem hat.2.2.2.2 (mem_factsFrom hr)
  replace hc : kernel.code[s.site.pc]? = some ins := hc
  have hb := hp.shared.1
  have hb2 := hp.shared.2.1
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | sh j => exact start_safe hp hX he hσ (startAt0_sh hS (by
      have := hS; simp only [StartAt0] at this; omega)) f
  | elect j =>
    intro hk
    have hu := fires_ub hf hk
    fin_cases j <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      exact elect_imm_ok f hu
  | init q =>
    obtain ⟨-, rfl, -⟩ := startAt0_of_mid (by rfl) hS
    have hsb : Flow.Arith32.Al 3 (BitVec.ofNat 64 L.sharedBase) := by
      unfold Flow.Arith32.Al; simp only [BitVec.toNat_ofNat]; omega
    intro hk
    have hu := fires_ub hf hk
    fin_cases q <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine mbarInit_al_ok (hreg _ (by lit_mem)) ?_ (by decide) (hreg _ (by lit_mem))
        (by decide) (by decide) f hu
      show Flow.Arith32.Al 3 _
      al_tac
  | fence =>
    obtain ⟨hev, -, -⟩ := start_fired hp hX he hσ
    simp only [Startup.Ev] at hev
    rw [hev]; simp
  | bar =>
    obtain ⟨hev, -, -⟩ := start_fired hp hX he hσ
    simp only [Startup.Ev] at hev
    rw [hev]; simp
  | enter r => simp [StartAt0] at hS

/-- **A startup state of warp 0 does not die** on the event it fires. -/
theorem start0_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt0 L s n)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hn : (thread p L g).next (.inl s, n) e = none) : e.kind = .exit := by
  obtain ⟨hev, -, -⟩ := start_fired hp hX he hσ
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  simp only [thread, Code.counted, glued, Code.glue, Option.map_eq_none_iff] at hn
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;>
      (obtain ⟨_, _, hk⟩ := hev; subst hk
       simp [Startup.succ, Startup.word32] at hn; split at hn <;> simp at hn)
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, -, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Startup.succ] at hn
    · exact absurd hk (hub f)
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp only [Startup.succ] at hn; split at hn <;> simp at hn
    · exact absurd hk (hub f)
  | fence => simp [Startup.succ] at hn
  | bar => simp [Startup.succ] at hn
  | enter r => simp [StartAt0] at hS

end
end PTX.Kernels.TmlFa4Fwd.Proof
