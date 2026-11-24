-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Slot

@[expose] public section

/-! # One actor per selector of the input ring

The producer selector of a slot names all of a loader warp and the consumer selector all of
an MMA warp; only the warp's elected lane polls the slot's barriers. So any two threads of a
selector that poll the selector's barrier are one thread. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two threads of producer `a`'s selector that poll slot `s`'s empty barrier are one. -/
theorem producer_unique (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {cluster : Nat} {a : Fin 2} {s : Fin 4} {g h j k : Nat}
    {e f : Event} (hpg : producerThread L cluster a g = true)
    (hph : producerThread L cluster a h = true) (he : X.get (g, j) = some e)
    (hf : X.get (h, k) = some f) {p p' : Nat} {ok ok' acq acq' : Bool} {sc sc' : MbarScope}
    (hke : e.kind = .wait ((slot L cluster s).empty a) p ok acq sc)
    (hkf : f.kind = .wait ((slot L cluster s).empty a) p' ok' acq' sc') : g = h := by
  simp only [producerThread, decide_eq_true_eq] at hpg hph
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  have elected : ∀ {x i : Nat} {ev : Event} {q : Nat} {o a' : Bool} {c : MbarScope},
      x < L.threads → x / L.block = 2 * cluster + a.val → x % L.block / 32 = 11 →
      X.get (x, i) = some ev → ev.kind = .wait ((slot L cluster s).empty a) q o a' c →
      ∃ j' inst leader, X.Elect (x, j') Prologue.Site.roleElect.pc 4294967295 inst leader ∧
        laneOf L x = leader := by
    intro x i ev q o a' c hx hb hw hev hk
    obtain ⟨r, hσ, hr⟩ := wait_role hX ht hx hev hk
    cases r with
    | loader l =>
      obtain ⟨j', inst, leader, -, hget, hl⟩ := ht.elected hx hev hσ rfl (by rw [hk]; trivial)
      exact ⟨j', inst, leader, hget, hl⟩
    | mma m => simp only [roleWarp] at hr; omega
    | sched sd => simp only [roleWarp] at hr; omega
    | cons c => simp only [roleWarp] at hr; omega
  obtain ⟨j1, i1, l1, hE1, hl1⟩ := elected hg hpg.1 hpg.2 he hke
  obtain ⟨j2, i2, l2, hE2, hl2⟩ := elected hh hph.1 hph.2 hf hkf
  exact selected_elect_thread_unique hX.elect hE1 hE2
    ⟨⟨hg, hh, hpg.1.trans hph.1.symm⟩, hpg.2.trans hph.2.symm⟩ hl1 hl2

/-- Two threads of consumer `b`'s selector that poll slot `s`'s full barrier are one. -/
theorem consumer_unique (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {cluster : Nat} {b : Fin 2} {s : Fin 4} {g h j k : Nat}
    {e f : Event} (hcg : consumerThread L cluster b g = true)
    (hch : consumerThread L cluster b h = true) (he : X.get (g, j) = some e)
    (hf : X.get (h, k) = some f) {p p' : Nat} {ok ok' acq acq' : Bool} {sc sc' : MbarScope}
    (hke : e.kind = .wait ((slot L cluster s).full 0) p ok acq sc)
    (hkf : f.kind = .wait ((slot L cluster s).full 0) p' ok' acq' sc') : g = h := by
  simp only [consumerThread, decide_eq_true_eq] at hcg hch
  have := b.isLt
  exact mma_unique hX ht (hcg.1.trans hch.1.symm) (hcg.2.trans hch.2.symm) (by omega) he hf hke hkf

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
