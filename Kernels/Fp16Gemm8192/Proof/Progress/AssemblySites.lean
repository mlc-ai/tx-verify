-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Descent

@[expose] public section

/-! # The kinds of a thread's next event

The progress assembly splits a pending thread whose last event is released by the site of its
machine state, that is by the kind of its next event (`nextKind`, `Thread/NextKind.lean`): one
of the mbarrier waits whose class is proved, a cluster barrier operation, a named barrier
arrival, a register request, a paired Tensor Memory operation, or one of the kinds whose step is
still a premise of the assembly (`Assembly.lean`). The lemmas below turn a kind back into the site
predicates the class theorems take. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

theorem nextKind_emptyWait {d : ThreadD} (h : nextKind d = .emptyWait) :
    ∃ l b, d = .inr (.loader l) ∧ l.site = .wait b := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_drainWait {d : ThreadD} (h : nextKind d = .drainWait) :
    ∃ l i, d = .inr (.loader l) ∧ l.site = .drain i := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_fullWait {d : ThreadD} (h : nextKind d = .fullWait) :
    ∃ m s, d = .inr (.mma m) ∧ m.site = .full s := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_mmaAccWait {d : ThreadD} (h : nextKind d = .mmaAccWait) :
    ∃ m, d = .inr (.mma m) ∧ m.site = .accWait := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_consAccWait {d : ThreadD} (h : nextKind d = .consAccWait) :
    ∃ c, d = .inr (.cons c) ∧ c.site = .accWait := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_bulkWait {d : ThreadD} (h : nextKind d = .bulkWait) :
    ∃ c, d = .inr (.cons c) ∧ ((∃ k, c.site = .drain k) ∨ c.site = .finalDrain) := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_clcWait {d : ThreadD} (h : nextKind d = .clcWait) : d.AtClcWait := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind,
      ThreadD.AtClcWait]

theorem nextKind_ackWait {d : ThreadD} (h : nextKind d = .ackWait) :
    ∃ s, d = .inr (.sched s) ∧ s.site = .ackWait := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_cluster {d : ThreadD} (h : nextKind d = .cluster) : d.AtCluster := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind,
      ThreadD.AtCluster]

theorem nextKind_bar {d : ThreadD} (h : nextKind d = .bar) :
    ∃ c, d = .inr (.cons c) ∧
      (c.site = .clcBar ∨ (∃ k, c.site = .barA k) ∨ ∃ k, c.site = .barB k) := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind]

theorem nextKind_reg {d : ThreadD} (h : nextKind d = .reg) : d.AtSetMaxReg := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind,
      ThreadD.AtSetMaxReg]

theorem nextKind_tmem {d : ThreadD} (h : nextKind d = .tmem) : d.AtTmem := by
  rcases d with ⟨s, _⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ | ⟨⟨s⟩⟩ <;> cases s <;>
    simp_all [nextKind, prologueKind, loaderKind, mmaKind, schedKind, consKind,
      ThreadD.AtTmem]

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
