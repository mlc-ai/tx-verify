-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.OwnCta
public import Lemmas.Kernel.Safety.Classes
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Lemmas.Flow.TensorStoreBase
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A lane uses the shared memory of its own CTA

The accesses of shared memory, the mbarriers named, the destinations and sources of the copies and
the CTAs of a commit are of the issuing lane's CTA: clusters have one CTA. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem kernel_access :
    kernel.code.all (fun ins => !dynamicAccess ins.op || localRegOp ins.op) = true := by
  decide +kernel

theorem kernel_noAtomic : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

theorem kernel_noBulkGroup : kernel.code.all (fun ins => !bulkGroupOp ins.op) = true := by
  decide +kernel

theorem kernel_noClc : kernel.code.all (fun ins => !clcOp ins.op) = true := by decide +kernel

theorem kernel_noBulkPrefetch : kernel.code.all (fun ins => !bulkPrefetchOp ins.op) = true := by
  decide +kernel

/-- A CTA of the cluster of a CTA is that CTA. -/
theorem cluster_eq (hp : Pre p L m) {a b : Nat} (h : CtaInCluster L a b) : b = a := by
  have hOne := hp.cluster.2.2
  have h1 := hp.cluster.1
  obtain ⟨-, -, h⟩ := h
  simpa [Launch.oneDim_clusterOfCta hOne, h1] using h.symm

section
variable (hX : Consistent L kernel Assumptions.all m X)
include hX

/-- **A thread's access of shared memory is of its own CTA.** -/
theorem access_own {i : EvId} {a : Acc} {w : Bool} (h : X.Access i a w)
    (hs : a.loc.space = .shared) : a.loc.cta = i.1 / L.block := by
  have hstat : ∀ {pc : Nat} {ins : Instr}, kernel.code[pc]? = some ins →
      dynamicAccess ins.op = true → localRegOp ins.op = true := by
    intro pc ins hc hd
    have := List.all_eq_true.mp kernel_access ins (List.mem_of_getElem? hc)
    simpa [hd] using this
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
  · rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
    · cases hi
    · exact fires_access_own hf (hstat hc) (.inl ⟨bs, rfl⟩) hs
  · rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
    · cases hi
    · exact fires_access_own hf (hstat hc) (.inr ⟨bs, rfl⟩) hs
  · exact absurd ⟨_, _, _, rfl⟩ (no_kind_of_code hX atomicOp
      (fun k => ∃ a o n, k = .rmw a o n) (fun _ ⟨_, _, _, h⟩ => by cases h)
      (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) kernel_noAtomic he)

/-- **A tensor store's source is of its own CTA.** -/
theorem store_own {i : EvId} {a : Nat} {s : TensorStore.Spec} (h : X.TensorStoreIssue i a s) :
    s.sharedBase.cta = i.1 / L.block := by
  obtain ⟨pc, he⟩ := h
  rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hi
  · exact fires_tensorStore_base hf rfl

/-- **A tensor load's destination and mbarrier are of its own CTA.** -/
theorem load_own (hp : Pre p L m) {i : EvId} {a : Nat} {s : TensorCopy.Spec}
    (h : X.TensorIssue i a s) :
    s.sharedBase.cta = i.1 / L.block ∧ s.mbar.cta = i.1 / L.block := by
  obtain ⟨pc, he⟩ := h
  rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hi
  · obtain ⟨h1, h2⟩ := fires_tensorIssue_cluster hf
    exact ⟨cluster_eq hp h1, cluster_eq hp h2⟩

/-- **A row copy reads global memory and writes shared memory of its own CTA.** -/
theorem copy_own {i : EvId} {s : AsyncCopy.Spec} (h : X.Copy i s) :
    s.completion = .asyncGroup ∧ s.src.loc.space = .global ∧ s.dst.loc.space = .shared ∧
      s.dst.loc.cta = i.1 / L.block ∧ s.writes = .whole := by
  obtain ⟨pc, he⟩ := h
  rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hi
  · have hop := List.all_eq_true.mp kernel_noBulkGroup ins (List.mem_of_getElem? hc)
    exact fires_cpAsync_local (by simpa using hop) hf

/-- The kernel issues no cluster launch control request. -/
theorem no_clc {i : EvId} {s : Clc.Spec} {tg : List Nat} : ¬ X.ClcIssue i s tg :=
  fun ⟨_, he⟩ => no_kind_of_code hX clcOp (fun k => ∃ s tg, k = .clcIssue s tg)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk) kernel_noClc he
    ⟨_, _, rfl⟩

/-- The kernel issues no linear prefetch. -/
theorem no_bulkPrefetch {i : EvId} {a : Acc} : ¬ X.BulkPrefetch i a :=
  fun ⟨_, he⟩ => no_kind_of_code hX bulkPrefetchOp (fun k => ∃ a, k = .bulkPrefetch a)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulkPrefetch_op hf hk)
    kernel_noBulkPrefetch he ⟨_, rfl⟩

/-- **A named mbarrier is of the naming lane's CTA.** -/
theorem mbar_own (hp : Pre p L m) (hFw : Follow p L X) {i : EvId} {e : Event} {l : Loc}
    (he : X.get i = some e) (hm : Frame.MbarOf e l) (hub : ∀ f, e.kind ≠ .ub f) :
    l.cta = i.1 / L.block := by
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  have hinit : ∀ {j : EvId} {c : Nat}, X.MbInit j l c → l.cta = j.1 / L.block := by
    rintro ⟨h, k'⟩ c ⟨pc, hi⟩
    obtain ⟨-, q, s, n, -, -, hl, -⟩ := init_event hp hX hFw (Frame.lt_of_get hX hi) hi
    rw [hl]
  by_cases hni : ∃ c, e.kind = .mbInit l c
  · obtain ⟨c, hc⟩ := hni
    obtain ⟨pc, kd⟩ := e
    simp only at hc
    subst hc
    exact hinit (j := (g, k)) ⟨pc, he⟩
  · obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
      (table_followed hp hX hFw) he hub
    obtain ⟨j, c, hj, -, hcta, -⟩ := use_pub hp hX hFw hg he hσ hJ hi hev hm
      (fun c hc => hni ⟨c, hc⟩)
    exact (hinit hj).trans hcta

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Life
