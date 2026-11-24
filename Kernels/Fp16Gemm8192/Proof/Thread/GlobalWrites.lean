-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutEvents
public import Lemmas.Flow.WriteSpace

@[expose] public section

/-! # The kernel's writes to global memory

Every store of the kernel names shared memory (decided on the code), so a thread writes only
shared memory (`write_shared_fact`). The kernel's tensor stores are the consumer's eight TMA
stores, through the output map (`store_map_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's stores all name shared memory (decided on the code). -/
theorem kernel_stores_shared :
    kernel.code.all (fun ins => (storeSpace ins.op == none || storeSpace ins.op == some .shared) &&
      !dynamicAccess ins.op) = true := by
  decide +kernel

/-- **A thread writes shared memory.** -/
theorem write_shared_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .wr a bs) : a.loc.space = .shared := by
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hall := List.all_eq_true.mp kernel_stores_shared ins (List.mem_of_getElem? hc)
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hall
  rcases fires_write_space hfire hk with hsp | hd
  · rw [hsp] at hall
    simpa using hall.1
  · simp [hd] at hall

/-- The positions of the consumer's TMA stores. -/
def storePcs : List Nat := [Flow.tensorCopy_24, Flow.tensorCopy_25, Flow.tensorCopy_26,
  Flow.tensorCopy_27, Flow.tensorCopy_28, Flow.tensorCopy_29, Flow.tensorCopy_30,
  Flow.tensorCopy_31]

/-- The kernel's tensor stores are the consumer's (decided on the code, in one pass). -/
theorem kernel_store_pcs : OpPcsFast kernel.code tensorStoreOp storePcs = true := by
  decide +kernel

/-- A state at a TMA store position is a consumer at a TMA store. -/
theorem store_state {d : ThreadD} {g : Nat} (h : (code L g).pc d ∈ storePcs) :
    ∃ c k, d = .inr (.cons c) ∧ c.site = .tma k := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals change site.pc ∈ _ at h
  all_goals (cases site <;> first
    | exact ⟨_, _, rfl, rfl⟩
    | (exfalso; clear * - h; revert h; decide +kernel +revert))

/-- **The TMA stores write through the output map.** A tensor store reads the map held as the
third parameter. -/
theorem store_map_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorStore.Spec}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tensorStore a sp) :
    L.paramObjects "gemm_kernel_param_2" = some (mapParam "gemm_kernel_param_2", a) ∧
      L.tensorMaps a = some ⟨sp.outer, sp.descriptor⟩ := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨c, s, rfl, hs⟩ :=
    store_state (OpPcsFast.mem kernel_store_pcs hc (fires_tensorStore_op hfire hk))
  obtain ⟨rfl, hdesc, -⟩ := Consumer.tma_event hpre hat hinv.2.1 hc hfire hs a sp hk
  refine ⟨hpre.paramD, ?_⟩
  rw [hpre.mapD, hdesc]
