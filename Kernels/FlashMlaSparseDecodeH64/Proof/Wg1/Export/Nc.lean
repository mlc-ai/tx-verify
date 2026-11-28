-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IdleLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # The idle code's `.nc` reads are allocated

The idle code's two `.nc` reads are its length loads (pcs 2596 and 2601), whose pointers are set
(`idleOk`): each reads the four bytes of its row of the array (`Wg1.idle_topk_read`,
`Wg1.idle_extra_read`), which `Pre` allocates (`paramTopkLen`, `paramExtraTopkLen`). The head
(pcs 1842–1849) makes none. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The `.nc` read of warpgroup 1's head or idle code covers allocated bytes only.** -/
theorem wg1_ncAlloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : Wg1At L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, -, hr⟩ := hat
  have h := state_role hJ hi
  rw [← hpcσ] at h
  cases h with
  | head s n hs hpc' hr' hg hw =>
    have hev' : Wg1.Ev L g s e := hev
    rcases hs with rfl | rfl
    · obtain ⟨_, h⟩ := hev'; rw [hk] at h; cases h
    · obtain ⟨_, _, h⟩ := hev'; rw [hk] at h; cases h
  | idle s n hpc' hw hr' hret =>
    have hev' : Wg1.IEv s e := hev
    have hok := idle_ok hσ s n rfl
    obtain ⟨t, ins, o, hat', -, hc', hf⟩ : ∃ t ins o, (Wg1.idle P L g).AtD s t ∧ True ∧
        kernel.code[(Wg1.idle P L g).pc s]? = some ins ∧
        Fires ((Wg1.idle P L g).pc s) (eventTmpl Assumptions.all L g t ins.op) e o :=
      let ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
      ⟨t, ins, o, hat, trivial, hc, hf⟩
    cases s with
    | ldA =>
      obtain ⟨x, hx⟩ := len_ptr hok
      obtain ⟨bs', hr⟩ := Wg1.idle_topk_read hp hx rfl hat' hc' hf
      obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
      exact len_alloc_topk hp (ctaid_lt hp g).2 hx hk hr l hc
    | ldB =>
      obtain ⟨x, hx⟩ := len_ptr hok
      obtain ⟨bs', hr⟩ := Wg1.idle_extra_read hp hx rfl hat' hc' hf
      obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
      exact len_alloc_extra hp (ctaid_lt hp g).2 hx hk hr l hc
    | bar => simp only [Wg1.IEv] at hev'; rw [hk] at hev'; cases hev'
    | ret => simp only [Wg1.IEv] at hev'; rw [hk] at hev'; cases hev'
  | _ => exfalso; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
