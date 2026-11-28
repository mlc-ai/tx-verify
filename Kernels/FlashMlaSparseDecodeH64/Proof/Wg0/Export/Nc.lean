-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.LseSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # Warpgroup 0's `.nc` reads are allocated

Warpgroup 0's `.nc` reads are the sink's load (pc 156: word `t % 64`, entered only with the sink
pointer set, `Wg0.sink_pred`) and the two length loads (pcs 168 and 181: the row's words, their
pointers set by the launch facts); `Pre` allocates their bytes (`paramSink`, `paramTopkLen`,
`paramExtraTopkLen`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Warpgroup 0's `.nc` reads are reads of the launch words** (pcs 156, 168, 181): the sink's
head word, the row's top-k length word, the row's extra length word; only the lane's events before
the read are assumed to be no undefined behaviour. -/
theorem wg0_nc_reads_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} (hal : LaneUbFree X g k) {e : Event}
    (he : X.get (g, k) = some e) (hat : Wg0At L g e.pc) {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .nc a bs) :
    (∃ x, P.sinkBase = some x ∧ e.pc = 156 ∧ ReadsLaunchWord e (x + 4 * (tidOf L g % 64)) bs) ∨
    (∃ x, P.topkLenBase = some x ∧ e.pc = 168 ∧ ReadsLaunchWord e (x + 4 * ctaidY L g) bs) ∨
    (∃ x, P.extraTopkLenBase = some x ∧ e.pc = 181 ∧
      ReadsLaunchWord e (x + 4 * ctaidY L g) bs) := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hg := Frame.lt_of_get hX he
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, hE, hw⟩ := wg0_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  obtain ⟨t, ins, o, hat', hinv, hc', hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  have hs : d.site = .sink ∨ d.site = .lenA ∨ d.site = .lenB := by
    have hK := hE.2
    unfold Wg0.EvK at hK
    revert hK
    generalize d.site = s
    intro hK
    cases s <;> simp [Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv, RdAt, WrAt,
      GenWrAt, GWrAt, hk] at hK ⊢
  have hpc' : e.pc = Wg0.Site.pc d.site := hpcσ
  rcases hs with hs | hs | hs
  · rcases wg0_pred_pre hFw hal hw hg hkl.le hσ with ⟨-, -, d', -, e', -, -, hS⟩ | h
    · obtain ⟨-, hptr, -⟩ := Wg0.sink_pred hS hs
      obtain ⟨x, hx⟩ := len_ptr hptr
      obtain ⟨bs', hr⟩ := Wg0.sink_read hp hx hs hat' hinv hc' hf
      obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
      exact .inl ⟨x, hx, by simpa [hs, Wg0.Site.pc] using hpc', hr⟩
    · rw [hs] at h; cases h
  · rcases w0_bst_pre hFw hal hw hg hσ with ⟨_, _, h, -⟩ | ⟨d', n', h, -, hL, -⟩
    · cases h
    · simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨x, hx⟩ := len_ptr (hL.1 hs)
      obtain ⟨bs', hr⟩ := Wg0.topk_read hp hx hs hat' hinv hc' hf
      obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
      exact .inr (.inl ⟨x, hx, by simpa [hs, Wg0.Site.pc] using hpc', hr⟩)
  · rcases w0_bst_pre hFw hal hw hg hσ with ⟨_, _, h, -⟩ | ⟨d', n', h, -, hL, -⟩
    · cases h
    · simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨x, hx⟩ := len_ptr (hL.2.1 hs)
      obtain ⟨bs', hr⟩ := Wg0.extra_read hp hx hs hat' hinv hc' hf
      obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
      exact .inr (.inr ⟨x, hx, by simpa [hs, Wg0.Site.pc] using hpc', hr⟩)

/-- **Warpgroup 0's `.nc` read covers allocated bytes only.** -/
theorem wg0_ncAlloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : Wg0At L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hrow := (ctaid_lt hp g).2
  rcases wg0_nc_reads_pre hp hX hFw (noUbBefore_of_noUb hnu) he hat hk with
    ⟨x, hx, -, hr⟩ | ⟨x, hx, -, hr⟩ | ⟨x, hx, -, hr⟩
  · exact sink_alloc hp (Nat.mod_lt _ (by norm_num)) hx hk hr l hc
  · exact len_alloc_topk hp hrow hx hk hr l hc
  · exact len_alloc_extra hp hrow hx hk hr l hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
