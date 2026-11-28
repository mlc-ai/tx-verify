-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Softmax.TcCount
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.TcCount
import Lemmas.Data.CountRank
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # The probability stores before a rendezvous of a softmax lane, by round

At an event of the softmax loop at site `s` of round `i` the lane has polled `s_ready`
`i + 1` times once past the score load and made `i` probability stores, one more once past the
store. So the stores before the rendezvous at pc 1012 of round `i` are those of the rounds
`0 … i`, each exactly once (`store_of_round`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat}

private theorem soft_ledger (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc k} (he : X.get (g, j) = some ⟨pc, k⟩) (hk : ∀ f, k ≠ .ub f)
    (lo : 574 < pc) (hi : pc < 2331) :
    ∃ (s : Site) (i : Nat), pc = s.pc ∧
      pollRound 1257 ((X.tr g).take j) = i + s.afterS.toNat ∧
      ((X.tr g).take j).countP (fun x => x.pc == 1009) = i + (afterTmemSt s).toNat := by
  obtain ⟨w, ent, d, n', hs, hpd⟩ := at_site hp hX he hk lo hi
  have hg := Frame.lt_of_get hX he
  have tbl := reached_table hf hg (noUbBefore_of_get hX he) hs
  have cnt (key : Cls) : n' key = ((X.tr g).take j).countP (cls key) := fcount hs key
  have ref := tbl.2
  change Softmax.Ref _ d (softCounts n') at ref
  have sc := congrArg Softmax.Cnt.s ref.ledger
  change n' (.poll 1257) = d.i + d.site.afterS.toNat at sc
  rw [cnt] at sc
  have hle := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨cntInv, -⟩ := tc_inv hp hX hf hg hle hs (noUbBefore_of_get hX he)
  have c9 := cntInv 1009 (by simp [Lib.dataPcs])
  simp only [Softmax.softCount] at c9
  rw [cnt] at c9
  refine ⟨d.site, d.i, hpd, sc, ?_⟩
  simp only [cls] at c9
  exact c9

private theorem site_1012 (s : Site) (h : s.pc = 1012) :
    s.afterS = true ∧ afterTmemSt s = true := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_1009 (s : Site) (h : s.pc = 1009) :
    s.afterS = true ∧ afterTmemSt s = false := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **Every round up to a rendezvous at pc 1012 has its probability store before it.** -/
theorem store_of_round (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {c : Option Nat} (bar : X.get (g, j) = some ⟨1012, .bar 0 c .sync⟩)
    (nu : NoUbBefore X g j) {i r : Nat} (rd : pollRound 1257 ((X.tr g).take j) = i + 1)
    (hr : r ≤ i) :
    ∃ k kd, k < j ∧ X.get (g, k) = some ⟨1009, kd⟩ ∧ (∀ f, kd ≠ .ub f) ∧
      pollRound 1257 ((X.tr g).take k) = r + 1 := by
  obtain ⟨s, i0, hs, h1, h2⟩ := soft_ledger hp hX hf bar (fun f => nofun) (by omega) (by omega)
  obtain ⟨a1, a2⟩ := site_1012 s hs.symm
  simp only [a1, a2, Bool.toNat_true] at h1 h2
  obtain ⟨k, hk, e, hget, hpe, hc⟩ := exists_rank (fun x : Event => x.pc == 1009) (X.tr g) j r
    (by omega)
  have he : X.get (g, k) = some e := hget
  have hpc : e.pc = 1009 := by simpa using hpe
  obtain ⟨pc, kd⟩ := e
  simp only at hpc
  subst hpc
  have clean := nu k hk _ he
  obtain ⟨s', i1, hs', h3, h4⟩ := soft_ledger hp hX hf he clean (by omega) (by omega)
  obtain ⟨b1, b2⟩ := site_1009 s' hs'.symm
  simp only [b1, b2, Bool.toNat_true, Bool.toNat_false] at h3 h4
  exact ⟨k, kd, hk, he, clean, by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
