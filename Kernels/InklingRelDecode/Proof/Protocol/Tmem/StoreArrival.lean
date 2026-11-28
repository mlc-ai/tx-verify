-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Handoff
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.LdWait

@[expose] public section

/-! # A softmax store is done before lane zero's publication of its round or a later one

The store's `wait::st` is before the thread's rendezvous at pc 1012 of the round of the
publication (its own round is not later), which has the ordinal of lane zero's rendezvous before the
publication: so the wait is before the publication (`arrival_handoff`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Frame Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A store's `wait::st` is before lane zero's publication of its round or a later one.** -/
public theorem store_arrival (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {p ia l tx cnt rel sc t sk pcy a vals sh}
    (arr : X.get (p,ia) = some ⟨1013,.arrive l tx cnt rel sc⟩) (lp : p%L.block < 128)
    (lt : t%L.block < 128) (cta : t/L.block = p/L.block)
    (hy : X.get (t,sk) = some ⟨pcy,.tc (.st a vals sh)⟩) (hpcy : pcy = 1009 ∨ pcy = 2328)
    {r} (rd : pollRound 1257 ((X.tr t).take sk) = r+1)
    (hr : r ≤ ((X.tr p).take ia).countP (fun e : Event => e.pc == 1013)) :
    (∃ pcw, X.get (t,sk+1) = some ⟨pcw,.tc .waitSt⟩) ∧ baseCausality L X (t,sk+1) (p,ia) := by
  have tc : isTcColl ⟨pcy,.tc (.st a vals sh)⟩ = true := by
    rcases hpcy with rfl|rfl <;> rfl
  obtain ⟨i,w,s1,-,s3,-⟩ := Export.st_round hp hX hf base hy tc hpcy
  have low : Softmax.Export.mandatory ((X.tr t).take sk) <
      4*(((X.tr p).take ia).countP (fun e : Event => e.pc == 1013)) + 2 := by
    rcases hpcy with rfl|rfl <;> simp at s3 <;> omega
  obtain ⟨len,-,nu⟩ := arrival_handoff hp hX hf safe arr lp lt cta hy low
  obtain ⟨e1,g1⟩ : ∃ e1, X.get (t,sk+1) = some e1 :=
    ⟨_,List.getElem?_eq_some_iff.mpr ⟨len,rfl⟩⟩
  obtain ⟨pcw,rfl⟩ := Export.st_wait hp hX hf nu hpcy hy g1
  refine ⟨⟨pcw,g1⟩,(arrival_handoff hp hX hf safe arr lp lt cta g1 ?_).2.1⟩
  rw [mandatory_tc hX hp.block hy]
  exact low

end PTX.Kernels.InklingRelDecode.Proof.Tmem
