-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LastBar
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchRound
import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Safety.TableU
import Lemmas.Flow.NthEv
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit

@[expose] public section

/-! # A mandatory rendezvous between two events of data lanes orders them

Two Tensor Memory events of data lanes of one CTA, with the first before fewer mandatory
rendezvous than the second, are ordered: the second's last mandatory rendezvous has a peer of the
same ordinal in the first's lane, which the first precedes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Frame Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A mandatory rendezvous is counted by `mandatory`. -/
public theorem mandatory_step {es : List Event} {i : Nat} {e : Event} (get : es[i]? = some e)
    (pc : e.pc = 2241 ∨ e.pc = 2251 ∨ e.pc = 999 ∨ e.pc = 1012) :
    Softmax.Export.mandatory (es.take (i+1)) = Softmax.Export.mandatory (es.take i) + 1 := by
  unfold Softmax.Export.mandatory
  rw [List.take_add_one, get]
  rcases pc with h|h|h|h <;> simp [h] <;> omega

/-- A Tensor Core event is no mandatory rendezvous. -/
public theorem mandatory_tc (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256)
    {t u pc k} (hx : X.get (t,u) = some ⟨pc,.tc k⟩) :
    Softmax.Export.mandatory ((X.tr t).take (u+1)) =
      Softmax.Export.mandatory ((X.tr t).take u) := by
  have isb := Lib.zero_event hX hb hx (fun f => nofun)
  have pcs : ¬(pc = 2241 ∨ pc = 2251 ∨ pc = 999 ∨ pc = 1012) := by
    rintro (rfl|rfl|rfl|rfl) <;> simp [Execution.isBarId] at isb <;> revert isb <;> decide +kernel
  have : (X.tr t)[u]? = some ⟨pc,.tc k⟩ := hx
  unfold Softmax.Export.mandatory
  rw [List.take_add_one, this]
  have h1 : pc ≠ 2241 := fun h => pcs (.inl h)
  have h2 : pc ≠ 2251 := fun h => pcs (.inr (.inl h))
  have h3 : pc ≠ 999 := fun h => pcs (.inr (.inr (.inl h)))
  have h4 : pc ≠ 1012 := fun h => pcs (.inr (.inr (.inr h)))
  simp [List.countP_append, h1, h2, h3, h4]

/-- `mandatory` of a prefix grows with it. -/
public theorem mandatory_mono (es : List Event) {j k : Nat} (le : j ≤ k) :
    Softmax.Export.mandatory (es.take j) ≤ Softmax.Export.mandatory (es.take k) := by
  unfold Softmax.Export.mandatory
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Flow.countP_take_mono _ es le)
    (Flow.countP_take_mono _ es le)) (Flow.countP_take_mono _ es le))
    (Flow.countP_take_mono _ es le)

/-- **A Tensor Memory event before fewer mandatory rendezvous than another data lane's event is
before it.** The first event is not the last of its lane. -/
public theorem mandatory_handoff (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) {t t' i j pc k}
    (hx : X.get (t,i) = some ⟨pc,.tc k⟩) (lt : t%L.block < 128) (lt' : t'%L.block < 128)
    (cta : t/L.block = t'/L.block) (hy : j < (X.tr t').length)
    (nu : ∀ u ev, u < j → X.get (t',u) = some ev → ∀ f, ev.kind ≠ .ub f)
    (hm : Softmax.Export.mandatory ((X.tr t).take i) <
      Softmax.Export.mandatory ((X.tr t').take j)) :
    i+1 < (X.tr t).length ∧ baseCausality L X (t,i) (t',j) ∧ NoUbBefore X t (i+2) := by
  obtain ⟨jb,pcb,cb,hjb,hbar,hpcb,hmand⟩ := last_bar hX hp.block (t := t') nu (by omega)
  obtain ⟨ib,c',hb,ord,pr1,pr2⟩ := peer_bar hp hX hf safe (t := t') (h := t) hpcb hbar
    (by omega) lt' lt cta
  obtain ⟨i1,a1,a2,a3⟩ := bar_round_facts hp hX hf hbar hpcb
  obtain ⟨i2,b1,b2,b3⟩ := bar_round_facts hp hX hf hb hpcb
  have same : Softmax.Export.mandatory ((X.tr t).take ib) =
      Softmax.Export.mandatory ((X.tr t').take jb) := by
    have : i2 = i1 := by omega
    omega
  have before : i < ib := by
    by_contra! le
    have ne : ib ≠ i := by
      rintro rfl
      rw [hb] at hx
      cases hx
    have step := mandatory_step (es := X.tr t) (i := ib) hb hpcb
    have mono := mandatory_mono (X.tr t) (show ib+1 ≤ i by omega)
    omega
  have hl : ib < (X.tr t).length := (List.getElem?_eq_some_iff.mp hb).1
  exact ⟨by omega,scratch_handoff hp hX hb hbar cta lt lt' ord before (by omega) hy,
    noUbUpto hX hb (fun _ => nofun) (by omega)⟩

/-- **A Tensor Core event before fewer mandatory rendezvous than lane zero's publication is before
it.** The first event is not the last of its lane. -/
public theorem arrival_handoff (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) {p ia l tx cnt rel sc t u pc k}
    (arr : X.get (p,ia) = some ⟨1013,.arrive l tx cnt rel sc⟩) (lp : p%L.block < 128)
    (lt : t%L.block < 128) (cta : t/L.block = p/L.block)
    (hx : X.get (t,u) = some ⟨pc,.tc k⟩)
    (low : Softmax.Export.mandatory ((X.tr t).take u) <
      4*(((X.tr p).take ia).countP (fun e : Event => e.pc == 1013)) + 2) :
    u+1 < (X.tr t).length ∧ baseCausality L X (t,u) (p,ia) ∧ NoUbBefore X t (u+2) := by
  obtain ⟨u0,c,hu0,bar⟩ := Softmax.Export.arrive_source hp hX arr
  obtain ⟨pn,-⟩ := Softmax.Export.arrival_polls hp hX hf arr
  obtain ⟨i,-,b2,b3⟩ := bar_round_facts hp hX hf bar (Or.inr (Or.inr (Or.inr rfl)))
  subst hu0
  rw [poll_keeps 2239 bar] at pn
  have step := mandatory_step (es := X.tr p) (i := u0) bar (Or.inr (Or.inr (Or.inr rfl)))
  apply mandatory_handoff hp hX hf safe hx lt lp cta (List.getElem?_eq_some_iff.mp arr).1
    (fun v ev hv get => Frame.noUbBefore_of_get hX arr v hv ev get)
  simp [barPos] at b3
  dsimp only
  omega

end PTX.Kernels.InklingRelDecode.Proof.Tmem
