-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Ledger
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Epilogue.WorkPicked
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # An output lane that exits issued its work item's eight boxes -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem start_not_out {s : Startup.D} {e : Event} (hev : Startup.Ev L g s e)
    (hi : exit L g s = none) (hub : ∀ f, e.kind ≠ .ub f) :
    e.kind ≠ .exit ∧ Epilogue.isStore e = false := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | sh j => fin_cases j <;> simp only [Startup.Ev] at hev <;> shape_destruct hev <;>
      simp_all [Epilogue.isStore]
  | elect j => simp only [Startup.Ev] at hev; shape_destruct hev <;> simp_all [Epilogue.isStore]
  | init q => simp only [Startup.Ev] at hev; shape_destruct hev <;> simp_all [Epilogue.isStore]
  | fence => simp only [Startup.Ev] at hev; shape_destruct hev; simp_all [Epilogue.isStore]
  | bar => simp only [Startup.Ev] at hev; shape_destruct hev; simp_all [Epilogue.isStore]
  | enter r => simp [exit] at hi

/-- **An output lane of a CTA with a work item that exits issued every box of the item.** -/
theorem out_writes (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 13) {b pc : Nat} (hb : b < p.batch)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (st : Fin 2) (bx : Fin 4) :
    ∃ j addr, ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧
      X.TensorStoreIssue (g, j) addr (Epilogue.writebackStoreSpec p L g b
        (Epilogue.assignedCoordinates p b (g / L.block)).2
        (Epilogue.assignedCoordinates p b (g / L.block)).1 st bx) := by
  have hg := Frame.lt_of_get hX he
  rcases Epilogue.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, hub, -, -, hev⟩
  · exact ((start_not_out hev hi.2 fun f h => by cases h).1 rfl).elim
  obtain ⟨hF, hL, -⟩ := Epilogue.fits hp hX hg hw hσ
  obtain ⟨l, hs⟩ := epi_exit hev
  cases l with
  | false => exact (Epilogue.no_exit_of_work hp hg hb hhi hF hs).elim
  | true =>
    have hN : ((X.tr g).take k).countP Epilogue.isStore = 8 := by
      have h2 := count hσ .store
      rw [hL] at h2
      simpa [Epilogue.stores, hs, Epilogue.written, cls] using h2
    have hU : ((X.tr g).take k).countP (cls L g .ub) = 0 := (count hσ .ub).trans hub
    obtain ⟨j, e, hj, hst, hc⟩ := MbarRing.Slot.exists_nth_countP Epilogue.isStore
      (xs := (X.tr g).take k) (c := 4 * st.val + bx.val)
      (by rw [hN]; have := st.isLt; have := bx.isLt; omega)
    have hjk : j < k := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.length_take] at this
      omega
    have hej : X.get (g, j) = some e := by
      rw [List.getElem?_take_of_lt hjk] at hj
      exact hj
    rw [List.take_take, Nat.min_eq_left hjk.le] at hc
    have hne : ∀ f, e.kind ≠ .ub f := by
      intro f hf
      have := List.countP_eq_zero.mp hU e (List.mem_of_getElem? hj)
      simp [cls, hf] at this
    rcases Epilogue.open_ev hp hX hFw hw hej hne with ⟨s, n', -, -, -, hi, hev'⟩ |
      ⟨d', n', hσ', -, -, -, hev'⟩
    · rw [(start_not_out hev' hi.2 hne).2] at hst
      cases hst
    obtain ⟨hF', hL', -⟩ := Epilogue.fits hp hX hg hw hσ'
    have h2 : Epilogue.stores d' = 4 * st.val + bx.val := by
      rw [← hL', ← count hσ' .store]
      exact hc
    obtain ⟨epc, kind⟩ := e
    cases kind <;> simp only [Epilogue.isStore, Bool.false_eq_true] at hst
    case ub f => exact (hne f rfl).elim
    case tensorStore addr s =>
    have hs' : ∃ st' bx', d'.site = .store st' bx' := by
      obtain ⟨site, rest⟩ := d'
      cases site <;> simp only [Epilogue.Ev, Epilogue.isStore, reduceCtorEq, exists_false,
        or_self] at hev'
      exact ⟨_, _, rfl⟩
    obtain ⟨st', bx', hs'⟩ := hs'
    simp only [Epilogue.stores, hs'] at h2
    obtain rfl : st' = st := Fin.ext (by have := bx'.isLt; have := bx.isLt; omega)
    obtain rfl : bx' = bx := Fin.ext (by omega)
    obtain ⟨-, b', hb', hlo', hhi', rfl⟩ := Epilogue.store_at hp hX hej hσ' hF' hs'
    exact ⟨j, addr, b', hb', hlo', hhi', epc, hej⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
