-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.BarrierCount
public import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent

@[expose] public section

/-! # The `tcgen05` data events of the Softmax loop

A loop round makes four of them (`tcgen05.ld` of S and its wait, `tcgen05.st` of P and its wait)
and, when the O rescale is taken, four more (`tcgen05.ld` of O and its wait, `tcgen05.st` of O and
its wait). `softCount s i R P` is the number of events at the data position `P` before a thread at
site `s` of round `i`, when `R` visits of the optional rendezvous (pc 2326) have been counted:
the rescale's four are counted by `R`, the first two before the visit and the last two after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open _root_.PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

/-- The sites after the S load in a round. -/
def afterLdS : Site → Bool
  | .waitLd | .shfl5 | .shfl6 | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10
  | .bar23 | .ldL | .shfl11 | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20
  | .tmemSt | .tmemWait | .bar21 | .arrive => true
  | _ => false

/-- The sites after the wait for the S load in a round. -/
def afterWaitLd : Site → Bool
  | .waitLd => false
  | s => afterLdS s

def afterTmemSt : Site → Bool
  | .tmemWait | .bar21 | .arrive => true
  | _ => false

def afterTmemWait : Site → Bool
  | .bar21 | .arrive => true
  | _ => false

/-- The number of events at the data position `P` before site `s` of round `i`. -/
def softCount (s : Site) (i R P : Nat) : Nat :=
  if P = 1265 then i + (afterLdS s).toNat
  else if P = 1298 then i + (afterWaitLd s).toNat
  else if P = 2260 then R + (decide (s = .waitLdO ∨ s = .bar24)).toNat
  else if P = 2261 then R + (decide (s = .bar24)).toNat
  else if P = 2328 then R - (decide (s = .stO)).toNat
  else if P = 2329 then R - (decide (s = .stO ∨ s = .waitStO)).toNat
  else if P = 1009 then i + (afterTmemSt s).toNat
  else if P = 1010 then i + (afterTmemWait s).toNat
  else 0

/-- After the optional rendezvous the visit is counted. -/
def visited : Site → Bool
  | .stO | .waitStO => true
  | _ => false

private theorem loop_afterLdS (e t i) : afterLdS (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

private theorem loop_afterWaitLd (e t i) : afterWaitLd (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

private theorem loop_afterTmemSt (e t i) : afterTmemSt (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

private theorem loop_afterTmemWait (e t i) : afterTmemWait (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

private theorem loop_visited (e t i) : visited (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

private theorem loop_stO (e t i) : (loopSite e t i = .stO) = False := by
  unfold loopSite; split <;> first | (simp; done) | (split <;> simp)

private theorem loop_waitStO (e t i) : (loopSite e t i = .waitStO) = False := by
  unfold loopSite; split <;> first | (simp; done) | (split <;> simp)

private theorem loop_waitLdO (e t i) : (loopSite e t i = .waitLdO) = False := by
  unfold loopSite; split <;> first | (simp; done) | (split <;> simp)

private theorem loop_bar24 (e t i) : (loopSite e t i = .bar24) = False := by
  unfold loopSite; split <;> first | (simp; done) | (split <;> simp)

theorem count_next {ent L g d ev dn} (R P : Nat) (hP : P ∈ Lib.dataPcs)
    (live : visited d.site = true → 1 ≤ R)
    (step : Control.next ent L g d ev = some (some dn)) :
    softCount dn.site dn.i (R + (d.site.pc == 2326).toNat) P =
      softCount d.site d.i R P + (d.site.pc == P).toNat ∧
    (visited dn.site = true → 1 ≤ R + (d.site.pc == 2326).toNat) := by
  obtain ⟨s,i,v⟩ := d
  simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false] at hP
  cases s <;> simp only [Control.next,advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp only [softCount] at live ⊢
  all_goals try simp only [loop_afterLdS,loop_afterWaitLd,loop_afterTmemSt,loop_afterTmemWait,
    loop_visited,loop_stO,loop_waitStO,loop_waitLdO,loop_bar24] at live ⊢
  all_goals try simp only [afterLdS,afterWaitLd,afterTmemSt,afterTmemWait,visited,Site.pc]
    at live ⊢
  all_goals rcases hP with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp (config := {decide := true})
    [Flow.tmemWait_2,Flow.tmemStore_1,Flow.tmemWait_3] at live ⊢
  all_goals try (simp only [Bool.toNat, beq_iff_eq, Bool.cond_eq_ite] at live ⊢
                 split_ifs <;> omega)
  all_goals omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax
