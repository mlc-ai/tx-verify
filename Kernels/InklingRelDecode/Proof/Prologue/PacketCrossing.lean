-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.BarrierCrossing
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow Control

def packetSite (b : Fin 3) : Option (Fin 4) → Site
  | none => .arr b
  | some j => .ptc b j

private def protects (target s t : Site) : Prop :=
  s.pc≤target.pc → target.pc<t.pc → s=target

private instance (target s t : Site) : Decidable (protects target s t) :=
  inferInstanceAs (Decidable (_ → _ → _))

private def direct (s : Site) (single winner : Bool) : List Site :=
  match s with
  | .bar2 => [.pb 0 0]
  | .pb b 0 => [if single then .arr b else .lb b 0]
  | .pb b 1 => [.psh b]
  | .pb b 2 => [.pel b 1]
  | .pb b 3 => [.pel b 2]
  | .pb b 4 => [.pel b 3]
  | .arr b => [.lb b 0]
  | .lb b 0 => [.pb b 1]
  | .lb b 1 => [.pb b 3]
  | .psh b => [.pel b 0]
  | .pel b j => if winner then [.ptc b j] else []
  | _ => []

private theorem direct_ok (b : Fin 3) (op : Option (Fin 4)) (s : Site) (single winner : Bool)
    (a : op=none → single=true) (p : op.isSome → winner=true) :
    ∀ t ∈ direct s single winner, protects (packetSite b op) s t := by
  have h : (direct s single winner).all (fun t => decide (protects (packetSite b op) s t)) := by
    cases s <;> revert b op single winner
    all_goals repeat' first | decide +kernel | (rename_i i; revert i)
  exact fun t mem => of_decide_eq_true (List.all_eq_true.mp h t mem)

private def after (n : Fin 4) (b : Fin 3) : Fin 4 → Site
  | 0 => .pb b 2
  | 1 => .lb b 1
  | 2 => .pb b 4
  | 3 => if h : b.val+1<3 then
      if (if b.val=0 then n.val≠1 else ¬n.val<3) then .pb ⟨_,h⟩ 0 else .exit
    else .exit

private theorem after_ok (z : Fin 3) (op : Option (Fin 4)) (n : Fin 4) (b : Fin 3) (j : Fin 4)
    (active : z.val<n.val) :
    protects (packetSite z op) (.ptc b j) (after n b j) ∧
      (op=none → protects (packetSite z op) (.pel b j) (after n b j)) := by
  revert z op n b j
  decide +kernel

private theorem after_le (n : Nat) (d : D) (tid : Nat) (b : Fin 3) (j : Fin 4) :
    (afterCopy d tid n b j).pc≤(after ⟨min 3 n,by omega⟩ b j).pc := by
  fin_cases j <;> simp only [afterCopy,after] <;> try rfl
  have one : (min 3 n≠1) ↔ n≠1 := by omega
  have three : (min 3 n<3) ↔ n<3 := by omega
  simp only [one,three]
  split_ifs <;> first | rfl | exact (Site.pc_range _).2

private def packet : Site → Bool
  | .bar2 | .pb .. | .arr .. | .lb .. | .psh .. | .pel .. | .ptc .. => true
  | _ => false

private theorem middle (s : Site) : 180≤s.pc → s.pc≤315 → packet s := by
  cases s <;> repeat' first | decide +kernel | (rename_i i; revert i)

theorem packet_cross {Q L g d e dn} (step : Control.next Q L g d e=some (some dn))
    (z : Fin 3) (op : Option (Fin 4))
    (active : 41<d.site.pc → z.val<preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)
    (arr : op=none → g%L.block%128=0)
    (copy : op.isSome → g%L.block%128<64 ∧ ∀ mask inst l, e.kind=.elect mask inst l → l=laneOf L g)
    (lo : d.site.pc≤(packetSite z op).pc) (hi : (packetSite z op).pc<dn.site.pc) :
    d.site=packetSite z op := by
  have range : ∀ z op, 180<(packetSite z op).pc ∧ (packetSite z op).pc≤315 := by decide
  obtain ⟨lb,ub⟩ := range z op
  by_cases early : d.site.pc<180
  · have bad := crosses_barrier step (by omega) (by omega)
    rw [bad] at early; exact (Nat.lt_irrefl 180 early).elim
  have mid := middle d.site (by omega) (by omega)
  have act := active (by omega)
  let n := preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d
  have last (b : Fin 3) (j : Fin 4) := after_ok z op ⟨min 3 n,by omega⟩ b j
    (show z.val<min 3 n from by have := z.isLt; change z.val<n at act; omega)
  let single := decide (g%L.block%128=0)
  have single_ok (h : op=none) : single=true := decide_eq_true (arr h)
  obtain ⟨s,f,l,v,w,sh⟩ := d
  change s.pc≤_ at lo
  cases s <;> try contradiction
  case bar2 =>
    simp only [Control.next] at step
    split at step
    · omega
    · cases step
      exact direct_ok z op .bar2 single true single_ok (by simp) _ (by simp [direct]) lo hi
  case pb b i =>
    fin_cases i <;> simp only [Control.next] at step <;> cases step
    all_goals apply direct_ok z op _ single true single_ok (by simp) _ _ lo hi
    all_goals simp [direct,single]
  case arr b =>
    cases step
    exact direct_ok z op (.arr b) single true single_ok (by simp) _ (by simp [direct]) lo hi
  case lb b j =>
    fin_cases j <;> cases step
    all_goals apply direct_ok z op _ single true single_ok (by simp) _ _ lo hi
    all_goals simp [direct]
  case psh b =>
    cases step
    exact direct_ok z op (.psh b) single true single_ok (by simp) _ (by simp [direct]) lo hi
  case ptc b j =>
    cases step
    exact (last b j).1 lo (hi.trans_le (after_le ..))
  case pel b j =>
    simp only [Control.next] at step
    split at step <;> try contradiction
    rename_i mask inst ld kd
    cases step
    split at hi
    · exact direct_ok z op (.pel b j) single true single_ok (by simp) _ (by simp [direct]) lo hi
    · have no : op=none := by
        cases op with
        | none => rfl
        | some i =>
          obtain ⟨tid,win⟩ := copy rfl
          simp [tid,win _ _ _ kd] at *
      exact (last b j).2 no lo (hi.trans_le (after_le ..))

end PTX.Kernels.InklingRelDecode.Proof.Prologue
