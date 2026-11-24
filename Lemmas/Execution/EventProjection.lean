-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ControlProjection

@[expose] public section

namespace PTX.Proof
open PTX
noncomputable section

/-- Agreement of event kind and control fields, allowing either run to fault. -/
inductive OutRelated (S : Nat → Bool) : Out → Out → Prop
  | fault_left (f : Fault) (o : Out) : OutRelated S (.ev (.ub f)) o
  | fault_right (o : Out) (f : Fault) : OutRelated S o (.ev (.ub f))
  | tau {t u} : ControlAgree S t u → OutRelated S (.tau t) (.tau u)
  | read {a k k'} :
      (∀ bs cs, (k bs).fault ≠ none ∨ (k' cs).fault ≠ none ∨ ControlAgree S (k bs) (k' cs)) →
      OutRelated S (.ev (.read a k)) (.ev (.read a k'))
  | nc {a k k'} :
      (∀ bs cs, (k bs).fault ≠ none ∨ (k' cs).fault ≠ none ∨ ControlAgree S (k bs) (k' cs)) →
      OutRelated S (.ev (.readNC a k)) (.ev (.readNC a k'))
  | write {a bs cs t u} : ControlAgree S t u →
      OutRelated S (.ev (.write a bs t)) (.ev (.write a cs u))
  | bar {id t u count} : ControlAgree S t u →
      OutRelated S (.ev (.bar id t count)) (.ev (.bar id u count))
  | shfl {m a a' b c k k'} : (∀ v ok v' ok', ControlAgree S (k v ok) (k' v' ok')) →
      OutRelated S (.ev (.shfl m a b c k)) (.ev (.shfl m a' b c k'))
  | exit : OutRelated S (.ev .exit) (.ev .exit)

namespace ControlAgree
variable {S : Nat → Bool} {t u : TState} {L : Launch} {g : Nat}

theorem loadTmpl {A : List Assumption} {sp : Space} {nc : Bool} {w : Nat}
    {ds : List Nat} {base : Nat} {off : Int} (h : ControlAgree S t u)
    (hb : S base = true) (hd : ∀ r ∈ ds, S r = false) :
    OutRelated S (.ev (PTX.loadTmpl A L g t sp nc w ds base off))
      (.ev (PTX.loadTmpl A L g u sp nc w ds base off)) := by
  unfold PTX.loadTmpl
  rw [h.effAddr hb, h.sub, h.pc]
  split
  · exact .fault_left _ _
  · split
    · split
      · exact .nc (fun bs cs => h.afterLoad hd)
      · exact .fault_left _ _
    · exact .read (fun bs cs => h.afterLoad hd)

theorem storeTmpl {sp : Space} {w : Nat} {base : Nat} {off : Int} {srcs : List Opnd}
    (h : ControlAgree S t u) (hb : S base = true) :
    OutRelated S (.ev (PTX.storeTmpl L g t sp w base off srcs))
      (.ev (PTX.storeTmpl L g u sp w base off srcs)) := by
  unfold PTX.storeTmpl
  rw [h.effAddr hb, h.sub]
  split
  · exact .fault_left _ _
  · split
    · exact .fault_left _ _
    · split
      · exact .fault_left _ _
      · split
        · exact .fault_right _ _
        · exact .write h.afterStore

theorem barTmpl {a : Opnd} {count : Option Opnd} (h : ControlAgree S t u)
    (ha : staticArg S a = true) (hc : ∀ b ∈ count.toList, staticArg S b = true) :
    OutRelated S (.ev (PTX.barTmpl L g t a count)) (.ev (PTX.barTmpl L g u a count)) := by
  unfold PTX.barTmpl
  rw [h.readBits ha]
  split
  · exact .fault_left _ _
  · split
    · exact .fault_left _ _
    · cases count with
      | none => exact .bar h.next
      | some b =>
        dsimp only
        rw [h.readBits (hc b (by simp))]
        split
        · exact .fault_left _ _
        · split
          · exact .bar h.next
          · exact .fault_left _ _

theorem shflTmpl {m : ShflMode} {d : Nat} {p : Option Nat} {a b c mask : Opnd}
    (h : ControlAgree S t u) (hd : S d = false) (hp : ∀ r ∈ p.toList, S r = false)
    (hb : staticArg S b = true) (hc : staticArg S c = true) (hm : staticArg S mask = true) :
    OutRelated S (.ev (PTX.shflTmpl L g t m d p a b c mask))
      (.ev (PTX.shflTmpl L g u m d p a b c mask)) := by
  have hk : ∀ v ok v' ok', ControlAgree S
      (PTX.next (match p with
        | some p => PTX.setReg (PTX.setReg t d v) p (.pred ok) | none => PTX.setReg t d v))
      (PTX.next (match p with
        | some p => PTX.setReg (PTX.setReg u d v') p (.pred ok') | none => PTX.setReg u d v')) := by
    intro v ok v' ok'
    cases p with
    | none => exact (h.setReg (.inl hd)).next
    | some r => exact ((h.setReg (.inl hd)).setReg (.inl (hp r (by simp)))).next
  unfold PTX.shflTmpl
  rw [h.readBits hb, h.readBits hc, h.readBits hm]
  cases hm : PTX.readBits L g u 32 mask <;>
    cases ha : PTX.readValue L g t 32 a <;>
    cases ha' : PTX.readValue L g u 32 a <;>
    cases hb : PTX.readBits L g u 32 b <;>
    cases hc : PTX.readBits L g u 32 c <;> simp only []
  all_goals try first | exact .fault_left _ _ | exact .fault_right _ _
  rename_i mv av av' bv cv
  by_cases hmask : mv.toNat = 2 ^ 32 - 1 ∧ L.block % 32 = 0
  · simp only [ite_eq_left hmask]
    by_cases hv : av.bytes = 4
    · simp only [ite_eq_left hv]
      by_cases hv' : av'.bytes = 4
      · simp only [ite_eq_left hv']; exact .shfl hk
      · simp only [ite_eq_right hv']; exact .fault_right _ _
    · simp only [ite_eq_right hv]; exact .fault_left _ _
  · simp only [ite_eq_right hmask]; exact .fault_left _ _

end ControlAgree
end
end PTX.Proof
