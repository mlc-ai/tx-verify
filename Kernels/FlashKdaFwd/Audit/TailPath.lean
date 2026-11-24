-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TailRun

/-! A successful register replay is a path of actual PTX thread steps. The list contains
the destinations still to be written, so the path records both the order and the contents. -/
namespace FlashKda.Tail
open PTX
noncomputable section

def advancing (k : Kernel) (g : Nat) (p q : TState × List Nat) : Prop :=
  (Tau k [] launch g p.1 q.1 ∧ p.2 = q.2) ∨
  ∃ (a : Acc) (bs : List Byte),
    EStep k [] launch g p.1 ⟨p.1.pc,.wr a bs⟩ (some q.1) ∧
    a.loc.space = .shared ∧ a.loc.cta = g/256 ∧ a.size = 2 ∧
    bs.map byteBits = [some 0,some 0] ∧ p.2 = a.loc.addr :: q.2

theorem reaches (mode : Bool) (k : Kernel) (g fuel : Nat) (t : TState) (writes : List Nat)
    (h : clearWrites mode k g fuel t = some writes) :
    ∃ last, last.pc = finish mode ∧
      Relation.ReflTransGen (advancing k g) (t,writes) (last,[]) := by
  induction fuel generalizing t writes with
  | zero => simp [clearWrites] at h
  | succ n ih =>
    by_cases stop : t.pc = finish mode
    · simp [clearWrites,stop] at h
      subst writes
      exact ⟨t,stop,.refl⟩
    by_cases inside : start mode ≤ t.pc ∧ t.pc < finish mode
    · cases observed : out k [] launch g t with
      | tau next =>
        simp [clearWrites,stop,inside,observed] at h
        obtain ⟨last,endPc,rest⟩ := ih next _ h
        have first : advancing k g (t,writes) (next,writes) := Or.inl ⟨observed,rfl⟩
        exact ⟨last,endPc,.head first rest⟩
      | ev template =>
        cases template <;> simp [clearWrites,stop,inside,observed] at h
        rename_i a bs next
        by_cases zero : a.loc.space = .shared ∧ a.loc.cta = g/256 ∧ a.size = 2 ∧
            bs.map byteBits = [some 0,some 0]
        · cases rec : clearWrites mode k g n next with
          | none => simp [guard,zero,rec] at h
          | some tail =>
            simp [guard,zero,rec] at h
            subst writes
            obtain ⟨last,endPc,rest⟩ := ih next _ rec
            have first : advancing k g (t,a.loc.addr :: tail) (next,tail) :=
              Or.inr ⟨a,bs,⟨.write a bs next,observed,rfl,rfl⟩,
                zero.1,zero.2.1,zero.2.2.1,zero.2.2.2,rfl⟩
            exact ⟨last,endPc,.head first rest⟩
        · simp [guard,zero] at h
    · simp [clearWrites,stop,inside] at h

end
end FlashKda.Tail
