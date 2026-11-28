-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {g : Nat}

abbrev workerState {Q L g} (w : Value) (x : BitVec 64) (r : Worker)
    (d : (workerFrag Q L g w x r).D) (n : Cls → Nat) : (thread Q L g).D :=
  (.inr ⟨.inl (.dispatch w x), .inr ⟨r, d⟩⟩, n)

abbrev softState {Q L g} (w : Value) (e : Softmax.Control.Entry) (s : Softmax.Control.D)
    (n : Cls → Nat) : (thread Q L g).D := (.inr ⟨.inl (.prologue w),.inr ⟨e,.inl s⟩⟩,n)

abbrev epiState {Q L g} (w : Value) (e : Softmax.Control.Entry) (s : Epilogue.Control.D)
    (n : Cls → Nat) : (thread Q L g).D := (.inr ⟨.inl (.prologue w),.inr ⟨e,.inr ⟨(),s⟩⟩⟩,n)

abbrev proState {Q L g} (w : Value) (s : Prologue.Control.D) (n : Cls → Nat) :
    (thread Q L g).D := (.inr ⟨.inl (.prologue w),.inl s⟩,n)

/-- Interior PC intervals exclude shared handoff PCs. -/
structure Placement (d : (thread Q L g).D) (p : Nat) : Prop where
  worker : 2344 < p → p < 2557 → p ≠ 2422 →
    ∃ w x r s n, d = workerState w x r s n
  softmax : 574 < p → p < 2331 → ∃ w e s n, d = softState w e s n
  prologue : 27 < p → p < 574 → ∃ w s n, d = proState w s n

  epilogue : 2565 ≤ p → p < 2853 → (thread Q L g).inv d → ∃ w e s n, d = epiState w e s n

  startup : p < 27 → ∃ s n, d = (.inl s,n)

  dispatchRead : p=2340 → ∃ w x r n, d=(.inr ⟨.inl (.dispatch w x),.inl ⟨.read,r⟩⟩,n)

private theorem apart (p : Nat) (worker : ¬ (2344 < p ∧ p < 2557 ∧ p ≠ 2422))
    (soft : ¬ (574 < p ∧ p < 2331)) (pro : ¬ (27 < p ∧ p < 574))
    (epi : ¬ (2565 ≤ p ∧ p < 2853)) (d : (thread Q L g).D)
    (hs : p < 27 → ∃ s n, d = (.inl s,n))
    (hd : p=2340 → ∃ w x r n, d=(.inr ⟨.inl (.dispatch w x),.inl ⟨.read,r⟩⟩,n)) :
    Placement d p :=
  ⟨fun a b c => (worker ⟨a,b,c⟩).elim,fun a b => (soft ⟨a,b⟩).elim,
    fun a b => (pro ⟨a,b⟩).elim,fun a b _ => (epi ⟨a,b⟩).elim,hs,hd⟩

theorem state_role (d : (thread Q L g).D) : Placement d ((thread Q L g).pc d) := by
  obtain ⟨s,n⟩ := d
  rcases s with ⟨s,tm,x,w⟩ | ⟨r,s⟩
  · apply apart s.pc
    case hs => exact fun _ => ⟨_,_,rfl⟩
    case hd =>
      intro eq; exfalso; revert eq
      cases s <;> first | decide | (rename_i r; cases r <;> decide)
    all_goals cases s <;> first | decide | (rename_i r; cases r <;> decide)
  · rcases r with r | r
    · cases r with
      | prologue w =>
        rcases s with s|⟨e,s|⟨⟨⟩,s⟩⟩
        · have range := s.site.pc_range
          apply Placement.mk (p := s.site.pc)
          · omega
          · omega
          · exact fun _ _ => ⟨w,s,n,rfl⟩
          · omega
          · omega
          · omega
        · have range := s.site.pc_range
          have lower : 574 ≤ s.site.pc := by
            rcases range with h|h
            · exact h.1
            · rw [h]; decide
          apply Placement.mk (p := s.site.pc)
          · rcases range with h|h
            · omega
            · rw [h]; change 2344 < 2565 → 2565 < 2557 → _; omega
          · exact fun _ _ => ⟨w,e,s,n,rfl⟩
          · omega
          · intro lo _ inv
            rcases range with h|h
            · omega
            · have no : epiExit s = none := inv.2
              simp [epiExit,h] at no
          · omega
          · rcases range with h|h
            · omega
            · rw [h]; intro eq; cases eq
        · have range := s.site.pc_range
          apply Placement.mk (p := s.site.pc)
          · omega
          · omega
          · omega
          · exact fun _ _ _ => ⟨w,e,s,n,rfl⟩
          · omega
          · omega
      | dispatch w x =>
        rcases s with ⟨s,i⟩ | ⟨r,s⟩
        · apply apart s.pc
          case hs => intro h; exact False.elim ((by cases s <;> decide : ¬ s.pc < 27) h)
          case hd => cases s <;> intro eq <;> first | exact ⟨w,x,i,n,rfl⟩ | cases eq
          all_goals cases s <;> decide
        · have bounds : 2337 ≤ (workerFrag Q L g w x r).pc s ∧
              (workerFrag Q L g w x r).pc s < 2565 := by
            cases r with
            | mma =>
              change 2337 ≤ s.site.pc ∧ s.site.pc < 2565
              generalize s.site = site
              cases site <;> first | decide | (rename_i j; fin_cases j <;> decide)
            | loader =>
              change 2337 ≤ s.site.pc ∧ s.site.pc < 2565
              generalize s.site = site
              cases site <;> first | decide | (rename_i j; fin_cases j <;> decide) |
                (rename_i j b; fin_cases j <;> cases b <;> decide)
          apply Placement.mk (p := (workerFrag Q L g w x r).pc s)
          · exact fun _ _ _ => ⟨w,x,r,s,n,rfl⟩
          · omega
          · omega
          · omega
          · omega
          · intro eq
            exfalso
            cases r <;> change s.site.pc=2340 at eq <;> generalize s.site=z at eq <;> revert eq
            all_goals cases z <;> repeat' first | decide +kernel | (rename_i j; revert j)
    · cases r with
      | dp => exact apart 27 (by decide) (by decide) (by decide) (by decide) _ (by omega) (by omega)
      | worker =>
        exact apart 2337 (by decide) (by decide) (by decide) (by decide) _ (by omega) (by omega)

end PTX.Kernels.InklingRelDecode.Proof
