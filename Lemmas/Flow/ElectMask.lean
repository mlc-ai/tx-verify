-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotInit
public import Lemmas.Flow.CommitTarget

@[expose] public section

/-! # The mask of an election

A proof tool. Only `elect.sync` fires an election event (`elect_op`), and the event's mask is the
value of the instruction's mask operand (`elect_mask`). This holds of every thread's every event,
whatever machine follows it: an event of a thread's run is fired at a state whose program counter
is the event's, by the instruction at that position (`Run.estep`). A proof that every election
of a kernel uses one mask checks that the mask operand of each `elect.sync` of its code evaluates
to it (`electMaskOk`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template that is not an election. -/
def NotElect : Tmpl → Prop
  | .elect .. => False
  | _ => True

/-- Whether an instruction is an `elect.sync`. -/
def electOp : Op → Bool
  | .warp ⟨.elect, _, _, _, _⟩ => true
  | _ => false

theorem ofExec_notElect {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotElect r) :
    NotElect (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notElect {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotElect m) :
    NotElect (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

/-- Every instruction other than `elect.sync` is not an election. -/
theorem eventTmpl_notElect {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : electOp op = false) : NotElect (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    simp only [eventTmpl]
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    unfold warpTmpl
    split
    · simp only [shflTmpl]; repeat' first | trivial | split
    · simp only [voteTmpl]; repeat' first | trivial | split
    · simp only [voteModeTmpl]; repeat' first | trivial | split
    · simp only [reduxTmpl]; repeat' first | trivial | split
    · simp only [matchTmpl]; repeat' first | trivial | split
    · trivial
    · simp_all [electOp]
    · simp only [warpBarTmpl]; repeat' first | trivial | split
    · trivial
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notElect
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notElect)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notElect)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A template that is not an election fires none. -/
theorem fires_notElect {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotElect m)
    (hf : Fires pc m e o) : ∀ mask inst l, e.kind ≠ .elect mask inst l := by
  intro mask inst l he
  cases m <;> simp only [Fires] at hf <;> (try simp only [NotElect] at hm) <;> aesop

/-- The event of an `elect.sync` is an election of the mask its operand holds. -/
theorem electTmpl_fires {L : Launch} {g : Nat} {t : TState} {d : Option Nat} {p : Nat}
    {mk : Opnd} {pc : Nat} {e : Event} {o : Option TState} {mask inst l : Nat}
    (hf : Fires pc (electTmpl L g t d p mk) e o) (hk : e.kind = .elect mask inst l) :
    e.pc = pc ∧ ∃ bits, readBits L g t 32 mk = .ok bits ∧ bits.toNat = mask := by
  unfold electTmpl at hf
  split at hf
  · obtain ⟨rfl, -⟩ := hf; cases hk
  · rename_i bits hb
    split at hf
    · obtain ⟨i, v, rfl, -⟩ := hf
      cases hk
      exact ⟨rfl, bits, hb, rfl⟩
    · obtain ⟨rfl, -⟩ := hf; cases hk

/-- **An election event** is fired by an `elect.sync` at its position whose mask operand holds the
event's mask. -/
theorem elect_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} {mask inst l : Nat}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hk : e.kind = .elect mask inst l) :
    ∃ ty d p mk, op = .warp ⟨.elect, ty, [d, some p], [], some mk⟩ ∧
      e.pc = pc ∧ ∃ bits, readBits L g t 32 mk = .ok bits ∧ bits.toNat = mask := by
  cases hop : electOp op
  · exact absurd hk (fires_notElect (eventTmpl_notElect hop) hf mask inst l)
  · cases op <;> simp only [electOp, Bool.false_eq_true] at hop
    rename_i w
    rcases w with ⟨kind, ty, dsts, srcs, mo⟩
    simp only [eventTmpl, warpTmpl] at hf
    split at hf
    · simp only [shflTmpl] at hf
      split at hf <;> (try split_ifs at hf) <;> simp_all
    · simp only [voteTmpl] at hf
      split at hf <;> (try split_ifs at hf) <;> simp_all
    · simp only [voteModeTmpl] at hf
      split at hf <;> (try split_ifs at hf) <;> simp_all
    · simp only [reduxTmpl] at hf
      split at hf <;> (try split_ifs at hf) <;> simp_all
    · simp only [matchTmpl] at hf
      split at hf <;> (try split_ifs at hf) <;> simp_all
    · simp only [activemaskTmpl] at hf
      obtain ⟨_, rfl, -⟩ := hf; cases hk
    · rename_i d p mk _
      exact ⟨ty, d, p, mk, rfl, electTmpl_fires hf hk⟩
    · simp only [warpBarTmpl] at hf
      split at hf <;> (try split_ifs at hf) <;> simp_all
    · obtain ⟨rfl, -⟩ := hf; cases hk

/-- An event of a thread's run is fired by an instruction of the code at the event's position. -/
theorem _root_.PTX.Run.estep {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {es : List Event} {o : Option TState} (h : Run K A L g t es o) {e : Event} (he : e ∈ es) :
    ∃ t1 o', EStep K A L g t1 e o' := by
  induction h with
  | nil => cases he
  | step _ hs _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, hs⟩
    · exact ih he
  | last _ hs =>
    cases List.mem_singleton.mp he
    exact ⟨_, _, hs⟩

/-- **The mask of an election event** of a thread's trace: the event is fired by an `elect.sync`
of the code at its position, whose mask operand evaluates to the event's mask. -/
theorem elect_mask {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {es : List Event}
    (hp : Produces K A L g es) {e : Event} (he : e ∈ es) {mask inst l : Nat}
    (hk : e.kind = .elect mask inst l) :
    ∃ ins ty d p mk, K.code[e.pc]? = some ins ∧
      ins.op = .warp ⟨.elect, ty, [d, some p], [], some mk⟩ ∧
      ∃ t bits, readBits L g t 32 mk = .ok bits ∧ bits.toNat = mask := by
  obtain ⟨o, hr⟩ := hp
  obtain ⟨t, o', m, hm, hf⟩ := hr.estep he
  rcases out_ev hm with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · obtain ⟨rfl, -⟩ := hf
    cases hk
  · obtain ⟨ty, d, p, mk, hop, hpc, bits, hb, hbm⟩ := elect_op hf hk
    exact ⟨ins, ty, d, p, mk, hpc ▸ hc, hop, t, bits, hb, hbm⟩

end
end PTX.Flow
