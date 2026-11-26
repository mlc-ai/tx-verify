-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotVote
public import Lemmas.Kernel.Progress.Warp
public import Lemmas.Flow.NotBulk
public import Lemmas.Kernel.Progress.WarpNoBallot

@[expose] public section

/-! # A kernel without ballot instructions performs no ballot

`vote.sync` with a mode (`.all`, `.any`, `.uni`) fires a `.voteMode` event, never a `.vote`
(ballot) event. A kernel whose only votes are mode votes therefore meets the `hnb` premise of
`Sched.warpColl_steps_relNB` with one evaluated check of its code (`no_ballot`). -/

namespace PTX.Sched
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {κ : Type}

/-- A template that fires no ballot. -/
def NotBallot : Tmpl → Prop
  | .vote .. => False
  | _ => True

/-- Whether an instruction is a ballot (`vote.sync.ballot`). -/
def ballotOp : Op → Bool
  | .warp w => match w.kind with
    | .vote .ballot _ => true
    | _ => false
  | _ => false

/-- An instruction other than a ballot fires no ballot. -/
theorem eventTmpl_notBallot {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : ballotOp op = false) : NotBallot (eventTmpl A L g t op) := by
  by_cases hv : Op.isVote op = true
  · cases op
    case warp w =>
      rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> simp only [Op.isVote, Bool.false_eq_true] at hv
      rename_i mode neg
      cases mode <;> simp only [ballotOp] at hop
      all_goals
        simp only [eventTmpl, warpTmpl, voteModeTmpl]
        repeat' first
          | trivial
          | (exfalso; simp_all; done)
          | split
    all_goals simp [Op.isVote] at hv
  · have := eventTmpl_notVote (A := A) (L := L) (g := g) (t := t) (by simpa using hv)
    cases h : eventTmpl A L g t op <;> rw [h] at this <;> simp_all [NotVote, NotBallot]

/-- A ballot is fired by a ballot instruction. -/
theorem fires_ballot_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : Nat} {a : Bool} {b : BitVec 32} (hk : e.kind = .vote m a b) : ballotOp op = true := by
  cases hq : ballotOp op
  · exfalso
    have hm := eventTmpl_notBallot (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotBallot] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- **A kernel without ballot instructions performs no ballot.** -/
theorem no_ballot {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hK : K.code.all (fun ins => !ballotOp ins.op) = true) (hX : Consistent L K A mem0 X)
    {i : EvId} {pc m : Nat} {a : Bool} {b : BitVec 32} : X.get i ≠ some ⟨pc, .vote m a b⟩ :=
  fun he => Flow.no_kind_of_code hX ballotOp (fun k => ∃ m a b, k = .vote m a b)
    (fun _ ⟨_, _, _, h⟩ => by cases h) (fun hf ⟨_, _, _, hk⟩ => fires_ballot_op hf hk)
    hK he ⟨_, _, _, rfl⟩

variable {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {key : Nat → κ} {M : Timed K A L} {AtColl : ∀ g, (M.code g).D → Prop}

/-- **Progress at a warp collective, in a kernel without ballot instructions** (mode votes
allowed): `warpColl_steps_relNB` with `no_ballot`. -/
theorem warpColl_steps_relK (hK : K.code.all (fun ins => !ballotOp ins.op) = true)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h)
    (hsound : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hw : WarpCollRel mem0 M X key AtColl)
    (hb : L.block % 32 = 0) (hlaunch : ∀ h, Step.Launched L X h)
    (hcl : ∀ h, ¬ ClcCanceled L X h)
    (happ : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hrel : Step.Released L X g) : Steps M mem0 X (.thread g) :=
  warpColl_steps_relNB (fun {_ _ _ _ _} => no_ballot hK hmax.1) hkey hsound hs htr hw hb hlaunch
    hcl happ hubx hmax hp hσ hk hrel

end
end PTX.Sched
