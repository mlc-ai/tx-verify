-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Entry
import all Kernels.FlashKdaFwd.Packed.Producer
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

private def code (pc n : Nat) := (Transfers.slice pc n).getD []

private noncomputable def localWindow (base : Nat → Nat → Nat) (L : Launch) (pc n count : Nat)
    (t : TState) :=
  Producer.limited (Producer.model pc (code pc n)) (Prologue.assumptions base)
    L 129 pc (pc+n) count t

private theorem localWindow_sound {base : Nat → Nat → Nat} {L : Launch} {pc n count : Nat}
    {t u : TState} (fit : pc+n ≤ 3835) (h : localWindow base L pc n count t = some u) :
    run kernel (Prologue.assumptions base) L 129 count t = some u := by
  apply Producer.agrees (src := Producer.model pc (code pc n)) _ h
  intro j low high
  obtain ⟨i,rfl⟩ : ∃ i, j = pc+i := ⟨j-pc,by omega⟩
  have inside : i < n := by omega
  have read : Transfers.slice pc n = some (code pc n) := by
    simp only [code,instructions fit,Option.getD_some]
  rw [fetch fit inside read]
  change (code pc n)[i]? = (List.replicate pc Election.stop ++ code pc n)[pc+i]?
  have enough : (List.replicate pc Election.stop).length ≤ pc+i := by simp
  rw [List.getElem?_append_right enough,List.length_replicate,Nat.add_sub_cancel_left]

private def firstSequence (t : TState) :=
  setReg {t with pc := 117,fault := none} 309 (b32 0)

private def offsetState (t : TState) := (t.pc,t.fault,t.regs 2248,t.regs 2249,t.regs 307,t.regs 88)

set_option maxRecDepth 60000 in
private theorem first_branch (base : Nat → Nat → Nat) (L : Launch) (t : TState) :
    (localWindow base L 117 3 3 (firstSequence t)).map offsetState =
      some (301,none,t.regs 2248,t.regs 2249,t.regs 307,t.regs 88) := by kernel_rfl

theorem first_sequence_offsets (base : Nat → Nat → Nat) (L : Launch) (t : TState)
    (pc : t.pc = 117) (clear : t.fault = none) (sequence : t.regs 309 = some (b32 0)) :
    ∃ u, run kernel (Prologue.assumptions base) L 129 3 t = some u ∧ u.pc = 301 ∧
      u.fault = none ∧ u.regs 2248 = t.regs 2248 ∧ u.regs 2249 = t.regs 2249 ∧
      u.regs 307 = t.regs 307 ∧ u.regs 88 = t.regs 88 := by
  have original : firstSequence t = t := by
    unfold firstSequence
    rw [← pc,← clear]
    simp [setReg,← sequence,Function.update_eq_self]
  have h := first_branch base L t
  rw [original] at h
  obtain ⟨u,steps,summary⟩ := Option.map_eq_some_iff.mp h
  exact ⟨u,localWindow_sound (by decide) steps,by simpa [offsetState] using summary⟩

private def seed (t : TState) :=
  setReg (setReg {t with pc := 301, fault := none} 2248 (.bits 64 0)) 2249 (.bits 64 1)

private def electionInput (t : TState) :=
  (t.pc,t.fault,t.regs 487,t.regs 314,t.regs 307,t.regs 88)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem evaluate (base : Nat → Nat → Nat) (L : Launch) (t : TState) :
    (localWindow base L 301 11 11 (seed t)).map electionInput =
      some (312,none,some (b32 0xffffffff),some (b32 1),t.regs 307,t.regs 88) := by kernel_rfl

theorem offsets_to_election (base : Nat → Nat → Nat) (L : Launch) (t : TState)
    (pc : t.pc = 301) (clear : t.fault = none) (first : t.regs 2248 = some (.bits 64 0))
    (last : t.regs 2249 = some (.bits 64 1)) :
    ∃ u, run kernel (Prologue.assumptions base) L 129 11 t = some u ∧ u.pc = 312 ∧
      u.fault = none ∧ u.regs 487 = some (b32 0xffffffff) ∧ u.regs 314 = some (b32 1) ∧
      u.regs 307 = t.regs 307 ∧ u.regs 88 = t.regs 88 := by
  have same {r : Nat} {v : Value} (val : t.regs r = some v) : setReg t r v = t := by
    simp [setReg,← val,Function.update_eq_self]
  have h := evaluate base L t
  have original : seed t = t := by
    unfold seed
    rw [← pc,← clear]
    simp only [same first,same last]
  rw [original] at h
  obtain ⟨u,steps,summary⟩ := Option.map_eq_some_iff.mp h
  exact ⟨u,localWindow_sound (by decide) steps,by simpa [electionInput] using summary⟩

def secondResult (L : Launch) (t : TState) (leader : Nat) :=
  next (setReg (setReg t 3423 (b32 leader)) 3424 (.pred (laneOf L 129 == leader)))

private def elect : Instr :=
  ⟨none,.warp ⟨.elect,none,[some 3423,some 3424],[],some (.reg 487)⟩⟩

set_option maxRecDepth 60000 in
private theorem electSite : Transfers.slice 312 1 = some [elect] := by kernel_rfl

theorem second_election (base : Nat → Nat → Nat) (L : Launch) (t : TState)
    (pc : t.pc = 312) (clear : t.fault = none) (mask : t.regs 487 = some (b32 0xffffffff)) :
    out kernel (Prologue.assumptions base) L 129 t =
      .ev (.elect 0xffffffff (secondResult L t)) := by
  have site : kernel.code[t.pc]? = some elect := by
    rw [pc]
    exact fetch (pc := 312) (i := 0) (by decide) (by decide) electSite
  simp only [out,clear,site,show guardHolds t elect.guard = .ok true from rfl,
    show elect.op.isLocal = false from rfl,Bool.false_eq_true,ite_false,Out.ev.injEq]
  change electTmpl L 129 t (some 3423) 3424 (.reg 487) = _
  rw [electTmpl, readBits_b32 mask (by decide)]
  change (if electMember 0xffffffff (laneOf L 129) then _ else _) = _
  have member : electMember 0xffffffff (laneOf L 129) :=
    Election.mask_member (Nat.mod_lt _ (by decide))
  rw [ite_eq_left member]
  rfl

private def picked (t : TState) :=
  next (setReg (setReg t 3423 (b32 1)) 3424 (.pred true))

set_option maxRecDepth 60000 in
private theorem after (base : Nat → Nat → Nat) (L : Launch) (t : TState) :
    (localWindow base L 313 2 2 (picked {t with pc := 312,fault := none})).map
      (fun s => (s.pc,s.fault,s.regs 486,s.regs 314,s.regs 307,s.regs 88)) =
      some (315,none,some (b32 1),t.regs 314,t.regs 307,t.regs 88) := by kernel_rfl

theorem selected_after (base : Nat → Nat → Nat) (L : Launch) (t : TState) (block : L.block = 192)
    (pc : t.pc = 312) (clear : t.fault = none) :
    ∃ u, run kernel (Prologue.assumptions base) L 129 2 (secondResult L t 1) = some u ∧
      u.pc = 315 ∧ u.fault = none ∧ u.regs 486 = some (b32 1) ∧ u.regs 314 = t.regs 314 ∧
      u.regs 307 = t.regs 307 ∧ u.regs 88 = t.regs 88 := by
  have h := after base L t
  have original : {t with pc := 312,fault := none} = t := by rw [← pc,← clear]
  rw [original] at h
  have lane : laneOf L 129 = 1 := by unfold laneOf; rw [block]
  have agree : secondResult L t 1 = picked t := by simp [secondResult,picked,lane]
  obtain ⟨u,steps,data⟩ := Option.map_eq_some_iff.mp h
  exact ⟨u,agree ▸ localWindow_sound (by decide) steps,by simpa using data⟩

end FlashKda.Packed.ProducerControl
