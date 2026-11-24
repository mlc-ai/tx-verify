-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkBar
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Progress.Fire
public import Kernels.InklingRelDecode.Proof.Progress.WarpFacts

@[expose] public section

/-!
# Warp lockstep: the warp-collective events

A state is a warp-collective state (`wcSt`) when its instruction is a shuffle, an election, a warp
barrier or a ballot (`warpOp`; the kind `NextKind.warp`). The event fired from a state is a warp
collective (`Sched.isWarpColl`) exactly when the state is (`isWarpColl_state`): the template at a
state is undefined behaviour, which no followed state fires, or of the state's kind (`tmpl_kind`),
and the events of a template of each kind are classified (`warp_kind_iff`). The states of the class
are synchronizing (`wcSt_sy`), and two synchronizing states of one key are both in the class or both
out (`wcKey_class`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Lk (syOp syPcs syPc syAt kernel_syPcs)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The events of a template of a kind**: the event is a warp collective exactly when the kind
is `warp`. -/
theorem warp_kind_iff {k : NextKind} {m : Tmpl} {pc : Nat} {e : Event} {o : Option TState}
    (hk : KindTmpl k m) (hf : Fires pc m e o) : Sched.isWarpColl e = true ↔ k = .warp := by
  cases k
  · obtain ⟨l, p, k', a, s, rfl⟩ := hk
    obtain ⟨ok, rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · simp only [KindTmpl] at hk
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    rcases hk with ⟨md, a, b, c, k', rfl⟩ | ⟨mask, k', rfl⟩ | ⟨mask, t, rfl⟩ | ⟨mask, a, k', rfl⟩
    · obtain ⟨recv, ok, rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨inst, leader, rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨inst, rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨ballot, rfl, -⟩ := hf; simp [Sched.isWarpColl]
  · obtain ⟨id, t, c, md, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨inc, n, t, rfl⟩ := hk
    obtain ⟨inst, rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨grp, dst, act, t, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨l, c, t, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨l, tx, t, c, r, s, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨a, s, t, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨d, s, acc, ms, t, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨s, t, rfl⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · rcases hk with ⟨a, n, sh, k', rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨vals, -, rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨rfl, -⟩ := hf; simp [Sched.isWarpColl]
  · rcases hk with ⟨a, vs, sh, t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨rfl, -⟩ := hf; simp [Sched.isWarpColl]
  · obtain ⟨a, k', rfl⟩ := hk
    obtain ⟨bs, -, rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · rcases hk with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨rfl, -⟩ := hf; simp [Sched.isWarpColl]
    · obtain ⟨rfl, -⟩ := hf; simp [Sched.isWarpColl]
  · obtain ⟨a, bs, t, rfl, -⟩ := hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · obtain ⟨dst, t, rfl⟩ := hk
    obtain ⟨col, -, rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · subst hk
    obtain ⟨rfl, -⟩ := hf
    simp [Sched.isWarpColl]
  · exact hk.elim

/-! ### The instruction -/

/-- The instruction is a shuffle, an election, a warp barrier or a ballot. -/
def warpOp : Op → Bool
  | .warp ⟨.shfl _, _, _, _, _⟩ | .warp ⟨.elect, _, _, _, _⟩ | .warp ⟨.barWarp, _, _, _, _⟩
  | .warp ⟨.vote .ballot _, _, _, _, _⟩ => true
  | _ => false

/-- The position is a warp-collective instruction. -/
abbrev warpPc (pc : Nat) : Bool := opPc warpOp pc

/-- The state's event is a warp collective. -/
def wcSt (s : TSt) : Bool := warpPc (TSt.pc s)

theorem opKind_warp (op : Op) : opKind op = .warp ↔ warpOp op = true := by
  unfold opKind warpOp
  split <;> simp_all <;> split <;> simp_all <;> split <;> simp

/-- **The kind of a state is `warp` exactly when its position is a warp-collective one.** -/
theorem nextKind_warp (s : TSt) : nextKind s = .warp ↔ wcSt s = true := by
  unfold nextKind wcSt warpPc opPc
  cases hc : kernel.code[TSt.pc s]? with
  | none => simp
  | some ins =>
    simp only
    cases hop : ins.op with
    | tcAlloc g b o n => simp [opKindSub, warpOp]; split <;> simp
    | _ => rw [← opKind_warp, ← hop]; simp [opKindSub, hop]

/-- **A warp-collective state is synchronizing.** -/
theorem wcSt_sy {s : TSt} (h : wcSt s = true) : tSy s :=
  opPc_sy (f := warpOp) (fun op h => by
    cases op <;> simp_all [warpOp, syOp]) ⟨fun s => by cases s <;> decide +kernel,
    by decide +kernel, fun s => by cases s <;> decide +kernel⟩ h

/-- **A synchronizing state is in the class exactly when its position is a warp-collective
one**: by definition, the class is a function of the position. -/
theorem wcKey_class :
    ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' → wcSt s = wcSt s' :=
  opKey_class warpOp

/-- **The event fired from a state is a warp collective exactly when the state is.** -/
theorem isWarpColl_state (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some s)) : Sched.isWarpColl e = wcSt s := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site hf.sound hX he hσ
  have hk := kind_ne_other (hf.sound g hg) hinv hc
  rcases tmpl_kind hat hc hk with ⟨fl, hub⟩ | hkt
  · exfalso
    rw [hub] at hfire
    obtain ⟨rfl, -⟩ := hfire
    rcases hf.ub_stop hg he with h | h <;> rw [hσ] at h <;> cases h
  · have h1 := warp_kind_iff hkt hfire
    have h2 := nextKind_warp s
    cases hw : wcSt s
    · cases hc' : Sched.isWarpColl e
      · rfl
      · have := h1.mp hc'
        have := h2.mp this
        simp_all
    · exact h1.mpr (h2.mpr hw)

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4
