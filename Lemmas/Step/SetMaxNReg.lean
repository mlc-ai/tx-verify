-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # The warp rendezvous of `setmaxnreg`

A proof tool for the progress argument about `setmaxnreg` (DEP-SETMAXNREG-RENDEZVOUS). The matching
relation `SameRequest` is an equivalence on actual requests; the readiness of a request transfers
along it. The rendezvous obligation itself is the `setmaxnreg` arm of `KindNeeds`: `Ready L X e`
for a request `e` says that every lane of its warp has a present matching request, and
`DependencyOk.ready` demands it of every returned request, which is `Ok` over the whole execution.
A request whose warp is incomplete keeps every matching request source-terminal
(`Consistent.pending_sameRequest_last`), and in a safe execution some lane of the warp has no
matching request and no other request with the ordinal of `e` (`missing_member_lane`). -/

namespace PTX
noncomputable section

/-- The threads of a warp start at the first lane of the warp of `x`. -/
theorem sub_laneOf {L : Launch} (x : Nat) :
    x - laneOf L x = (x / L.block) * L.block + (x % L.block / 32) * 32 := by
  have e1 : x = (x / L.block) * L.block + x % L.block := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod x L.block).symm
  have e2 : x % L.block = (x % L.block / 32) * 32 + x % L.block % 32 := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod (x % L.block) 32).symm
  unfold laneOf
  omega

/-- Lane `l` is the same thread in both warps. -/
theorem warpLane_eq_of_sameWarp {L : Launch} {g h l : Nat} (hw : SameWarp L g h) :
    warpLane L g l = warpLane L h l := by
  obtain ⟨⟨_, _, hcta⟩, hwarp⟩ := hw
  have hgl : g - laneOf L g = h - laneOf L h := by
    rw [sub_laneOf, sub_laneOf, hcta, hwarp]
  unfold warpLane
  rw [hgl]

/-- The thread of the warp of `g` in lane `l` is the only thread of that warp in lane `l`. -/
theorem eq_warpLane_of_sameWarp {L : Launch} {g h l : Nat} (hw : SameWarp L g h)
    (hl : laneOf L h = l) : h = warpLane L g l := by
  obtain ⟨⟨_, _, hcta⟩, hwarp⟩ := hw
  have hgl : g - laneOf L g = h - laneOf L h := by
    rw [sub_laneOf, sub_laneOf, hcta, hwarp]
  have hle : laneOf L h ≤ h := by
    unfold laneOf
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _)
  unfold warpLane
  omega

end
end PTX

namespace PTX.SetMaxNReg
noncomputable section

/-- Reflexivity holds on actual requests of launched threads. Instance labels
are local payloads and do not identify a warp's collective generation. -/
theorem SameRequest.refl {L : Launch} {X : Execution} {e : EvId}
    {pc n inst : Nat} {inc : Bool} (hg : e.1 < L.threads)
    (he : Request X e pc inc n inst) : SameRequest L X e e :=
  ⟨⟨⟨hg,hg,rfl⟩,rfl⟩,rfl,pc,inc,n,inst,inst,he,he⟩

theorem SameRequest.symm {L : Launch} {X : Execution} {e f : EvId}
    (h : SameRequest L X e f) : SameRequest L X f e := by
  obtain ⟨hw,ho,pc,inc,n,einst,finst,he,hf⟩ := h
  exact ⟨⟨⟨hw.1.2.1,hw.1.1,hw.1.2.2.symm⟩,hw.2.symm⟩,
    ho.symm,pc,inc,n,finst,einst,hf,he⟩

theorem SameRequest.trans {L : Launch} {X : Execution} {e f g : EvId}
    (hef : SameRequest L X e f) (hfg : SameRequest L X f g) :
    SameRequest L X e g := by
  obtain ⟨hw,ho,pc,inc,n,einst,finst,he,hf⟩ := hef
  obtain ⟨hw',ho',pc',inc',n',finst',ginst,hf',hg⟩ := hfg
  have heq : (⟨pc,.setMaxReg inc n finst⟩ : Event) =
      ⟨pc',.setMaxReg inc' n' finst'⟩ := Option.some.inj (hf.symm.trans hf')
  cases heq
  exact ⟨⟨⟨hw.1.1,hw'.1.2.1,hw.1.2.2.trans hw'.1.2.2⟩,hw.2.trans hw'.2⟩,
    ho.trans ho',pc,inc,n,einst,ginst,he,hg⟩

/-- The needs of a request are its warp's matching requests, one per lane
(DEP-SETMAXNREG-RENDEZVOUS). -/
theorem needs_eq {L : Launch} {X : Execution} {e : EvId} {pc n inst : Nat} {inc : Bool}
    (he : Request X e pc inc n inst) :
    Needs L X e = (List.range 32).map (fun l => Need.node fun x =>
      ∃ j, x = .thread (warpLane L e.1 l, j) ∧ SameRequest L X e (warpLane L e.1 l, j)) := by
  have hget : X.get e = some ⟨pc, .setMaxReg inc n inst⟩ := he
  simp only [Needs, hget, KindNeeds]

/-- A request is ready when every lane of its warp has a present matching request
(DEP-SETMAXNREG-RENDEZVOUS). -/
theorem ready_iff {L : Launch} {X : Execution} {e : EvId} {pc n inst : Nat} {inc : Bool}
    (he : Request X e pc inc n inst) :
    Ready L X e ↔ ∀ l, l < 32 → ∃ j, X.RefPresent (.thread (warpLane L e.1 l, j)) ∧
      SameRequest L X e (warpLane L e.1 l, j) := by
  rw [Ready, needs_eq he]
  constructor
  · intro h l hl
    have hmem : Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
        SameRequest L X e (warpLane L e.1 l, j)) ∈ (List.range 32).map (fun l => Need.node fun x =>
          ∃ j, x = .thread (warpLane L e.1 l, j) ∧
            SameRequest L X e (warpLane L e.1 l, j)) :=
      List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩
    have hh : ∃ x, X.RefPresent x ∧ ∃ j, x = .thread (warpLane L e.1 l, j) ∧
        SameRequest L X e (warpLane L e.1 l, j) := h _ hmem
    obtain ⟨x, hpres, j, heqx, hs⟩ := hh
    subst heqx
    exact ⟨j, hpres, hs⟩
  · intro h n hn
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
    obtain ⟨j, hpres, hs⟩ := h l (List.mem_range.mp hl)
    exact ⟨_, hpres, j, rfl, hs⟩

/-- Readiness transfers along the same-request relation: the two events need the matching request
of the same lanes of one warp (DEP-SETMAXNREG-RENDEZVOUS). -/
theorem ready_of_sameRequest {L : Launch} {X : Execution} {e f : EvId} {pc n inst : Nat}
    {inc : Bool} (he : Request X e pc inc n inst) (hef : SameRequest L X e f)
    (hr : Ready L X e) : Ready L X f := by
  have hfe := hef
  obtain ⟨hw, _, pc', inc', n', _, _, _, hf⟩ := hfe
  rw [ready_iff hf]
  intro l hl
  obtain ⟨j, hpres, hs⟩ := (ready_iff he).1 hr l hl
  have hwl : warpLane L e.1 l = warpLane L f.1 l := warpLane_eq_of_sameWarp hw
  exact ⟨j, hwl ▸ hpres, hwl ▸ SameRequest.trans (SameRequest.symm hef) hs⟩

/-- Every returned request has the whole warp: the `setmaxnreg` slice of `DependencyOk.ready`
(DEP-ORDER), which is what the deleted `SetMaxNReg.Ok` of the per-form waiting layer said
(DEP-SETMAXNREG-RENDEZVOUS). A request returns when its thread performs a later event
(`Kind.resume`). -/
def Ok (L : Launch) (X : Execution) : Prop :=
  ∀ e pc inc n inst, Request X e pc inc n inst → e.2 + 1 < (X.tr e.1).length → Ready L X e

end
end PTX.SetMaxNReg

namespace PTX
noncomputable section

/-- In a consistent execution a request whose warp is incomplete has every matching request as
its thread's last event: a return would need the whole warp (DEP-SETMAXNREG-RENDEZVOUS). -/
theorem Consistent.pending_sameRequest_last {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {e f : EvId} (hn : ¬ Ready L X e)
    (hef : SetMaxNReg.SameRequest L X e f) :
    f.2+1 = (X.tr f.1).length := by
  have hfe := hef
  obtain ⟨_, _, _, _, _, _, _, _, hf⟩ := hfe
  have hle : f.2+1 ≤ (X.tr f.1).length := by
    have ht := len_of_get hf
    omega
  by_contra hne
  have hp : f.2+1 < (X.tr f.1).length := by omega
  have hret : Returned X f := by
    unfold Returned
    rw [hf]
    exact hp
  exact hn (SetMaxNReg.ready_of_sameRequest (e := f) (f := e) hf
    (SetMaxNReg.SameRequest.symm hef) (hX.dependency.ready f hret))

end
end PTX

namespace PTX.Step
open PTX
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- For a request without all of its lanes, in a safe execution: for some lane, every thread of
the warp in that lane has no request matching `e` and no other request with the ordinal of `e`
(`SetMaxNReg.Unsafe` and ERR-ALIGNED-MISMATCH, the mismatch clauses). The exit clause of the
former `SetMaxNReg.Unsafe` is `AlignedClass.setMaxReg.Exited` now, whose participant count is the
thread's whole trace; a companion stating that no thread of the lane exits at or before the
ordinal of `e` needs `Execution.exit_last` and so belongs beside it in `Lemmas/Step/ExitLast.lean`,
which cannot be imported here. -/
theorem missing_member_lane (hsafe : ¬ Unsafe L K A mem0 X)
    {e : EvId} {pc n inst : Nat} {inc : Bool} (he : SetMaxNReg.Request X e pc inc n inst)
    (hm : ¬ Ready L X e) :
    ∃ lane, lane < 32 ∧ ∀ h, h < L.threads → SameWarp L e.1 h → laneOf L h = lane →
      (∀ j, ¬ SetMaxNReg.SameRequest L X e (h, j)) ∧
      (∀ j pc' inc' n' inst', SetMaxNReg.Request X (h, j) pc' inc' n' inst' →
        SetMaxNReg.ordinal X (h, j) ≠ SetMaxNReg.ordinal X e) := by
  have hnoReg : ¬ SetMaxNReg.UnsafeAt A L X := fun h => hsafe (by simp [Unsafe, h])
  have hnoAligned : ¬ AlignedMismatch L K X := fun h => hsafe (by simp [Unsafe, h])
  have hm' : ∃ lane, lane < 32 ∧ ∀ j, ¬ (X.RefPresent (.thread (warpLane L e.1 lane, j)) ∧
      SetMaxNReg.SameRequest L X e (warpLane L e.1 lane, j)) := by
    by_contra hcon
    apply hm
    rw [SetMaxNReg.ready_iff he]
    intro l hl
    by_contra hno
    exact hcon ⟨l, hl, fun j hx => hno ⟨j, hx⟩⟩
  obtain ⟨lane, hl, hno⟩ := hm'
  refine ⟨lane, hl, fun h hh hw hlane => ?_⟩
  have heq : h = warpLane L e.1 lane := eq_warpLane_of_sameWarp hw hlane
  have hnone : ∀ j, ¬ SetMaxNReg.SameRequest L X e (h, j) := by
    intro j hs
    have hsc := hs
    obtain ⟨_, _, _, _, _, _, _, _, hreq⟩ := hsc
    exact hno j ⟨by rw [← heq]; exact ⟨_, hreq⟩, by rw [← heq]; exact hs⟩
  have hsg : SetMaxNReg.SameGroup L e.1 h := ⟨hw.1, by have h2 := hw.2; omega⟩
  refine ⟨hnone, ?_⟩
  intro j pc' inc' n' inst' hr hord
  by_cases hpc : pc = pc'
  · have hr' : SetMaxNReg.Request X (h, j) pc inc' n' inst' := hpc.symm ▸ hr
    by_cases hvals : inc = inc' ∧ n = n'
    · obtain ⟨rfl, rfl⟩ := hvals
      exact hnone j ⟨hw, hord.symm, pc, inc, n, inst, inst', he, hr'⟩
    · apply hnoReg
      refine ⟨e, pc, inc, n, inst, he, Or.inr (Or.inr (Or.inl
        ⟨(h, j), pc, inc', n', inst', hsg, hr', hord.symm, ?_⟩))⟩
      by_cases hi : inc = inc'
      · exact Or.inr (by tauto)
      · exact Or.inl hi
  · apply hnoAligned
    exact ⟨.setMaxReg, Or.inl ((AlignedClass.divergent_setMaxReg_iff L (K := K) (X := X)).mpr
      ⟨e, (h, j), pc, pc', inc, inc', n, n', inst, inst', hw, he, hr, hord.symm, hpc⟩)⟩

end
end PTX.Step
