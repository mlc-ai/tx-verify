-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Mma.Steps
public import Lemmas.Flow.Glue

@[expose] public section

/-! # The MMA warp from its `setmaxnreg`: a startup machine glued before the role machine

The `setmaxnreg` and the Tensor Memory allocation (pc 1907 to 1909) are a machine of their own
(`S`): the allocation's second event on lane 0, the write of the address, sits at sub-step 1,
which the role machine cannot carry (its `sub` would not be constant). `S`'s last state, at the
first named barrier, is the role machine's first state; `G` is the two glued (lane L's
`Code.glue`), one machine for the MMA warp from its `setmaxnreg` to its `ret`, with every state's
step obligation (`stepAt_G`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The startup states: the `setmaxnreg`, the allocation, its address write on lane 0, and the
hand-off at the first named barrier. -/
inductive Start where
  | set | alloc | wr | enter
  deriving DecidableEq

def Start.pc : Start → Nat
  | .set => 1907
  | .alloc | .wr => 1909
  | .enter => 1910

/-- The startup machine. -/
@[reducible] def S (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g where
  D := Start
  init := .set
  pc := Start.pc
  facts := fun s => Flow.factsFrom (Flow.live s.pc) (valueOf p L g ent ⟨.bar1, {}⟩)
  sub := fun | .wr => 1 | _ => 0
  inv := fun _ => True
  next := fun s _ => match s with
    | .set => some (some .alloc)
    | .alloc => some (some (if laneOf L g = 0 then .wr else .enter))
    | .wr => some (some .enter)
    | .enter => none

/-- The startup machine's exit: its hand-off state. -/
def Start.exit : Start → Option Unit
  | .enter => some ()
  | _ => none

/-- The MMA warp's machine from its `setmaxnreg`. -/
abbrev G (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g :=
  Code.glue (S p L g ent) (fun _ => code p L g ent) Start.exit

/-- The registers live at the `setmaxnreg` that the warp never reads, with their startup values:
three barrier addresses and two launch words. -/
def ent (p : Params) (L : Launch) (r : Nat) : Value :=
  if r = 1069 then b32 (L.sharedBase + 192) else if r = 2390 then b32 (L.sharedBase + 208)
  else if r = 6497 then b32 (L.sharedBase + 224) else if r = 7500 then b64 p.lseBase
  else if r = 7501 then b64 p.lseStride else .pred false

/-- **The MMA warp's fragment**: its machine from the role's entry, the `setmaxnreg` at pc 1907.
The registers live there are the startup's (`ent` for those the warp never reads). -/
abbrev M (p : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  G p L g (ent p L)

theorem live_1907 : Flow.live 1907 = [1062, 1069, 1072, 1178, 2390, 2535, 6495, 6497, 7203,
    7500, 7501, 7502, 7503, 7506] := by
  rfl

/-- The registers the fragment's first state relies on: what a hand-off from the startup proves. -/
theorem init_facts (p : Params) (L : Launch) (g : Nat) : (M p L g).facts (M p L g).init =
    [(1062, b32 12), (1069, b32 (L.sharedBase + 192)), (1072, .bits 32 (Epilogue.ctaW L g)),
     (1178, b32 (L.sharedBase + 68608)), (2390, b32 (L.sharedBase + 208)), (2535, b32 L.sharedBase),
     (6495, b32 (L.sharedBase + 144)), (6497, b32 (L.sharedBase + 224)), (7203, b32 p.batch),
     (7500, b64 p.lseBase), (7501, b64 p.lseStride), (7502, b64 p.cuQBase),
     (7503, b64 p.usedKBase), (7506, b64 p.cuQBase)] := by
  show Flow.factsFrom (Flow.live 1907) (valueOf p L g (ent p L) ⟨.bar1, {}⟩) = _
  rw [live_1907]
  simp [Flow.factsFrom, valueOf, values, valuesRole, valuesStart, ent, List.lookup]

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt_S (hp : Pre p L m) (d : Start) (hx : d.exit = none) :
    (S p L g ent).StepAt d := by
  have hparams := Epilogue.params hp
  cases d with
  | set =>
    refine Code.StepAt.of (by intro _; exact ⟨_, Flow.code_1907, rfl, trivial⟩) ?_
    exact Code.step_issue (dn := .alloc) Flow.code_1907 (fun hf => fires_next (by exact trivial) hf)
      (fun _ => rfl) rfl rfl
      ⟨fun _ => by site_norm; seg_auto using ep_seg, rfl, rfl, fun _ => trivial⟩
  | alloc =>
    refine Code.StepAt.of (by intro _; exact ⟨_, Flow.code_1909, rfl, trivial⟩) ?_
    exact Code.step_alloc (dw := .wr) (dn := .enter) Flow.code_1909 rfl rfl
      (fun h0 _ => by simp [h0]) (fun h0 _ => by simp [h0]) rfl rfl rfl rfl (fun _ => trivial)
      ⟨fun _ => by site_norm; seg_auto using ep_seg, rfl, rfl, fun _ => trivial⟩
  | wr =>
    refine Code.StepAt.of (by intro _; exact ⟨_, Flow.code_1909, rfl, trivial⟩) ?_
    exact Code.step_allocWr (dn := .enter) Flow.code_1909 rfl rfl (fun _ => rfl)
      ⟨fun _ => by site_norm; seg_auto using ep_seg, rfl, rfl, fun _ => trivial⟩
  | enter => cases hx

/-- The hand-off: the startup machine's last state is the role machine's first. -/
theorem handoff : Code.Handoff (S p L g ent) (fun _ => code p L g ent) Start.exit := by
  intro d i t hx h _
  cases d <;> simp only [Start.exit, reduceCtorEq] at hx
  exact ⟨h, trivial⟩

/-- **Every state of the MMA warp's machine from its `setmaxnreg` meets its step
obligation.** -/
theorem stepAt_G (hp : Pre p L m) (hg : g < L.threads) (d : (G p L g ent).D) :
    (G p L g ent).StepAt d :=
  Code.glue_steps (fun d hx => stepAt_S hp d hx) (fun _ d => stepAt hp hg d) handoff d

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Mma
