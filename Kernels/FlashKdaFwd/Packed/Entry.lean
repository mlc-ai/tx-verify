-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Program
public import Kernels.FlashKdaFwd.Packed.Prologue
public import Kernels.FlashKdaFwd.Packed.ProjectionAddress
public import Kernels.FlashKdaFwd.Packed.MatrixRegs
public import Kernels.FlashKdaFwd.Packed.OutputMap
public import Kernels.FlashKdaFwd.Packed.PartialOutput
public import Kernels.FlashKdaFwd.Packed.Producer

@[expose] public section
namespace FlashKda.Packed.Entry
open PTX
attribute [local irreducible] FlashKda.Packed.kernel

theorem parameters (b : Nat → Nat → Nat) (L : Launch) (g : Nat) (v : BitVec 64)
    (host : L.params (Prologue.param 15) = some v) :
    run kernel (Prologue.assumptions b) L g 13 {} = some (Prologue.ready v) := by
  apply Prologue.bind_launch b L kernel g v host
  · intro i hi
    have f := fetch (pc := 0) (n := 13) (i := i) (by decide) (by omega) Prologue.sites
    have len : i < ((List.range 11).map Prologue.address).length := by simpa using hi
    simpa only [Nat.zero_add, List.getElem?_append_left len,
      List.getElem?_map, List.getElem?_range hi, Option.map_some] using f
  · exact fetch (pc := 0) (i := 11) (by decide) (by decide) Prologue.sites
  · exact fetch (pc := 0) (i := 12) (by decide) (by decide) Prologue.sites

theorem load_warp_election (base : Nat → Nat → Nat) (L : Launch) (l : Fin 32)
    (v : BitVec 64) (host : L.params (Prologue.param 15) = some v)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) :
    ∃ t, Next kernel (Prologue.assumptions base) L (128+l.val) {} t
      (.elect 0xffffffff fun leader => next (setReg (setReg t 3415 (Proof.b32 leader)) 3416
        (.pred (laneOf L (128+l.val) == leader)))) ∧ t.pc = 32 ∧ t.fault = none := by
  have headRun := parameters base L (128+l.val) v host
  obtain ⟨t,rs,pc,clear,mask⟩ := Producer.before_election base L kernel (Prologue.ready v) l
    block threads rfl rfl (fun i hi =>
      fetch (pc := 13) (n := 19) (i := i) (by decide) hi Producer.sites)
  have site : kernel.code[32]? = some Election.elect :=
    fetch (pc := 32) (n := 1) (i := 0) (by decide) (by decide) Election.sites.1
  refine ⟨t, ⟨run_rtg (run_comp headRun rs), ?_⟩, pc, clear⟩
  simp only [out, clear, pc, site, show guardHolds t Election.elect.guard = .ok true from rfl,
    show Election.elect.op.isLocal = false from rfl, Bool.false_eq_true, ite_false]
  exact congrArg Out.ev (Election.choose L (128+l.val) t mask)

theorem selected_lane (base : Nat → Nat → Nat) (L : Launch) (l : Fin 32) (v : BitVec 64)
    (host : L.params (Prologue.param 15) = some v) (block : L.block = 192)
    (threads : L.ntid = ⟨192,1,1⟩) :
    ∃ t u, Run kernel (Prologue.assumptions base) L (128+l.val) {}
        [⟨32,.elect 0xffffffff 0 l.val⟩] (some t) ∧
      run kernel (Prologue.assumptions base) L (128+l.val) 9 t = some u ∧
      u.pc = 48 ∧ u.fault = none ∧ u.regs 88 = some (.pred false) := by
  obtain ⟨s,atEvent,pc,clear⟩ := load_warp_election base L l v host block threads
  obtain ⟨u,post,flags⟩ := Producer.after_election base L kernel s (128+l.val) l.val pc clear
    (fun i hi => fetch (pc := 33) (n := 9) (i := i) (by decide) hi Producer.selected_sites)
  have lane : laneOf L (128+l.val) = l.val := by
    unfold laneOf
    rw [block, Nat.mod_eq_of_lt (show 128+l.val < 192 by omega)]
    omega
  refine ⟨Producer.chosen s l.val,u,Run.step atEvent.steps ⟨_,atEvent.stop,?_⟩ (.nil _),post,flags⟩
  exact ⟨0,l.val,by rw [pc],by simp [lane,Producer.chosen]⟩

theorem initial_state_loads : (kernel.code.drop 330).take 49 =
    (List.range 16).flatMap Transfers.load :=
  code_window (by decide) Transfers.initial

theorem final_state_stores : (kernel.code.drop 3783).take 52 = (List.range 16).flatMap
    Transfers.store ++ [⟨none, .bulkCommit⟩, ⟨none, .bulkWait .read 0⟩,
      ⟨none, .barSync (.imm 0) true⟩, ⟨none, .ret⟩] := code_window (by decide) Transfers.finalStores

theorem projection : (((kernel.code.drop 2193).take 112).foldlM Projection.step {}).map
    Projection.summary = some (64, (List.range 32).map Projection.address, (List.range 8).map
      fun i => (List.range 4).map (Projection.Word.product (56+i))) := by
  have f := Projection.register_flow
  rw [instructions (pc := 2193) (n := 112) (by decide)] at f
  exact f

theorem first_multiply : kernel.code[2199]? = some ⟨none,.matrix Matrix.first⟩ :=
  fetch (pc := 2199) (n := 1) (i := 0) (by decide) (by decide) Matrix.first_site

theorem partial_load : (kernel.code.drop 3019).take 5 = ⟨none, .mem PartialOutput.load⟩ ::
    (List.range 4).map PartialOutput.unpack := code_window (by decide) PartialOutput.sites

theorem scalar_stores : (kernel.code.drop 3024).take 8 =
    (List.range 8).map fun i => ⟨none, .mem (Tail.store i)⟩ := code_window (by decide) Tail.sites

theorem bulk_stores : (kernel.code.drop 3051).take 32 = [OutputMap.copy 0] ++
    ((List.range 15).flatMap fun j => [OutputMap.advance (j+1), OutputMap.copy (j+1)]) ++
    [⟨none, .bulkCommit⟩] := code_window (by decide) OutputMap.sites

theorem producer_check (b : Nat → Nat → Nat) (L : Launch) (g : Nat) (t : TState)
    (pc : t.pc = 1454) (ok : t.fault = none) (go : t.regs 2 = some (.pred false)) :
    Run kernel (Prologue.assumptions b) L g t [⟨1455, .ub .noRule⟩] none := by
  apply Election.stop_path b kernel L g t _ _ pc ok go
  · exact fetch (pc := 1454) (i := 0) (by decide) (by decide) Election.sites.2.2
  · exact fetch (pc := 1454) (i := 1) (by decide) (by decide) Election.sites.2.2

end FlashKda.Packed.Entry
