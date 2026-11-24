-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ScSm
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleAll
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead
public import Kernels.InklingRelDecode.Proof.Thread.FootRole
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.NotRead

@[expose] public section

/-!
# The shared reads of a tracked thread, by footprint

`TRead L g s a` says what a shared read event with footprint `a` is, given the abstract state `s`
of thread `g` before it. The program's loads from shared memory are seven (`kernel_shared_load_pcs`,
`decide +kernel` over the decoded program):

* the Tensor Memory base word's read, four bytes at `sharedBase`, by the default partition
  (`DStart.Site.ld0`) and by a worker (`Worker.Site.ld0`);
* the worker's role byte, one byte at `sharedBase + 213332 + warp` (`Worker.Site.ldRole`);
* the loader's read of `(num_pre, num_iters)`: two four-byte elements at `sharedBase + 212992` and
  `+ 212996` (`Loader.Site.ld0`, `ld1`), and the MMA warp's read of `num_iters` at
  `sharedBase + 212996` (`Mma.Site.ldNum`);
* the softmax region's read of the four warps' minima, four bytes at
  `sharedBase + 212992 + 4 (tid % 4)` (`Sm.Site.ldL`).

`thread_read_class` is the statement for a thread whose machine tracked through the read (`TT`)
from the soundness of the machines and `Pre`; every footprint is in the thread's own CTA and in a
region of `Safety.Regions` (`TRead.inRegions`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The positions of the instructions that read shared memory. -/
def sharedLoadPcs : List Nat :=
  [DStart.Site.ld0.pc, Worker.Site.ld0.pc, Worker.Site.ldRole.pc, Loader.Site.ld0.pc,
    Loader.Site.ld1.pc, Mma.Site.ldNum.pc, Sm.Site.ldL.pc]

/-- Instructions that read shared memory directly or through a dynamic address. -/
def sharedLoadOp (op : Op) : Bool :=
  loadSpace op == some .shared || (dynamicAccess op && readOp op)

/-- **The shared reads of the program are the seven loads above.** -/
theorem kernel_shared_load_pcs : OpPcsFast kernel.code sharedLoadOp sharedLoadPcs = true := by
  decide +kernel

/-- **A shared read event is fired at one of the seven read positions.** -/
theorem read_pc_shared {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    {pc : Nat} {e : Event} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o)
    (hk : e.kind = .rd a bs) (hsp : a.loc.space = .shared) : pc ∈ sharedLoadPcs := by
  refine OpPcsFast.mem kernel_shared_load_pcs hc ?_
  rcases fires_read_loc hf hk with ⟨h, -⟩ | h
  · simp [sharedLoadOp, h, hsp]
  · simp [sharedLoadOp, h, fires_read_op hf hk]

/-! ### The sites of each machine at those positions -/

theorem pro_pc_notLoad (s : ProA.Site) : s.pc ∉ sharedLoadPcs := by
  cases s
  all_goals decide +kernel

theorem dstart_pc_load (s : DStart.Site) (h : s.pc ∈ sharedLoadPcs) : s = .ld0 := by
  revert h
  cases s
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem sm_pc_load (s : Sm.Site) (h : s.pc ∈ sharedLoadPcs) : s = .ldL := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem epi_pc_notLoad (s : Epi.Site) : s.pc ∉ sharedLoadPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_load (s : Worker.Site) (h : s.pc ∈ sharedLoadPcs) : s = .ld0 ∨ s = .ldRole := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem idle_pc_notLoad (s : Worker.Idle.Site) : s.pc ∉ sharedLoadPcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_load (s : Loader.Site) (h : s.pc ∈ sharedLoadPcs) : s = .ld0 ∨ s = .ld1 := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem mma_pc_load (s : Mma.Site) (h : s.pc ∈ sharedLoadPcs) : s = .ldNum := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem exit_pc_notLoad (s : WComp.ExitSite) : s.pc ∉ sharedLoadPcs := by
  cases s
  all_goals decide +kernel

/-! ### The classification -/

/-- **What a shared read is, from the state of its thread.** -/
inductive TRead (L : Launch) (g : Nat) : TSt → Acc → Prop
  | dstart {d : DStart.D} {a : Acc} (hs : d.site = .ld0)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase⟩) (hz : a.size = 4) :
      TRead L g (.d (.dstart d)) a
  | base {w : Worker.D} {a : Acc} (hs : w.site = .ld0)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase⟩) (hz : a.size = 4) :
      TRead L g (.w (.worker w)) a
  | role {w : Worker.D} {a : Acc} (hs : w.site = .ldRole)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase + 213332 + WComp.warpOf L g⟩)
      (hz : a.size = 1) : TRead L g (.w (.worker w)) a
  | ld0 {d : Loader.D} {P : Loader.Pro} {a : Acc} (hs : d.site = .ld0)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase + 212992⟩) (hz : a.size = 4) :
      TRead L g (.w (.loader d P)) a
  | ld1 {d : Loader.D} {P : Loader.Pro} {a : Acc} (hs : d.site = .ld1)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4⟩) (hz : a.size = 4) :
      TRead L g (.w (.loader d P)) a
  | ldNum {d : Mma.D} {P : Loader.Pro} {a : Acc} (hs : d.site = .ldNum)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase + 212996⟩) (hz : a.size = 4) :
      TRead L g (.w (.mma d P)) a
  | scratch {d : Sm.D} {a : Acc} (hs : d.site = .ldL)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase + g % L.block % 4 * 4 + 212992⟩)
      (hz : a.size = 4) : TRead L g (.d (.sm d)) a

/-- **A shared read of a thread tracked through it is one of the seven kinds.** -/
theorem thread_read_class (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    {s : TSt} (hσ : St Q L X g k = some (some s)) (hsp : a.loc.space = .shared) :
    TRead L g s a := by
  have hk : (⟨pc, .rd a bs⟩ : Event).kind = .rd a bs := rfl
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hpw : TSt.pc s ∈ sharedLoadPcs := read_pc_shared hc hf hk hsp
  have hr := treach_stateAt hpre hg hσ
  have hSh := ProA.sharedOk_of_pre hpre
  cases s with
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
      obtain ⟨t', hgd, hfire⟩ := hF
      have hF' : (WComp.code L g Q).toMachine.Fired (some (.worker ⟨site, P⟩)) ⟨pc, .rd a bs⟩
          (some u) := ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
      rcases worker_pc_load site hpw with hs | hs
      · subst hs
        obtain ⟨pc', ac, bs', he2, hl, hz⟩ := worker_ld0_shape hpre (g := g)
          (w := ⟨.ld0, P⟩) rfl hF'
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, rfl⟩ := he2
        exact .base rfl hl hz
      · subst hs
        have hg256 : g % L.block < 256 := by
          have := hpre.block
          rw [this]
          exact Nat.mod_lt _ (by omega)
        obtain ⟨ac, bs', he2, hl, hz⟩ := Worker.shape_ldRole hpre (w := ⟨.ldRole, P⟩) hg256 rfl
          hF'
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, rfl⟩ := he2
        exact .role rfl hl hz
    | idle d => exact absurd hpw (idle_pc_notLoad d.site)
    | loader d P =>
      obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
      obtain ⟨t', hgd, hfire⟩ := hF
      have hF' : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) ⟨pc, .rd a bs⟩
          (some u) := ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
      have hsh := EvW.loader_shapeW hpre hr.2 (g := g) (d := d) (P := P) (u := u) hF'
      unfold EvW.LdShapeW at hsh
      rcases loader_pc_load d.site hpw with hs | hs
      · rw [hs] at hsh
        obtain ⟨ac, bs', he2, hl, hz, -⟩ := hsh
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, rfl⟩ := he2
        exact .ld0 hs hl hz
      · rw [hs] at hsh
        obtain ⟨ac, bs', he2, hl, hz, -⟩ := hsh
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, rfl⟩ := he2
        exact .ld1 hs hl hz
    | mma d P =>
      obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
      obtain ⟨t', hgd, hfire⟩ := hF
      have hF' : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) ⟨pc, .rd a bs⟩
          (some u) := ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
      have hsh := EvW.mma_shape hpre hg (d := d) (P := P) hF'
      unfold EvW.MmShape at hsh
      have hs := mma_pc_load d.site hpw
      rw [hs] at hsh
      obtain ⟨ac, bs', he2, hl, hz⟩ := hsh
      simp only [Event.mk.injEq, Kind.rd.injEq] at he2
      obtain ⟨-, rfl, rfl⟩ := he2
      exact .ldNum hs hl hz
    | exit x => exact absurd hpw (exit_pc_notLoad x.site)
  | d s =>
    cases s with
    | dstart d =>
      obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
      have hs := dstart_pc_load d.site hpw
      obtain ⟨ac, bs', he2, hl, hz, -⟩ := DStart.shape_ld0 hSh (fired_dstart hF) hs
      simp only [Event.mk.injEq, Kind.rd.injEq] at he2
      obtain ⟨-, rfl, rfl⟩ := he2
      exact .dstart hs hl hz
    | pro d => exact absurd hpw (pro_pc_notLoad d.site)
    | sm d =>
      obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
      have hs := sm_pc_load d.site hpw
      obtain ⟨ac, bs', he2, hl, hz⟩ := Sm.shape_ldL_foot hSh (fired_sm hF) hs
      simp only [Event.mk.injEq, Kind.rd.injEq] at he2
      obtain ⟨-, rfl, rfl⟩ := he2
      exact .scratch hs hl hz
    | epi d => exact absurd hpw (epi_pc_notLoad d.site)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
