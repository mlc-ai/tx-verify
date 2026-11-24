-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts
public import Lemmas.Flow.NotShfl
public import Lemmas.Order.WarpBarOrdinal
public import Lemmas.Flow.Hooks

@[expose] public section

/-!
# The warp barriers of the kernel, by role

Only `bar.warp.sync` fires a warp-barrier event (`fires_warpBar_op`, by the same case analysis
over the templates as `Lemmas/Flow/NotShfl.lean`; it is generic and a candidate for `Lemmas/`).
An audit of the decoded program by `decide +kernel` lists the kernel's ten `bar.warp.sync`
positions: the loader's five (`wb0` … `wb4`) and the MMA warp's five (`qkBar`, `qkBar2`, `pvBar`,
`pvBar2`, `finBar`; `qkSkip` and `pvSkip` are the sites at the positions of `qkBar2` and `pvBar2`
on the branch that skips a half). So a warp-barrier event of an execution fires from a loader or
an MMA state at one of those sites, and its member mask is the full warp (`warpBar_event_state`,
`warpBar_mask`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### Only `bar.warp.sync` fires a warp barrier -/

/-- A `bar.warp.sync` instruction. -/
def isWarpBarOp : Op → Bool
  | .warp ⟨.barWarp, _, _, _, _⟩ => true
  | _ => false

/-- A template that is no warp barrier. -/
def NotWarpBar : Tmpl → Prop
  | .warpBar .. => False
  | _ => True

theorem ofExec_notWarpBar {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotWarpBar r) :
    NotWarpBar (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notWarpBar {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotWarpBar m) :
    NotWarpBar (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

theorem localSregTmpl_notWarpBar {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotWarpBar (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotWarpBar]

theorem ruleTmpl_notWarpBar {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotWarpBar (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notWarpBar
  · simp only [NotWarpBar]

theorem ite_notWarpBar {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotWarpBar a)
    (hb : NotWarpBar b) : NotWarpBar (if c then a else b) := by
  split <;> assumption

/-- Every instruction other than `bar.warp.sync` fires no warp barrier. -/
theorem eventTmpl_notWarpBar {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : isWarpBarOp op = false) : NotWarpBar (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> first
      | (simp [isWarpBarOp] at hop; done)
      | (simp only [eventTmpl, warpTmpl, shflTmpl, electTmpl, voteTmpl, voteModeTmpl,
           reduxTmpl, matchTmpl, activemaskTmpl]
         repeat' first
           | trivial
           | split)
  case int i => exact ruleTmpl_notWarpBar (op := .int i)
  case move m => exact ruleTmpl_notWarpBar (op := .move m)
  case cvt c => exact ruleTmpl_notWarpBar (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notWarpBar
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWarpBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        SetMaxNReg.tmpl, matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcTmpl, tcCommitTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWarpBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notWarpBar)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- **A warp-barrier event is fired by a `bar.warp.sync`.** -/
theorem fires_warpBar_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hs : Execution.isWarpBar e = true) : isWarpBarOp op = true := by
  by_contra hq
  have hm := eventTmpl_notWarpBar (A := A) (L := L) (g := g) (t := t) (by simpa using hq)
  obtain ⟨epc, ek⟩ := e
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotWarpBar] at hm <;>
    simp only [Fires] at hf <;> cases ek <;> simp_all [Execution.isWarpBar]

/-! ### The kernel's `bar.warp.sync` positions -/

/-- Prove a statement about the sites of one machine at a list of positions. -/
local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

def warpBarPcs : List Nat :=
  [Loader.Site.wb0.pc, Loader.Site.wb1.pc, Loader.Site.wb2.pc, Loader.Site.wb3.pc,
    Loader.Site.wb4.pc, Mma.Site.qkBar.pc, Mma.Site.qkBar2.pc, Mma.Site.pvBar.pc,
    Mma.Site.pvBar2.pc, Mma.Site.finBar.pc]

theorem kernel_warpBar_pcs : OpPcsFast kernel.code isWarpBarOp warpBarPcs = true := by
  decide +kernel

theorem dstart_warpBar : ∀ s : DStart.Site, s.pc ∈ warpBarPcs → s ∈ ([] : List DStart.Site) := by
  site_cls
theorem pro_warpBar : ∀ s : ProA.Site, s.pc ∈ warpBarPcs → s ∈ ([] : List ProA.Site) := by site_cls
theorem sm_warpBar : ∀ s : Sm.Site, s.pc ∈ warpBarPcs → s ∈ ([] : List Sm.Site) := by site_cls
theorem epi_warpBar : ∀ s : Epi.Site, s.pc ∈ warpBarPcs → s ∈ ([] : List Epi.Site) := by site_cls
theorem worker_warpBar : ∀ s : Worker.Site, s.pc ∈ warpBarPcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_warpBar : ∀ s : Worker.Idle.Site, s.pc ∈ warpBarPcs →
    s ∈ ([] : List Worker.Idle.Site) := by site_cls
theorem loader_warpBar : ∀ s : Loader.Site, s.pc ∈ warpBarPcs →
    s ∈ ([.wb0, .wb1, .wb2, .wb3, .wb4] : List Loader.Site) := by site_cls
theorem mma_warpBar : ∀ s : Mma.Site, s.pc ∈ warpBarPcs →
    s ∈ ([.qkBar, .qkBar2, .pvBar, .pvBar2, .finBar, .qkSkip, .pvSkip] : List Mma.Site) := by
  site_cls
theorem exit_warpBar : ∀ s : WComp.ExitSite, s.pc ∈ warpBarPcs →
    s ∈ ([] : List WComp.ExitSite) := by site_cls

/-- The loader's warp-barrier sites. -/
def _root_.PTX.Kernels.InklingRelDecode.Proof.Loader.Site.isWb : Loader.Site → Bool
  | .wb0 | .wb1 | .wb2 | .wb3 | .wb4 => true
  | _ => false

/-- The MMA warp's warp-barrier sites. -/
def _root_.PTX.Kernels.InklingRelDecode.Proof.Mma.Site.isWb : Mma.Site → Bool
  | .qkBar | .qkBar2 | .pvBar | .pvBar2 | .finBar | .qkSkip | .pvSkip => true
  | _ => false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A warp barrier is the loader's or the MMA warp's**, at one of their warp-barrier sites,
with the full member mask. -/
theorem warpBar_event_state (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : Execution.isWarpBar e = true) :
    ((∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site.isWb = true) ∨
    (∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      d.site.isWb = true)) ∧ ∃ inst, e.kind = .warpBar 4294967295 inst := by
  have hk' : ∃ m inst, e.kind = .warpBar m inst := by
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp_all [Execution.isWarpBar]
  obtain ⟨m0, i0, hk0⟩ := hk'
  obtain ⟨s, t, ins, o, u, hσ, hc, hf, hF⟩ := event_pre hX hS ht hg he
    (not_ends (by intro f h; rw [hk0] at h; cases h) (by intro h; rw [hk0] at h; cases h))
    (no_ub_of_kind (by intro f h; rw [hk0] at h; cases h))
  have hop : isWarpBarOp ins.op = true := fires_warpBar_op hf hk
  have hpw : TSt.pc s ∈ warpBarPcs := OpPcsFast.mem kernel_warpBar_pcs hc hop
  have hr := treach_stateAt hpre hg hσ
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_warpBar w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_warpBar d.site h)
    | exit x => exact absurd hpw (fun h => by simpa using exit_warpBar x.site h)
    | loader d P =>
      have hs := loader_warpBar d.site hpw
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      have hsh := EvW.loader_shapeW hpre hr.2 (g := g) (d := d) (P := P) (u := u)
        ⟨t', ⟨ha, hi.2⟩, hf'⟩
      unfold EvW.LdShapeW at hsh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with h | h | h | h | h <;> rw [h] at hsh <;> obtain ⟨inst, rfl⟩ := hsh <;>
        exact ⟨.inl ⟨d, P, hσ, by rw [h]; rfl⟩, inst, rfl⟩
    | mma d P =>
      have hs := mma_warpBar d.site hpw
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      have hsh := EvW.mma_shape hpre hg (d := d) (P := P) (u := u) ⟨t', ⟨ha, hi.2⟩, hf'⟩
      unfold EvW.MmShape at hsh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with h | h | h | h | h | h | h <;> rw [h] at hsh <;> obtain ⟨inst, rfl⟩ := hsh <;>
        exact ⟨.inr ⟨d, P, hσ, by rw [h]; rfl⟩, inst, rfl⟩
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_warpBar d.site h)
    | pro d => exact absurd hpw (fun h => by simpa using pro_warpBar d.site h)
    | sm d => exact absurd hpw (fun h => by simpa using sm_warpBar d.site h)
    | epi d => exact absurd hpw (fun h => by simpa using epi_warpBar d.site h)

/-- **Every warp barrier of the kernel has the full member mask.** -/
theorem warpBar_mask (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {e : EvId} {m inst : Nat} (h : X.WarpBar e m inst) : m = 4294967295 := by
  obtain ⟨pc, hp⟩ := h
  have hg : e.1 < L.threads := Frame.lt_of_get hX hp
  obtain ⟨-, inst', hk⟩ := warpBar_event_state hpre hX hS ht hg hp rfl
  simp only [Kind.warpBar.injEq] at hk
  exact hk.1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
