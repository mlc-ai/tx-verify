-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.OkNext
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Qt
public import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.Sound
import Lemmas.Flow.StepForQ
import Lemmas.Flow.GlueStep
import Lemmas.Flow.StepForQStay
import Lemmas.Flow.AllocTmpl
import Kernels.InklingRelDecode.Proof.Prologue.Strict.Close
import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # The strict window from the first state of the thread: the startup's states

The window of a data lane starts at the thread's first state and covers the startup's states too:
`OkG` holds of a startup state whose base word is the zero word and of a prologue state of the
value thread machine that is `Ok`. `WfG` is `Wf` of the prologue's events and what the window
needs of the startup's (the base load reads zero, the shuffle delivers the warp index) and keeps
the window's events from leaving the prologue (pc 573 is the barrier before the softmax). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat}

/-- The window's events: well-formed for the prologue, and the startup's two loads of words. -/
def WfG (Q : Params) (L : Launch) (g : Nat) (e : Event) : Prop :=
  Wf Q L g e ∧ e.pc ≠ 573 ∧
  (∀ a bs, e.pc = 13 → e.kind = .rd a bs → bs = (b32 0).toBytes.map some) ∧
  (g % L.block < 128 → ∀ m a b c recv ok, e.pc = 17 → e.kind = .shfl m a b c recv ok →
    recv = b32 (g % L.block / 32))

/-- The states of the window: the startup's with the zero base word, the prologue's `Ok` ones. -/
def OkG (Q : Params) (L : Launch) (g : Nat) (d : (threadD Q L g).D) : Prop :=
  (∃ s n, d = (.inl s, n) ∧ s.w = b32 0) ∨ ∃ d' n, d = proDState (b32 0) d' n ∧ Ok Q L g d'

theorem ok_init : Ok Q L g {} :=
  ⟨known_init .., ⟨0, rfl⟩, fun _ _ => ⟨0, rfl⟩, fun _ => rfl⟩

/-- The registers the startup's sites leave untagged hold 32-bit words. -/
theorem proQt_start : ∀ pc ∈ [11, 12, 13, 14, 15, 17], ∀ r ∈ Flow.live pc,
    (!ctl r && !qS r && !(trackedAt pc).contains r) = true →
      r = 529 ∨ r = 530 ∨ r = 531 ∨ r = 534 := by decide +kernel

theorem lookup_filterMap {p : Nat → Bool} {tg tg' : Tag} {r : Nat} :
    ∀ {ls : List Nat}, ((ls.filter p).map fun x => (x, tg)).lookup r = some tg' →
      r ∈ ls ∧ p r = true ∧ tg' = tg
  | [], h => by simp at h
  | x :: xs, h => by
    by_cases hx : p x = true
    · rw [List.filter_cons_of_pos hx, List.map_cons, List.lookup] at h
      by_cases hr : (r == x) = true
      · simp only [hr, Option.some.injEq] at h
        obtain rfl := beq_iff_eq.mp hr
        exact ⟨List.mem_cons_self .., hx, h.symm⟩
      · simp only [hr] at h
        obtain ⟨a, b, c⟩ := lookup_filterMap h
        exact ⟨List.mem_cons_of_mem _ a, b, c⟩
    · rw [List.filter_cons_of_neg hx] at h
      obtain ⟨a, b, c⟩ := lookup_filterMap h
      exact ⟨List.mem_cons_of_mem _ a, b, c⟩

theorem lookup_proQt {pc r : Nat} {tg : Tag} (h : (proQt pc).lookup r = some tg) :
    r ∈ Flow.live pc ∧ (!ctl r && !qS r && !(trackedAt pc).contains r) = true ∧ tg = .bits 32 :=
  lookup_filterMap h

theorem proQt_27 : proQt 27 = [] := by decide +kernel

theorem qt_start {d : Startup.D} {t : TState} (hat : (Startup.code Q L g).AtD d t)
    (hx : d.site ≠ .enter .worker) : QT proQt t := by
  obtain ⟨hpc, -, -, -, hregs⟩ := hat
  have hF : Holds t.regs (Flow.factsFrom (Flow.live d.site.pc) (Startup.valueOf Q L g d)) := hregs
  intro r tg h
  have h' : (proQt d.site.pc).lookup r = some tg := by rw [hpc] at h; exact h
  obtain ⟨hl, hq, rfl⟩ := lookup_proQt h'
  have hv := holds_mem hF (Flow.mem_factsFrom (val := Startup.valueOf Q L g d) hl)
  have hs : d.site.pc ∈ [11, 12, 13, 14, 15, 17] := by
    by_cases h27 : d.site.pc = 27
    · rw [h27, proQt_27] at h'
      simp at h'
    · revert hx h27
      generalize d.site = s
      intro hx h27
      cases s with
      | enter e => cases e <;> first | exact absurd rfl h27 | exact absurd rfl hx
      | _ => decide
  rcases proQt_start _ hs r hl hq with rfl | rfl | rfl | rfl <;>
    exact ⟨_, hv⟩

private theorem select_lane : ∀ tid : Fin 256, Startup.entryOf (BitVec.ofNat 64 (tid.val / 32)) =
    if tid.val < 128 then .dp else .worker := by decide +kernel

/-- The startup's successor on a window event never enters the workers. -/
theorem start_succ (hb : g % L.block < 256) (hlane : g % L.block < 128) {s d' : Startup.D}
    {e : Event} (hw : WfG Q L g e) (hpc : e.pc = s.site.pc)
    (hn : Startup.succ L g s e = some (some d')) :
    d'.site ≠ .enter .worker := by
  obtain ⟨-, -, -, hr⟩ := hw
  obtain ⟨site, tm, x, bw⟩ := s
  obtain ⟨pc, kd⟩ := e
  by_cases sh : site = .shfl
  · subst sh
    change pc = 17 at hpc
    cases kd <;> simp only [Startup.succ] at hn <;> try contradiction
    rename_i m a b c recv ok
    split at hn
    · rename_i y
      cases hn
      have hy := hr hlane m a b c _ ok hpc rfl
      simp only [b32, Value.bits.injEq, true_and] at hy
      have hl := select_lane ⟨_, hb⟩
      simp only at hl
      rw [hy, hl]
      simp [hlane]
    · cases hn
  · cases site <;> simp only [Startup.succ] at hn
    all_goals repeat' split at hn
    all_goals first | contradiction | (cases hn; (intro h; cases h))

/-- The startup's successor on a window event does not lose the lane. -/
theorem start_total (hlane : g % L.block < 128) {s : Startup.D} {e : Event} (hw : WfG Q L g e)
    (hpc : e.pc = s.site.pc) : Startup.succ L g s e ≠ some none := by
  obtain ⟨-, -, -, hr⟩ := hw
  obtain ⟨site, tm, x, bw⟩ := s
  obtain ⟨pc, kd⟩ := e
  by_cases sh : site = .shfl
  · subst sh
    change pc = 17 at hpc
    cases kd <;> simp only [Startup.succ] <;> try trivial
    rename_i m a b c recv ok
    rw [hr hlane m a b c recv ok hpc rfl]
    simp [b32]
  · cases site <;> simp only [Startup.succ]
    all_goals try trivial
    all_goals repeat' split
    all_goals simp

/-- **A startup state steps strictly** on a window event, into a state that holds `QT proQt`. -/
theorem step_start {m : Mem0} (hp : Pre Q L m) (hlane : g % L.block < 128)
    (s : Startup.D) (n : Cls → Nat) (e : Event) (hw : WfG Q L g e) :
    (threadD Q L g).StepForQ (QT proQt) (WfG Q L g) (.inl s, n) e := by
  have hb : g % L.block < 256 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  have key : Code.gatedExit (P := Startup.code Q L g) Startup.enterOf (sel L g) s = none →
      (Startup.code Q L g).StepForQ (QT proQt) (WfG Q L g) s e := by
    intro hx
    have hx' := Code.gatedExit_none.mp hx
    intro t u ins hat hinv hc _ _ hf
    have hpc : e.pc = s.site.pc := EventFrame.fires_source_pc hf
    have hq : ∀ d' t', (Startup.code Q L g).next s e = some (some d') →
        (Startup.code Q L g).Good (some d') t' → QT proQt t' :=
      fun d' t' hn hgd => qt_start hgd.1 (start_succ hb hlane hw hpc hn)
    rcases (startup_steps hp s hx').stepFor e ins hat hinv hc hf with
        (h1 | ⟨d', t', h1, h2, h3⟩) | h4
    · exact absurd h1 (start_total hlane hw hpc)
    · exact .inl ⟨d', t', h1, h2, h3, hq d' t' h1 h3⟩
    · exact .inr h4
  have h : (Code.glue (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g))).StepForQ (QT proQt) (WfG Q L g) (.inl s) e :=
    Code.glue_inl_stepForQ key threadD_handoff
  intro t u ins hat hinv hc hq hw' hf
  exact Code.counted_stepForQ (cls := cls) (@h) n ins hat hinv hc hq hw' hf

theorem querySite_ne (tid : Nat) (d : Control.D) (k : Nat) : querySite tid d k ≠ .exit := by
  unfold querySite; split_ifs <;> (intro h; cases h)

theorem afterInit_ne (i : Fin 12) : afterInit i ≠ .exit := by
  unfold afterInit; split_ifs <;> (intro h; cases h)

theorem afterCopy_ne (d : Control.D) (tid n : Nat) (b : Fin 3) (j : Fin 4) :
    afterCopy d tid n b j ≠ .exit := by
  fin_cases j <;> simp only [afterCopy] <;> try (intro h; cases h)
  split_ifs <;> first | (intro h; cases h) | exact querySite_ne _ _ _

theorem afterQuery_ne (d : Control.D) (tid : Nat) (j : Fin 64) : afterQuery d tid j ≠ .exit := by
  unfold afterQuery; split_ifs <;> first | (intro h; cases h) | exact querySite_ne _ _ _

theorem afterStore_ne (i : Fin 8) (j : Fin 4) : Control.afterStore i j ≠ .exit := by
  unfold Control.afterStore; split_ifs <;> (intro h; cases h)

/-- Only the barrier before the softmax steps to the exit. -/
theorem exit_pred {c c' : Control.D} {e : Event} (hn : Control.next Q L g c e = some (some c'))
    (hx : c'.site = .exit) : c.site = .bar18 := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases s <;> simp only [Control.next] at hn
  all_goals repeat' split at hn
  all_goals first | contradiction | (cases hn; done) | (cases hn; rfl) |
    (cases hn; exact absurd hx (afterInit_ne _)) |
    (cases hn; exact absurd hx (querySite_ne _ _ _)) |
    (cases hn; exact absurd hx (afterCopy_ne _ _ _ _ _)) |
    (cases hn; exact absurd hx (afterQuery_ne _ _ _)) |
    (cases hn; exact absurd hx (afterStore_ne _ _)) |
    (cases hn; exact absurd hx (by intro h; cases h))

/-- The startup keeps the zero base word on a window event. -/
theorem start_word {s s' : Startup.D} {e : Event} (hw : WfG Q L g e) (hpc : e.pc = s.site.pc)
    (h0 : s.w = b32 0) (hn : Startup.succ L g s e = some (some s')) : s'.w = b32 0 := by
  obtain ⟨-, -, hl, -⟩ := hw
  obtain ⟨site, tm, x, bw⟩ := s
  obtain ⟨pc, kd⟩ := e
  dsimp only at h0
  subst h0
  by_cases h13 : site = .ld0
  · subst h13
    change pc = 13 at hpc
    cases kd <;> simp only [Startup.succ] at hn <;> try contradiction
    rename_i a bs
    have hb := hl a bs hpc rfl
    subst hb
    simp only [rebuild_b32] at hn
    split at hn <;> cases hn <;> rfl
  · cases site <;> simp only [Startup.succ] at hn
    all_goals try exact absurd rfl h13
    all_goals repeat' split at hn
    all_goals first | contradiction | (cases hn; done) | (cases hn; rfl)

/-- **The window's states are closed under the machine's steps** on its events. -/
theorem okG_next {m : Mem0} (hp : Pre Q L m) (hlane : g % L.block < 128)
    {d d' : (threadD Q L g).D} {e : Event} (hk : OkG Q L g d) (hw : WfG Q L g e)
    (hpc : e.pc = (threadD Q L g).pc d) (hn : (threadD Q L g).next d e = some (some d')) :
    OkG Q L g d' := by
  have hb : g % L.block < 256 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  obtain ⟨σ, n⟩ := d
  obtain ⟨hn1, hn2⟩ := Code.counted_next_some hn
  rcases hk with ⟨s, n0, hd, hw0⟩ | ⟨d0, n0, hd, hok⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
    obtain ⟨s', hs, hd'⟩ := Code.glue_inl_some hn1
    have hpc' : e.pc = s.site.pc := hpc
    have hne := start_succ hb hlane hw hpc' hs
    have hw' := start_word hw hpc' hw0 hs
    obtain ⟨dd, nn⟩ := d'
    dsimp only at hd' hn2
    by_cases hx : Startup.enterOf s' = none
    · left
      refine ⟨s', nn, ?_, hw'⟩
      rw [hd', Code.enter_none (Code.gatedExit_none.mpr hx)]
    · right
      obtain ⟨site, tm, x, w⟩ := s'
      cases site with
      | enter r =>
        cases r with
        | dp =>
          refine ⟨{}, nn, ?_, ok_init⟩
          subst hd'
          dsimp only at hw'
          subst hw'
          rfl
        | worker => exact absurd rfl hne
      | _ => exact absurd rfl hx
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
    obtain ⟨x', h1, hd1⟩ := Code.glue_inr_some hn1
    obtain ⟨dn, h2, rfl⟩ := Code.glue_inl_some (P := prologueDCode Q L g (b32 0))
      (R := fun e => softDCode e L g)
      (exit := fun c => dataExit Q L g (b32 0) (prologueErase Q L g (b32 0) c)) h1
    have hpc' : e.pc = d0.c.site.pc := hpc
    have hc := (Data.over Q L g (b32 0)).next h2
    have hx : dn.c.site ≠ .exit := fun h => hw.2.1 (hpc'.trans (by rw [exit_pred hc h]; rfl))
    have hex : dataExit Q L g (b32 0) (prologueErase Q L g (b32 0) dn) = none := by
      simp [dataExit, prologueErase, hx]
    obtain ⟨dd, nn⟩ := d'
    dsimp only at hd1 hn2
    right
    refine ⟨dn, nn, ?_, ok_next hok hw.1 hpc' h2⟩
    subst hd1
    simp only [Code.enter, hex]

/-- **A prologue state steps strictly** on a window event, to a prologue state. -/
theorem step_pro {m : Mem0} (hp : Pre Q L m) (hg : g < L.threads) (d : Data.D)
    (n : Cls → Nat) (e : Event) (hk : Ok Q L g d) :
    (threadD Q L g).StepForQ (QT proQt) (WfG Q L g) (proDState (b32 0) d n) e := by
  have h2 : (dataDCode Q L g (b32 0)).StepForQ (QT proQt) (WfG Q L g) (.inl d) e := by
    apply Code.glue_inl_stepForQ_stay
    · intro hx
      have hs : d.c.site ≠ .exit := fun h => by simp [dataExit, prologueErase, h] at hx
      intro t u ins hat hinv hc hq hw hf
      exact step_site hp hg rfl d hs hk e ins hat hinv hc hq hw.1 hf
    · intro hw hpc d' hn
      obtain ⟨-, h573, -⟩ := hw
      have hc := (Data.over Q L g (b32 0)).next hn
      by_contra hne
      have hx : d'.c.site = .exit := by
        by_contra h
        exact hne (by simp [dataExit, prologueErase, h])
      have hb := exit_pred hc hx
      apply h573
      rw [hpc]
      change d.c.site.pc = 573
      rw [hb]; rfl
  have h : (Code.glue (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g))).StepForQ (QT proQt) (WfG Q L g)
      (Sum.inr ⟨Sum.inl (Role.prologue (b32 0)), Sum.inl d⟩) e :=
    Code.glue_inr_stepForQ (i := Sum.inl (Role.prologue (b32 0))) h2
  intro t u ins hat hinv hc hq hw' hf
  exact Code.counted_stepForQ (cls := cls) (@h) n ins hat hinv hc hq hw' hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
