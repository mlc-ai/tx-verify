-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Bar1Count

@[expose] public section

/-! # Barrier 1's count along the workers, modulo 3

A worker's barrier-1 count is, modulo 3, the phase of its state (`wph`): 0 at the dispatch loop's
head and at each role's last site, 1 after the head's `barrier.sync 1` (the role byte's load, each
role's first sites, the exit path), 2 between a role's two `barrier.sync 1`. Each role machine's
step moves the phase by one exactly at a pc of `bar1Pcs` (`ld_ph_next`, `mm_ph_next`,
`idle_ph_next`, `wk_ph_next`). So a dispatch read is at a count `≡ 1 (mod 3)`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The loader's phase by site. -/
def ldPh : Proof.Loader.Site → Nat
  | .setMaxDec | .ld0 | .ld1 | .bar0 => 1
  | .setMaxInc => 0
  | _ => 2

/-- One if the pc is a `barrier.sync 1`. -/
def b1At (pc : Nat) : Nat := if pc ∈ bar1Pcs then 1 else 0

theorem ld_ph_next {d d' : Proof.Loader.D} {e : Event}
    (h : Proof.Loader.next L g d e = some (some d')) :
    ldPh d'.site = (ldPh d.site + b1At d.site.pc) % 3 := by
  unfold Proof.Loader.next at h
  split at h
  all_goals
    repeat' first
      | (split at h)
      | (simp only [Proof.Loader.readI, Proof.Loader.readN, Proof.Loader.afterIter] at h)
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       rename_i hs
       first
         | (simp only [hs]; decide)
         | (simp_all; decide))

/-- The MMA warp's phase by site. -/
def mmPh : Proof.Mma.Site → Nat
  | .setMaxReg | .ldNum | .bar0 => 1
  | .setMaxRegInc => 0
  | _ => 2

theorem qk_b1 : ∀ j : Fin 8, b1At (Proof.Mma.Site.qk j).pc = 0 := by decide
theorem pv_b1 : ∀ j : Fin 8, b1At (Proof.Mma.Site.pv j).pc = 0 := by decide

theorem mm_ph_next {d d' : Proof.Mma.D} {e : Event}
    (h : Proof.Mma.next L g d e = some (some d')) :
    mmPh d'.site = (mmPh d.site + b1At d.site.pc) % 3 := by
  unfold Proof.Mma.next at h
  split at h
  all_goals
    repeat' first
      | (split at h)
      | (simp only [Proof.Mma.start, Proof.Mma.iterNext, Proof.Mma.afterQk, Proof.Mma.qkNext,
          Proof.Mma.pvNext] at h)
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       rename_i hs
       first
         | (simp only [hs]; decide +revert)
         | (simp_all [mmPh, qk_b1, pv_b1]; done)
         | (simp_all; decide +revert))

/-- The idle role's phase by site. -/
def idPh : Proof.Worker.Idle.Site → Nat
  | .dec | .bar0 => 1
  | .bar1 => 2
  | .inc => 0

theorem idle_ph_next {d d' : Proof.Worker.Idle.D} {e : Event}
    (h : Proof.Worker.Idle.next d e = some (some d')) :
    idPh d'.site = (idPh d.site + b1At d.site.pc) % 3 := by
  obtain ⟨site, P⟩ := d
  cases site <;> simp only [Proof.Worker.Idle.next, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> dsimp only <;> decide

/-- The worker's phase by state. -/
def wph : Proof.WComp.WSt → Nat
  | .worker w =>
    match w.site with
    | .ldRole | .bad0 => 1
    | .bad1 => 2
    | _ => 0
  | .idle d => idPh d.site
  | .loader d _ => ldPh d.site
  | .mma d _ => mmPh d.site
  | .exit _ => 1

/-- **A worker's step moves its phase by one exactly at a `barrier.sync 1`.** -/
theorem wcomp_ph_next {b : Value} {σ σ' : Proof.WComp.WSt} {e : Event} (hW : WSite b σ)
    (h : Proof.WComp.next L g σ e = some (some σ')) :
    wph σ' = (wph σ + b1At (Proof.WComp.pc σ)) % 3 := by
  cases σ with
  | worker w =>
    obtain ⟨site, P⟩ := w
    obtain ⟨hs, -⟩ := hW
    simp only at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.some.injEq,
        Option.map] at h
      subst h; dsimp only [wph, Proof.WComp.pc]; decide
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.some.injEq,
        Option.map] at h
      subst h; dsimp only [wph, Proof.WComp.pc]; decide
    · simp only [Proof.WComp.next, Proof.WComp.dispatch] at h
      rcases hw : Proof.Worker.next L g ⟨.ldRole, P⟩ e with _ | _ | d'
      · rw [hw] at h; cases h
      · rw [hw] at h; cases h
      · rw [hw] at h
        simp only at h
        obtain ⟨site', P'⟩ := d'
        simp only [Proof.WComp.roleStart] at h
        cases site' <;> simp only [Option.some.injEq, reduceCtorEq] at h
        all_goals first
          | (subst h
             simp only [wph, Proof.WComp.pc, Proof.Loader.D.start, Proof.Worker.Idle.D.start,
               ldPh, idPh]
             decide)
          | (split at h
             · split at h
               · simp only [Option.some.injEq] at h
                 subst h
                 simp only [wph, Proof.WComp.pc, mmPh]
                 decide
               · cases h
             · cases h)
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.some.injEq,
        Option.map] at h
      subst h; dsimp only [wph, Proof.WComp.pc]; decide
    · simp only [Proof.WComp.next, Proof.Worker.next, Option.some.injEq,
        Option.map] at h
      subst h; dsimp only [wph, Proof.WComp.pc]; decide
  | idle d =>
    simp only [Proof.WComp.next] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      subst h
      show 0 = (idPh d.site + b1At d.site.pc) % 3
      rw [hs]; decide
    · obtain ⟨d', hd', rfl⟩ := mm_some h
      exact idle_ph_next hd'
  | loader d P =>
    simp only [Proof.WComp.next] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      subst h
      show 0 = (ldPh d.site + b1At d.site.pc) % 3
      rw [hs]; decide
    · obtain ⟨d', hd', rfl⟩ := mm_some h
      exact ld_ph_next hd'
  | mma d P =>
    simp only [Proof.WComp.next] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      subst h
      show 0 = (mmPh d.site + b1At d.site.pc) % 3
      rw [hs]; decide
    · obtain ⟨d', hd', rfl⟩ := mm_some h
      exact mm_ph_next hd'
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site
    · simp only [Proof.WComp.next, Option.some.injEq] at h
      subst h; dsimp only [wph, Proof.WComp.pc]; decide
    · simp [Proof.WComp.next] at h

/-- An instruction `barrier.sync 1` without a guard. -/
def isBar1Ins : Option Instr → Bool
  | some ⟨none, .barSync (.imm 1) _⟩ => true
  | _ => false

theorem kernel_bar1_ins : bar1Pcs.all (fun pc => isBar1Ins kernel.code[pc]?) = true := by
  decide +kernel

/-- Every `barrier.sync 1` position holds `barrier.sync 1` without a guard. -/
theorem kernel_bar1_code {pc : Nat} (hp : pc ∈ bar1Pcs) {ins : Instr}
    (hc : kernel.code[pc]? = some ins) : ∃ al, ins.op = .barSync (.imm 1) al := by
  have h := List.all_eq_true.mp kernel_bar1_ins pc hp
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  unfold isBar1Ins at h
  split at h
  · rename_i al heq
    simp only [Option.some.injEq, Instr.mk.injEq] at heq
    exact ⟨al, heq.2⟩
  · cases h

/-- **An event is a barrier-1 event exactly at a `barrier.sync 1` position.** -/
theorem bar1_iff {pc : Nat} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hb : L.block ≠ 128) :
    (if Execution.isBarId 1 e then 1 else 0) = b1At pc := by
  by_cases hp : pc ∈ bar1Pcs
  · obtain ⟨al, hop⟩ := kernel_bar1_code hp hc
    rw [hop] at hf
    rw [Proof.EvD.fires_barSync_imm (id := 1) (by omega) hf]
    simp [b1At, hp, Execution.isBarId]
  · rw [notBar1 hc hf hb hp]
    simp [b1At, hp]

/-- **The workers' barrier-1 count modulo 3** (and none in the startup). -/
def W1 (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat → Prop
  | (.inl _, _), c => c = 0
  | (.inr ⟨.inl (.worker _), σ⟩, _), c => c % 3 = wph σ
  | _, _ => True

theorem next_same_role {i : Role ⊕ Startup.Entry}
    {d : (Code.withStubs (frag Q L g) Startup.Entry.pc i).D} {n : Cls → Nat} {e : Event}
    {σ' : (thread Q L g).D} (h : (thread Q L g).next (.inr ⟨i, d⟩, n) e = some (some σ')) :
    ∃ d', σ'.1 = .inr ⟨i, d'⟩ := by
  simp only [thread, Code.roleThread, Code.counted, Code.glue] at h
  rcases hr : (Code.withStubs (frag Q L g) Startup.Entry.pc i).next d e with _ | _ | d'
  · rw [hr] at h; simp at h
  · rw [hr] at h; simp at h
  · rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨d', by rw [← h]⟩

/-- **A continuing step keeps the workers' count modulo 3.** -/
theorem w1_step (hp : Pre Q L m) {σ σ' : (thread Q L g).D} {e : Event}
    {t u : TState} {ins : Instr} (hJ : Ref Q L g σ) (hat : (thread Q L g).AtD σ t)
    (hi : (thread Q L g).inv σ) (hc : kernel.code[(thread Q L g).pc σ]? = some ins)
    (hf : Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e (some u))
    {c : Nat} (hC : W1 Q L g σ c) (hn : (thread Q L g).next σ e = some (some σ')) :
    W1 Q L g σ' (c + if Execution.isBarId 1 e then 1 else 0) := by
  have hb : L.block ≠ 128 := by rw [hp.block]; decide
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · have hC' : c = 0 := hC
    rw [notBar1 hc hf hb (fun h => startup_bar1 s.site h)]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [next_start] at hn
    obtain ⟨s', -, rfl⟩ := mm_some hn
    simp only [Code.enter]
    split
    · rename_i j _
      rcases j with (_ | _) | _
      · trivial
      · show c % 3 = 0
        rw [hC']
      · trivial
    · exact hC'
  · rename_i i
    obtain ⟨d', hd'⟩ := next_same_role hn
    obtain ⟨x', n'⟩ := σ'
    simp only at hd'
    subst hd'
    cases i with
    | dp tm bw => trivial
    | worker w =>
      have hC' : c % 3 = wph d := hC
      rw [next_worker] at hn
      obtain ⟨σw', hσw, he'⟩ := mm_some hn
      simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
      obtain ⟨he1, -⟩ := he'
      subst he1
      show (c + _) % 3 = wph σw'
      have hW : WSite (b32 0) d := hJ.2.2.1
      have hb1 : ∀ x, b1At x < 3 := fun x => by unfold b1At; split <;> omega
      rw [wcomp_ph_next hW hσw, bar1_iff hc hf hb, Nat.add_mod, hC', Nat.mod_eq_of_lt (hb1 _)]
  · exact hJ.elim

/-- **The workers' barrier-1 count modulo 3 along a thread.** -/
theorem w1_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      W1 Q L g σ (((X.tr g).take k).countP (Execution.isBarId 1)) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rfl
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX (k := k) he hk0
      cases o with
      | none => exact absurd (fires_none_ends hf) (not_ends_of_lt hX hg he hk)
      | some u =>
        rw [List.take_add_one, he, Option.toList_some, countP_snoc]
        exact w1_step hp (hF.2 σ hk0) hat hi hc hf (ih hlt σ hk0) hn

end
end PTX.Kernels.InklingRelDecode.Proof2
