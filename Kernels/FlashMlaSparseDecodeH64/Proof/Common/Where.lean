-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows
public import Lemmas.Kernel.UbLast

@[expose] public section

/-! # Where the states are: a state of the thread machine by its pc

The one case split on the thread machine's state, `state_role`: a state with the role table's
invariant is in exactly one role (`RoleAt`, one constructor per role with the role's state,
reference invariant, warp facts and pc range). Every `<role>_state` below (a state at a pc of the
role's region is the role's, with its event's shape) is a corollary by pc arithmetic, and every
`<role>_at` (the same for a trace event, at the thread's prefix counts) one more step. The
progress rows (`Common/Export.lean`) and the roles' trace-level exports import this file
privately. A role lane adds its role by one `RoleAt` constructor, one `state_role` case and its
two corollaries.

`ev_at` and `next_at` take the state behind a trace event and behind a next event, with the
event's pc. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

theorem idle_pc_ge (s : IdleSite) : 2596 ≤ s.pc := by cases s <;> decide

/-- The MMA warp's sites but its hand-backs are in its code (pcs 1853–2160) or its exit. -/
theorem mma_pc (s : Mma.Site) (hl : ∀ i, s ≠ .leave i) :
    (1853 ≤ s.pc ∧ s.pc ≤ 2160) ∨ (s = .exit ∧ s.pc = 3611) := by
  cases s with
  | leave i => exact absurd rfl (hl i)
  | exit => exact .inr ⟨rfl, rfl⟩
  | qLoad k => refine .inl ?_; have := k.isLt; simp only [Mma.Site.pc]; omega
  | qCopy k => refine .inl ?_; have := k.isLt; simp only [Mma.Site.pc]; split_ifs <;> omega
  | qk k => refine .inl ?_; have := k.isLt; simp only [Mma.Site.pc]; split_ifs <;> omega
  | pv k => refine .inl ?_; have := k.isLt; simp only [Mma.Site.pc]; split_ifs <;> omega
  | _ => exact .inl (by decide)

/-- The TMA warp's sites but its hand-backs are in its code (pcs 2165–2330) or its exit. -/
theorem tma_pc (s : Tma.Site) (hl : ∀ i, s ≠ .leave i) :
    (2165 ≤ s.pc ∧ s.pc ≤ 2330) ∨ (s = .exit ∧ s.pc = 3611) := by
  cases s with
  | leave i => exact absurd rfl (hl i)
  | exit => exact .inr ⟨rfl, rfl⟩
  | coord0 k | coord1 k | coord2 k | coord3 k =>
    refine .inl ?_; have := k.isLt; simp only [Tma.Site.pc, Tma.coordPc]; split_ifs <;> omega
  | gather k => refine .inl ?_; have := k.isLt; simp only [Tma.Site.pc]; split_ifs <;> omega
  | _ => exact .inl (by decide)

/-- Warpgroup 2's sites are in its code (pcs 2606–3610) or its exit. -/
theorem dequant_pc (s : Dequant.Site) :
    (2606 ≤ s.pc ∧ s.pc ≤ 3610) ∨ (s = .exit ∧ s.pc = 3611) := by
  by_cases hx : s = .exit
  · subst hx
    exact .inr ⟨rfl, rfl⟩
  · have := Dequant.Site.pc_lt s hx
    have := (Dequant.Site.pc_range s).1
    exact .inl ⟨by omega, by omega⟩

/-- Warpgroup 0's sites are in its code (pcs 103–1841) or its exit. -/
theorem wg0_pc (s : Wg0.Site) : (103 ≤ s.pc ∧ s.pc ≤ 1841) ∨ (s = .exit ∧ s.pc = 3611) := by
  cases s with
  | sld a k => refine .inl ?_; revert a k; decide
  | pst k | pld k => refine .inl ?_; revert k; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => refine .inl ?_; revert c; decide
  | ost2 c k => refine .inl ?_; revert c k; decide
  | exit => exact .inr ⟨rfl, rfl⟩
  | _ => exact .inl ⟨by decide, by decide⟩

/-- The startup's states are at pc 97 or below. -/
theorem startup_pc {d : (startupCode P L g).D} {n : Cls → Nat}
    (hi : (thread P L g).inv (.inl d, n)) : (thread P L g).pc (.inl d, n) ≤ 97 := by
  have hx : Startup.exitOf d = none := by
    have := hi.2
    simpa [Code.gatedExit, startupEnter] using this
  exact Startup.Site.pc_le d.site fun r hr => by simp [Startup.exitOf, hr] at hx

/-- An MMA state with the invariant is no hand-back. -/
theorem mma_leave {d : (mmaCode P L g).D} {n : Cls → Nat}
    (hJ : (table P L).J g (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n))
    (hi : (thread P L g).inv (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)) :
    ∀ i, d.site ≠ .leave i := by
  intro i hdi
  obtain ⟨-, ⟨-, -, -, hlv⟩, -, -⟩ := hJ
  have hb := hi.2
  simp [subBack, hdi, hlv i hdi] at hb

/-- A TMA state with the invariant is no hand-back. -/
private theorem tma_leave {d : (tmaCode P L g).D} {n : Cls → Nat}
    (hJ : (table P L).J g (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n))
    (hi : (thread P L g).inv (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)) :
    ∀ i, d.site ≠ .leave i := fun i hdi => by
  obtain ⟨-, ⟨-, -, -, hlv⟩, -, -⟩ := hJ
  simpa [subBack, hdi, hlv i hdi] using hi.2


/-- The index warp's sites are in its code (pcs 2332–2586) or its exit. -/
theorem index_pc (s : IxSite) : (2332 ≤ s.pc ∧ s.pc < 2587) ∨ (s = .exit ∧ s.pc = 3611) := by
  cases s <;> decide

/-- A lane of warpgroup `w` is in warps `4 w` to `4 w + 3`. -/
private theorem warp_of_wg {w : Nat} (h : wgOf L g = w) :
    4 * w ≤ warp L g ∧ warp L g < 4 * w + 4 := by
  simp only [wgOf, tidOf] at h
  simp only [warp]
  omega

/-- An idle site is before the `ret` at pcs 2596–2605, or the `ret`. -/
private theorem idle_range (s : IdleSite) :
    (2596 ≤ s.pc ∧ s.pc < 2606) ∨ s.pc = 3611 := by
  cases s <;> decide

/-- **The role of a state at pc `pc`**, one constructor per role of the thread machine, each with
the role's state, its reference invariant at the state's counts, the lane's warp facts and the
role's pc range (the final `ret`, pc 3611, is each role's exit). The role's shape table is the
table's (`(table P L).Ev g σ e` unfolds to it once `σ` is the constructor's state). A role lane
adds its role by adding one constructor here and one case to `state_role`. -/
inductive RoleAt (P : Params) (L : Launch) (g : Nat) (pc : Nat) : (thread P L g).D → Prop
  | startup (d : (startupCode P L g).D) (n : Cls → Nat)
      (hR : Startup.Ref d (n .mbInit) (n .bar0)) (hW : Startup.RefW L g d (n .shfl))
      (hx : Startup.exitOf d = none) (hpc : pc = d.site.pc) (hr : pc ≤ 97) :
      RoleAt P L g pc (.inl d, n)
  | head (s : Wg1.Site) (n : Cls → Nat) (hs : s = .smr ∨ s = .hsh)
      (hpc : pc = Wg1.Site.pc P L g s) (hr : pc = 1842 ∨ pc = 1843) (hg : wgOf L g = 1)
      (hw : 4 ≤ warp L g ∧ warp L g < 8) :
      RoleAt P L g pc (.inr ⟨.inl .wg1, .inl s⟩, n)
  | idle (s : IdleSite) (n : Cls → Nat) (hpc : pc = s.pc)
      (hw : 4 ≤ warpOf L g ∧ warpOf L g < 7) (hr : (2596 ≤ pc ∧ pc < 2606) ∨ pc = 3611)
      (hret : s = .ret → pc = 3611) :
      RoleAt P L g pc (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, s⟩⟩, n)
  | index (d : (indexCode P L g).D) (n : Cls → Nat)
      (hR : n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) (hw : warp L g = 7)
      (hpc : pc = d.site.pc) (hr : (2332 ≤ pc ∧ pc < 2587) ∨ (d.site = .exit ∧ pc = 3611)) :
      RoleAt P L g pc (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)
  | mma (d : (mmaCode P L g).D) (n : Cls → Nat)
      (hR : n .ub = 0 → Mma.Ref L g d (fun c => n (.mma c)))
      (hok : Mma.SiteOk P L g d) (hl : ∀ i, d.site ≠ .leave i) (hw : warp L g = 4)
      (hpc : pc = d.site.pc)
      (hr : (1853 ≤ pc ∧ pc ≤ 2160) ∨ (d.site = .exit ∧ pc = 3611)) :
      RoleAt P L g pc (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)
  | tma (d : (tmaCode P L g).D) (n : Cls → Nat)
      (hR : n .ub = 0 → Tma.Ref L g d (fun c => n (.tma c)))
      (hok : Tma.SiteOk P L g d) (hl : ∀ i, d.site ≠ .leave i) (hw : warp L g = 5)
      (hpc : pc = d.site.pc)
      (hr : (2165 ≤ pc ∧ pc ≤ 2330) ∨ (d.site = .exit ∧ pc = 3611)) :
      RoleAt P L g pc (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)
  | dequant (d : (dequantCode P L g (warpW L g)).D) (n : Cls → Nat)
      (hR : n .ub = 0 → Dequant.Ref L g d (fun c => n (.dequant c)))
      (hw : 8 ≤ warp L g ∧ warp L g < 12)
      (hpc : pc = d.site.pc) (hr : (2606 ≤ pc ∧ pc ≤ 3610) ∨ (d.site = .exit ∧ pc = 3611)) :
      RoleAt P L g pc (.inr ⟨.inl .dequant, d⟩, n)
  | wg0 (d : (wg0Code P L g (warpW L g)).D) (n : Cls → Nat)
      (hR : n .ub = 0 → Wg0.Ref P L g d (fun c => n (.wg0 c))) (hw : warp L g < 4)
      (hpc : pc = Wg0.Site.pc (d : Wg0.Control.D).site)
      (hr : (103 ≤ pc ∧ pc ≤ 1841) ∨ ((d : Wg0.Control.D).site = .exit ∧ pc = 3611)) :
      RoleAt P L g pc (.inr ⟨.inl .wg0, d⟩, n)

/-- **The one case split on the thread machine's state**: a state with the role table's
invariant and the machine's is in exactly one role (`RoleAt`) at its pc. -/
theorem state_role {σ : (thread P L g).D} (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) : RoleAt P L g ((thread P L g).pc σ) σ := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d'⟩
  · have hx : Startup.exitOf d = none := by
      have := hi.2
      simpa [Code.gatedExit, startupEnter] using this
    obtain ⟨hR, hW, -⟩ := hJ
    exact .startup d n hR hW hx rfl (startup_pc hi)
  · cases i with
    | wg0 =>
      obtain ⟨-, ⟨hR, -⟩, -, hg⟩ := hJ
      have := warp_of_wg (w := 0) hg
      exact .wg0 d' n hR (by omega) rfl (wg0_pc _)
    | dequant =>
      obtain ⟨-, hR, -, hg⟩ := hJ
      have := warp_of_wg (w := 2) hg
      exact .dequant d' n hR ⟨by omega, by omega⟩ rfl (dequant_pc _)
    | wg1 =>
      have hJ' := hJ
      obtain ⟨-, hW, -, hg⟩ := hJ
      have := warp_of_wg (w := 1) hg
      rcases d' with s | ⟨j | r, d⟩
      · have hx := hi.2
        cases s with
        | smr => exact .head .smr n (.inl rfl) rfl (.inl rfl) hg ⟨by omega, by omega⟩
        | hsh => exact .head .hsh n (.inr rfl) rfl (.inr rfl) hg ⟨by omega, by omega⟩
        | _ => simp [Code.gatedExit, wg1Enter, Wg1.exitOf] at hx
      · cases j with
        | mma =>
          obtain ⟨-, hsub, ⟨hR, hok⟩, -⟩ := hW
          simp only [subOk, beq_iff_eq] at hsub
          have hl := mma_leave hJ' hi
          exact .mma d n hR hok hl hsub rfl (mma_pc d.site hl)
        | tma =>
          obtain ⟨-, hsub, ⟨hR, hok⟩, -⟩ := hW
          simp only [subOk, beq_iff_eq] at hsub
          have hl := tma_leave hJ' hi
          exact .tma d n hR hok hl hsub rfl (tma_pc d.site hl)
        | index =>
          obtain ⟨-, hsub, hR⟩ := hW
          simp only [subOk, beq_iff_eq] at hsub
          exact .index d n hR hsub rfl (index_pc d.site)
        | idle =>
          obtain ⟨-, hsub⟩ := hW
          simp only [subOk, Bool.and_eq_true, decide_eq_true_eq] at hsub
          exact .idle d n rfl hsub (idle_range d) fun h => by subst h; rfl
      · exact hW.elim
  · exact hJ.elim

/-- **A state by its pc**: in the code of the role whose lane condition the thread meets, or at
the final `ret`. -/
theorem place_state (_hp : Pre P L m) {σ : (thread P L g).D} (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) :
    StartupAt ((thread P L g).pc σ) ∨ Wg0At L g ((thread P L g).pc σ) ∨
      Wg1At L g ((thread P L g).pc σ) ∨ MmaAt L g ((thread P L g).pc σ) ∨
      TmaAt L g ((thread P L g).pc σ) ∨ IndexAt L g ((thread P L g).pc σ) ∨
      DequantAt L g ((thread P L g).pc σ) ∨
      (thread P L g).pc σ = 3611 := by
  have hw : warp L g = warpOf L g := rfl
  have h := state_role hJ hi
  generalize (thread P L g).pc σ = q at h ⊢
  simp only [StartupAt, Wg0At, Wg1At, MmaAt, TmaAt, IndexAt, DequantAt]
  cases h <;> omega

/-- **The state behind a trace event, at the event's pc.** -/
theorem ev_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ) ∧ (table P L).J g σ ∧
      (thread P L g).inv σ ∧ (table P L).Ev g σ e ∧ e.pc = (thread P L g).pc σ := by
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_state hp hX hFw he hub
  exact ⟨σ, hσ, hJ, hi, hev,
    Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub⟩

/-- The role's counts of a trace state are the thread's prefix counts. -/
private theorem counts {α : Type} {s} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (s, n))) (f : α → Cls) :
    (fun c => n (f c)) = fun c => ((X.tr g).take k).countP (cls (f c)) :=
  funext fun c => state_count hσ (f c)

/-- **A state at a pc below 103** is a startup state, not an exit, with its event's shape. -/
theorem startup_state {σ : (thread P L g).D} (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : e.pc < 103) :
    ∃ d n, σ = (.inl d, n) ∧ Startup.Ref d (n .mbInit) (n .bar0) ∧
      Startup.RefW L g d (n .shfl) ∧ Startup.Ev L g d e ∧ Startup.exitOf d = none ∧
      e.pc = d.site.pc := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | startup d n hR hW hx hpc' _ => exact ⟨d, n, rfl, hR, hW, hev, hx, hpc'⟩
  | _ => exfalso; omega

/-- **A trace event below pc 103 is the startup's**: fired from a startup state with the
startup's invariants at the thread's prefix counts, which hold no barrier-0 event. -/
theorem startup_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc : e.pc < 103) :
    ∃ d, Startup.Ref d (((X.tr g).take k).countP (cls .mbInit)) 0 ∧
      Startup.RefW L g d (((X.tr g).take k).countP (cls .shfl)) ∧ Startup.Ev L g d e ∧
      Startup.exitOf d = none ∧ ((X.tr g).take k).countP (cls .bar0) = 0 ∧
      e.pc = d.site.pc := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hW, hE, hx, hpd⟩ := startup_state hJ hi hev hpc' hpc
  have hc : ∀ c, n c = ((X.tr g).take k).countP (cls c) := state_count hσ
  rw [hc, hc] at hR
  rw [hc] at hW
  have h0 : ((X.tr g).take k).countP (cls .bar0) = 0 := by
    obtain ⟨site, x1, x2⟩ := d
    cases site <;> simp only [Startup.Ref] at hR <;> first | exact hR.2 |
      simp [Startup.exitOf] at hx
  rw [h0] at hR
  exact ⟨d, hR, hW, hE, hx, h0, hpd⟩

/-- **A state at a pc of warpgroup 1's head or idle code** is a head state before the dispatch
or an idle state before the `ret`, and its event has the site's shape. -/
theorem wg1_state {σ : (thread P L g).D} (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : (1842 ≤ e.pc ∧ e.pc < 1850) ∨ (2587 ≤ e.pc ∧ e.pc < 2606)) :
    (∃ s, (s = .smr ∨ s = .hsh) ∧ Wg1.Ev L g s e ∧ e.pc = Wg1.Site.pc P L g s ∧
        wgOf L g = 1) ∨
      (∃ s : IdleSite, s ≠ .ret ∧ Wg1.IEv s e ∧ e.pc = s.pc ∧ 4 ≤ warpOf L g ∧
        warpOf L g < 7) := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | head s n hs hpc' _ hg _ => exact .inl ⟨s, hs, hev, hpc', hg⟩
  | idle s n hpc' hw _ hret =>
    exact .inr ⟨s, fun h => absurd (hret h) (by omega), hev, hpc', hw.1, hw.2⟩
  | _ => exfalso; omega

/-- **A state at a pc of warpgroup 0's code** (pcs 103–1841) is a warpgroup-0 state of a lane of
warps 0–3, with the role's reference invariant at its counts and its event's shape. -/
theorem wg0_state {σ : (thread P L g).D} (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : 103 ≤ e.pc ∧ e.pc < 1842) :
    ∃ d n, σ = (.inr ⟨.inl .wg0, d⟩, n) ∧ (n .ub = 0 → Wg0.Ref P L g d (fun c => n (.wg0 c))) ∧
      Wg0.Ev P L g (warpW L g) d e ∧ warp L g < 4 := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | wg0 d n hR hw _ _ => exact ⟨d, n, rfl, hR, hev, hw⟩
  | _ => exfalso; omega

/-- **A state at a pc of the MMA code** (pcs 1850–2161) is an MMA state, not a hand-back, of a
lane of warp 4, with the role's reference invariant at its counts and its event's shape. -/
theorem mma_state {σ : (thread P L g).D} (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : 1850 ≤ e.pc ∧ e.pc < 2162) :
    ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n) ∧
      (n .ub = 0 → Mma.Ref L g d (fun c => n (.mma c))) ∧ Mma.Ev L g d e ∧
      (∀ i, d.site ≠ .leave i) ∧
      warp L g = 4 := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | mma d n hR _ hl hw _ _ => exact ⟨d, n, rfl, hR, hev, hl, hw⟩
  | _ => exfalso; omega

/-- **A state at a pc of the TMA code** (pcs 2162–2331) is a TMA state, not a hand-back, of a
lane of warp 5, with the role's reference invariant at its counts, its launch facts and its
event's shape. -/
theorem tma_state {σ : (thread P L g).D} (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : 2162 ≤ e.pc ∧ e.pc < 2332) :
    ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n) ∧
      (n .ub = 0 → Tma.Ref L g d (fun c => n (.tma c))) ∧ Tma.SiteOk P L g d ∧ Tma.Ev L g d e ∧
      (∀ i, d.site ≠ .leave i) ∧ warp L g = 5 := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | tma d n hR hok hl hw _ _ => exact ⟨d, n, rfl, hR, hok, hev, hl, hw⟩
  | _ => exfalso; omega

/-- **A state at a pc of the index code** (pcs 2332–2586) is an index state of a lane of warp 7,
with the role's reference invariant at its counts and its event's shape. -/
theorem index_state {σ : (thread P L g).D} (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : 2332 ≤ e.pc ∧ e.pc < 2587) :
    ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n) ∧
      (n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) ∧ Index.Ev P L g d e ∧
      warp L g = 7 := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | index d n hR hw _ _ => exact ⟨d, n, rfl, hR, hev, hw⟩
  | _ => exfalso; omega

/-- **A state at a pc of warpgroup 2's code** (pcs 2606–3610) is a warpgroup-2 state of a lane of
warps 8–11, with the role's reference invariant at its counts and its event's shape. -/
theorem dequant_state {σ : (thread P L g).D} (_hp : Pre P L m) (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hr : 2606 ≤ e.pc ∧ e.pc < 3611) :
    ∃ d n, σ = (.inr ⟨.inl .dequant, d⟩, n) ∧
      (n .ub = 0 → Dequant.Ref L g d (fun c => n (.dequant c))) ∧
      Dequant.Ev L g d e ∧ 8 ≤ warp L g ∧ warp L g < 12 := by
  have h := state_role hJ hi
  rw [← hpc] at h
  cases h with
  | dequant d n hR hw _ _ => exact ⟨d, n, rfl, hR, hev, hw.1, hw.2⟩
  | _ => exfalso; omega

/-- **A trace event at a pc of warpgroup 0's code** is fired from a warpgroup-0 state whose
reference invariant holds at the thread's prefix counts. -/
theorem wg0_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 103 ≤ e.pc ∧ e.pc < 1842) :
    ∃ d : (wg0Code P L g (warpW L g)).D,
      Wg0.Ref P L g d (fun c => ((X.tr g).take k).countP (Wg0.cls c)) ∧
      Wg0.Ev P L g (warpW L g) d e ∧ warp L g < 4 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := wg0_state hJ hi hev hpc hr
  have hR := hR (state_ub hX hσ he)
  rw [counts hσ Cls.wg0] at hR
  exact ⟨d, hR, hE, hw⟩

/-- **A trace event at a pc of the MMA code** is fired from an MMA state whose reference invariant
holds at the thread's prefix counts. -/
theorem mma_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 1850 ≤ e.pc ∧ e.pc < 2162) :
    ∃ d, Mma.Ref L g d (fun c => ((X.tr g).take k).countP (Mma.cls c)) ∧ Mma.Ev L g d e ∧
      (∀ i, d.site ≠ .leave i) ∧ warp L g = 4 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hE, hl, hw⟩ := mma_state hJ hi hev hpc hr
  have hR := hR (state_ub hX hσ he)
  rw [counts hσ Cls.mma] at hR
  exact ⟨d, hR, hE, hl, hw⟩

/-- **A trace event at a pc of the TMA code** is fired from a TMA state whose reference invariant
holds at the thread's prefix counts. -/
theorem tma_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 2162 ≤ e.pc ∧ e.pc < 2332) :
    ∃ d, Tma.Ref L g d (fun c => ((X.tr g).take k).countP (Tma.cls c)) ∧
      Tma.SiteOk P L g d ∧ Tma.Ev L g d e ∧ (∀ i, d.site ≠ .leave i) ∧ warp L g = 5 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hok, hE, hl, hw⟩ := tma_state hJ hi hev hpc hr
  have hR := hR (state_ub hX hσ he)
  rw [counts hσ Cls.tma] at hR
  exact ⟨d, hR, hok, hE, hl, hw⟩

/-- **A trace event at a pc of the index code** is fired from an index state whose reference
invariant holds at the thread's prefix counts. -/
theorem index_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 2332 ≤ e.pc ∧ e.pc < 2587) :
    ∃ d, Index.Ref P L g d (fun c => ((X.tr g).take k).countP (Index.cls c)) ∧
      Index.Ev P L g d e ∧ warp L g = 7 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := index_state hJ hi hev hpc hr
  have hR := hR (state_ub hX hσ he)
  rw [counts hσ Cls.index] at hR
  exact ⟨d, hR, hE, hw⟩

/-- **A trace event at a pc of warpgroup 2's code** is fired from a warpgroup-2 state whose
reference invariant holds at the thread's prefix counts. -/
theorem dequant_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 2606 ≤ e.pc ∧ e.pc < 3611) :
    ∃ d, Dequant.Ref L g d (fun c => ((X.tr g).take k).countP (Dequant.cls c)) ∧
      Dequant.Ev L g d e ∧ 8 ≤ warp L g ∧ warp L g < 12 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := dequant_state hp hJ hi hev hpc hr
  have hR := hR (state_ub hX hσ he)
  rw [counts hσ Cls.dequant] at hR
  exact ⟨d, hR, hE, hw⟩

/-- **The MMA state behind a next event** at a pc of the MMA code, with the role's reference
invariant at the trace's counts, which hold no undefined behaviour. -/
theorem next_mma (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 1850 ≤ e.pc ∧ e.pc < 2162) :
    ∃ d, Mma.Ref L g d (fun c => (X.tr g).countP (Mma.cls c)) ∧ Mma.Ev L g d e ∧
      (∀ i, d.site ≠ .leave i) ∧ (X.tr g).countP (Mma.cls .ub) = 0 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, hE, hl, -⟩ := mma_state hJ hi hev hpc hr
  have hR := hR (by
    obtain ⟨Y, hY, hpre, he⟩ := hn
    have hσY : Frame.stateAt (thread P L) Y g (X.tr g).length = some (some (_, n)) :=
      (Sched.stateAt_congr (by rw [hpre, List.take_length])).trans hσ
    exact state_ub hY hσY he)
  have hc : (fun c => n (.mma c)) = fun c => (X.tr g).countP (Mma.cls c) :=
    funext fun c => (state_count hσ (.mma c)).trans (by rw [List.take_length]; rfl)
  rw [hc] at hR
  refine ⟨d, hR, hE, hl, List.countP_eq_zero.mpr fun f hf hcl => ?_⟩
  obtain ⟨Y, hY, hpre, he⟩ := hn
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf
  have hYj : Y.get (g, j) = some f := by
    show (Y.tr g)[j]? = some f
    rw [← List.getElem?_take_of_lt hj, hpre, List.getElem?_eq_getElem hj, hfj]
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl =>
    have := ub_last hY hYj he
    omega
  | wait l q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hcl
  | tc t => cases t <;> simp [Mma.cls, Mma.kindOf] at hcl
  | _ => simp [Mma.cls, Mma.kindOf] at hcl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
