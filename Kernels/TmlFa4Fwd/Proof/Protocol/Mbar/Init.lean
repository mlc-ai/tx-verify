-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Kernel.Source.Warp
public import Lemmas.Protocol.NamedBarSources
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Lemmas.Kernel.ElectSource
import Lemmas.Kernel.Safety.Init
import Lemmas.Kernel.UbLast
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

import Lemmas.Kernel.Safety.InitU

@[expose] public section

/-! # ERR-MBAR-UNINITIALIZED on the role table

`noUninit`: every event that names an mbarrier and is no initialization of it has an
initialization of the object published to it, by `RoleTable.noMbarUninit` on the thread machine's
role table (`table`). Per use:

* **The object** is one of the 34 the startup of the lane's CTA initializes, and the use is fired
  from a role state (`use_obj`).
* **The use follows the CTA barrier** (`role_bar0`): the lane's trace before the use has an event
  on barrier 0.
* **The initialization exists before the elected lane's barrier** (`init_exists`). The lane's first
  barrier-0 event is passed, so every lane of the CTA arrives on it (`member_arrival_any`). Lane 0
  of warp 0 walks the startup's path to its first election (`lead_path`) and learns the leader `ld`
  of warp 0's elections; lane `ld` arrives too, every one of its elections returns `ld`
  (`elect_leader`), so it walks the whole path (three shuffles, each election and its block of
  initializations, the fence, the barrier) and initializes every object before its barrier
  (`init_ev`).
* **The publication** is the CTA barrier's hand-off (`Handoff.of_bar_upTo` with one instance):
  the initialization's barrier count is `0`, the use's is positive. Barrier 0 is the startup's
  alone: every other `bar` of the shape tables names barrier 2, 11, 12 or a register word that is
  never `0` (`bar0_ev`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Barrier 0 is the startup's -/

theorem corr_nbW_ne (k : Fin 2) : (Correction.nbW L g k).toNat ≠ 0 := by
  fin_cases k
  · exact corr_nb_ne (L := L) (g := g) 0
  · exact corr_nb_ne (L := L) (g := g) 1

theorem soft_nbW_word : ∀ w < 16,
    (Epilogue.addi (Epilogue.add32 (Epilogue.sub32 (BitVec.ofNat 64 w)
      (Epilogue.andi (Epilogue.add32 (BitVec.ofNat 64 w)
        (Epilogue.shru (Epilogue.shrs (BitVec.ofNat 64 w) 31) 30)) (-4)))
      (Epilogue.sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3) (Epilogue.i32 4)
        (Epilogue.i32 0))) 3).toNat ≠ 0 := by
  decide

theorem soft_nbW_ne (hp : Pre p L m) : (Softmax.nbW L g).toNat ≠ 0 := by
  have h : g % L.block / 32 < 16 := by rw [hp.block]; omega
  exact soft_nbW_word _ h

/-- The output warp names no barrier. -/
theorem epi_nobar {d : Epilogue.D} {e : Event} (hev : Epilogue.Ev p L g d e) (id : Nat)
    (cnt : Option Nat) (mode : BarMode) : e.kind ≠ .bar id cnt mode := by
  intro hk
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  unfold Epilogue.Ev at hev
  split at hev <;> simp_all [Epilogue.isStore]

set_option maxHeartbeats 8000000 in
/-- **Every barrier-0 event of the shape tables is the startup's `bar.sync 0`.** -/
theorem bar0_ev (hp : Pre p L m) {σ : (thread p L g).D} {e : Event} {cnt : Option Nat}
    {mode : BarMode} (hJ : JR p L g σ) (hi : (thread p L g).inv σ) (hev : TEv p L g σ e)
    (hk : e.kind = .bar 0 cnt mode) : cnt = none ∧ mode = .sync := by
  obtain ⟨σ1, n⟩ := σ
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  have h1 : ∀ k, 0 ≠ (Correction.nbW L g k).toNat := fun k => (corr_nbW_ne k).symm
  have h3 : 0 ≠ (Softmax.nbW L g).toNat := (soft_nbW_ne (L := L) (g := g) hp).symm
  have h4 : (0 : Nat) ≠ (if Softmax.stg L g = true then 12 else 11) := by split <;> decide
  rcases σ1 with s | ⟨i, d⟩
  · obtain ⟨site, x1, x2, x3⟩ := s
    simp only [TEv] at hev
    cases site <;> try simp_all [Startup.Ev, exit]
    rename_i j
    fin_cases j <;> simp_all
  cases i with
  | epilogue =>
    simp only [TEv] at hev
    unfold Epilogue.Ev at hev
    split at hev <;> simp_all [Epilogue.isStore]
  | correction =>
    rcases hev.1.data_or_vote with hev | ⟨_,_,h⟩
    case inr => cases h
    unfold Correction.Ev at hev
    split at hev <;> first
      | exact (epi_nobar hev 0 cnt mode rfl).elim
      | exact (h1 _ (Kind.bar.inj hev).1).elim
      | simp_all [Correction.rdOrUb]
  | softmax =>
    have hev := hev.1
    unfold Softmax.Ev at hev
    split at hev <;> first
      | exact (epi_nobar hev 0 cnt mode rfl).elim
      | exact (h3 (Kind.bar.inj hev).1).elim
      | exact (h4 (Kind.bar.inj hev).1).elim
      | simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]
  | loader b =>
    simp only [TEv] at hev
    unfold Loader.Ev at hev
    split at hev <;> first
      | exact (epi_nobar hev 0 cnt mode rfl).elim
      | simp_all
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · simp only [TEv, Mma.PreEv] at hev
      simp_all
    · simp only [TEv] at hev
      unfold Mma.Ev at hev
      split at hev <;> first
        | exact (epi_nobar hev 0 cnt mode rfl).elim
        | simp_all
  | stub r =>
    exact (jr_stub hJ).elim

/-! ### Events on barrier 0 -/

section table
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hT : (table p L).ShapeOkU (· < L.threads)) (hF : (table p L).Followed X (· < L.threads))
include hp hX hT hF

/-- An event that is no undefined behaviour is fired from a followed state with the table's
shape. -/
theorem ev_at {h i : Nat} {e : Event} (he : X.get (h, i) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ, Frame.stateAt (thread p L) X h i = some (some σ) ∧ JR p L h σ ∧
      (thread p L h).inv σ ∧ TEv p L h σ e :=
  Frame.RoleTable.ev_of_ne_ubU (T := table p L) (fun _ hg => thread_sound hp hg) hX hT hF
    (Frame.lt_of_get hX he) he hub

/-- **Every barrier-0 event is a `bar.sync 0` over the whole CTA.** -/
theorem bar0_of {h i pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (h, i) = some ⟨pc, .bar 0 cnt mode⟩) : cnt = none ∧ mode = .sync := by
  obtain ⟨σ, -, hJ, hi, hev⟩ := ev_at hp hX hT hF he (by intro f hf; cases hf)
  exact bar0_ev hp hJ hi hev rfl

/-- A thread's return follows its CTA barrier. -/
theorem exit_bar0 {h j pc : Nat} (he : X.get (h, j) = some ⟨pc, .exit⟩) :
    0 < ((X.tr h).take j).countP (Execution.isBarId 0) := by
  obtain ⟨⟨σ1, n⟩, hσ, -, hi, hev⟩ := ev_at hp hX hT hF he (by intro f hf; cases hf)
  rcases σ1 with s | ⟨r, d⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    simp only [TEv] at hev
    have hx := hi.2
    cases site <;> simp_all [Startup.Ev, exit]
    rename_i j
    fin_cases j <;> simp_all
  · exact role_bar0 hp hX j hσ

/-- **The first barrier-0 event** of a thread with one before position `K`. -/
theorem first_bar0 {h K : Nat} (hpos : 0 < ((X.tr h).take K).countP (Execution.isBarId 0)) :
    ∃ i < K, ∃ pc mode, X.get (h, i) = some ⟨pc, .bar 0 none mode⟩ ∧
      ((X.tr h).take i).countP (Execution.isBarId 0) = 0 := by
  obtain ⟨j, ev, hj, hP, hc⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 0)
    (c := 0) (by omega : 0 + 1 ≤ ((X.tr h).take K).countP (Execution.isBarId 0))
  have hjK : j < K := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjK.le] at hc
  have hget : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take_of_lt hjK]
  obtain ⟨pc, kind⟩ := ev
  cases kind <;> simp [Execution.isBarId] at hP
  rename_i id cnt mode
  subst hP
  obtain ⟨rfl, -⟩ := bar0_of hp hX hT hF hget
  exact ⟨j, hjK, pc, mode, hget, hc⟩

/-- **Barrier 0's arrivals**: every one is a lane of the CTA's sixteen warps passing no count. -/
theorem srcs0 : NamedBar.Sources L X none (Finset.range 16) 0 := by
  rintro ⟨h, i⟩ pc cnt ⟨mode, he⟩ hh
  refine ⟨?_, (bar0_of hp hX hT hF he).1⟩
  simp only [Finset.mem_range]
  rw [hp.block]
  omega

end table

/-- Barrier 0's group: the CTA's sixteen warps. -/
theorem shape0 (hp : Pre p L m) : NamedBar.Shape L none (Finset.range 16) 0 where
  pos := by simp
  target := by rw [hp.block]; rfl
  bound := by intro w hw; rw [hp.block]; simp at hw; omega
  id_lt := by decide

/-! ### The initializations exist before the elected lane's barrier -/

theorem path_lt3 : ∀ j < 3, ∀ jj, pathSite.getD j .bar ≠ .elect jj := by decide

/-- An event of a startup state on barrier 0 is fired at the barrier site or an entry. -/
theorem start_bar {s : Startup.D} {e : Event} {id : Nat} {cnt : Option Nat} {mode : BarMode}
    (hev : Startup.Ev L g s e) (hk : e.kind = .bar id cnt mode) :
    s.site = .bar ∨ ∃ r, s.site = .enter r := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases site with
  | bar => exact .inl rfl
  | enter r => exact .inr ⟨r, rfl⟩
  | sh j => fin_cases j <;> simp [Startup.Ev] at hev
  | _ => simp [Startup.Ev] at hev

section table
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hT : (table p L).ShapeOkU (· < L.threads)) (hF : (table p L).Followed X (· < L.threads))
include hp hX hT hF

omit hT hF in
/-- A lane of warp 0 on the path whose first barrier-0 event is at `i` has `54 ≤ i`: the path
reaches the barrier site only at position 54. -/
theorem path_bar_lt {ℓ i : Nat} {pc : Nat} {mode : BarMode}
    (hi : X.get (ℓ, i) = some ⟨pc, .bar 0 none mode⟩)
    (hst : ∃ s n, Frame.stateAt (thread p L) X ℓ i = some (some (.inl s, n)) ∧
      s.site = pathSite.getD i .bar ∧ StartAt0 L s n) : 54 ≤ i := by
  by_contra hlt
  obtain ⟨s, n, hσ, hs, hS⟩ := hst
  have hE := (start_fired hp hX hi hσ).1
  rcases start_bar hE rfl with hb | ⟨r, hr⟩
  · exact path_ne_bar i (by omega) (hs ▸ hb)
  · obtain ⟨site, x1, x2, x3⟩ := s
    simp only at hr
    subst hr
    simp [StartAt0] at hS

set_option maxHeartbeats 4000000 in
/-- **Every object of a lane's CTA is initialized before the elected lane's barrier**, once the
lane has passed its CTA barrier. -/
theorem init_exists {k : Nat} (hg : g < L.threads) (hk : k < (X.tr g).length)
    (hb : 0 < ((X.tr g).take k).countP (Execution.isBarId 0)) {o : Nat} (ho : ObjOff o) :
    ∃ i c, X.MbInit i (obj L g o) c ∧ i.1 / L.block = g / L.block ∧ i.1 < L.threads ∧
      i.1 % L.block / 32 = 0 ∧
      ((X.tr i.1).take (i.2 + 1)).countP (Execution.isBarId 0) = 0 := by
  have hblk := hp.block
  -- the lane's first barrier-0 event, which it passed
  obtain ⟨f, hfk, pcf, modef, hfe, hfc⟩ := first_bar0 hp hX hT hF hb
  have hmf := (bar0_of hp hX hT hF hfe).2
  subst hmf
  have hf : X.IsBarrier (g, f) 0 none pcf := hfe
  -- every lane of warp 0 of the CTA arrives on it
  have harr : ∀ y, y / L.block = g / L.block → y % L.block / 32 = 0 →
      ∃ i pc mode, X.get (y, i) = some ⟨pc, .bar 0 none mode⟩ ∧
        ((X.tr y).take i).countP (Execution.isBarId 0) = 0 := by
    intro y hy hw
    obtain ⟨i, pc, md, he, hc⟩ := NamedBar.Sources.member_arrival_any hX (srcs0 hp hX hT hF)
      (shape0 hp) hf (by simp only; omega) hy (by simp [hw])
      (fun ⟨j, pcx, hx⟩ => by
        obtain ⟨i, -, pc, md, he, hc⟩ := first_bar0 hp hX hT hF (exit_bar0 hp hX hT hF hx)
        exact ⟨i, pc, md, he, by simp only; rw [hc, hfc]⟩)
    exact ⟨i, pc, md, he, by simp only at hc; rw [hc, hfc]⟩
  have hcta : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).2 hg
  -- lane 0 of warp 0 learns the leader at its first election
  set y0 := g / L.block * L.block with hy0
  have hy0b : y0 / L.block = g / L.block := by
    rw [hy0]; simp [Nat.mul_div_cancel _ (by omega : 0 < L.block)]
  have hy0m : y0 % L.block = 0 := by rw [hy0]; simp
  have hy0t : y0 < L.threads := by
    have := Nat.div_mul_le_self g L.block; omega
  have hy0w : InWarp L 0 y0 := ⟨hy0t, by simp [Prologue.warpIndex, hy0m]⟩
  obtain ⟨i0, pc0, md0, he0, hc0⟩ := harr y0 hy0b (by simp [hy0m])
  have hlt3 : 3 < i0 := by
    by_contra h
    obtain ⟨s, n, hσ, hs, hS⟩ := lead_path hp hX hy0w (K := i0) (by omega) he0
      (by intro f hf; cases hf) hc0 (fun j hj ⟨jj, hjj⟩ => absurd hjj (path_lt3 j (by omega) jj))
      i0 le_rfl
    have := path_bar_lt hp hX he0 ⟨s, n, hσ, hs, hS⟩
    omega
  obtain ⟨e3, he3⟩ : ∃ e, X.get (y0, 3) = some e :=
    ⟨_, List.getElem?_eq_getElem (show 3 < (X.tr y0).length by
      have := (List.getElem?_eq_some_iff.mp (show (X.tr y0)[i0]? = _ from he0)).1; omega)⟩
  have hub3 : ∀ f, e3.kind ≠ .ub f := by
    intro f hf
    have := ub_last hX (show X.get (y0, 3) = some ⟨e3.pc, .ub f⟩ by rw [he3, ← hf]) he0
    omega
  have hc3 : ((X.tr y0).take 3).countP (Execution.isBarId 0) = 0 := by
    have := countP_take_mono' (Execution.isBarId 0) (X.tr y0) (show 3 ≤ i0 by omega)
    omega
  obtain ⟨s3, n3, hσ3, hs3, hS3⟩ := lead_path hp hX hy0w (K := 3) (by omega) he3 hub3 hc3
    (fun j hj ⟨jj, hjj⟩ => absurd hjj (path_lt3 j hj jj)) 3 le_rfl
  have hE3 := (start_fired hp hX he3 hσ3).1
  obtain ⟨site3, x1, x2, x3⟩ := s3
  simp only at hs3
  have hs3' : site3 = .elect 0 := hs3
  subst hs3'
  simp only [Startup.Ev] at hE3
  rcases hE3 with ⟨inst3, ld, -, hk3⟩ | ⟨f, hk3⟩
  swap; exact absurd hk3 (hub3 f)
  obtain ⟨pc3, kind3⟩ := e3
  simp only at hk3
  subst hk3
  have hld : ld < 32 := (hX.elect.1 _ _ _ _ _ he3).2.2.1
  -- the leader's lane walks the whole path
  set ℓ := y0 + ld with hℓdef
  have hℓm : ℓ % L.block = ld := by
    rw [hℓdef, hy0, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hℓb : ℓ / L.block = g / L.block := by
    rw [hℓdef, hy0, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < L.block),
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hℓt : ℓ < L.threads := by
    have h1 : (g / L.block + 1) * L.block ≤ L.grid * L.block :=
      Nat.mul_le_mul_right _ (by omega)
    show y0 + ld < L.grid * L.block
    rw [hy0]; rw [Nat.add_mul, Nat.one_mul] at h1; omega
  have hℓw : InWarp L 0 ℓ := ⟨hℓt, by simp [Prologue.warpIndex, hℓm]; omega⟩
  have hlane : laneOf L ℓ = ld := by simp [laneOf, hℓm]; omega
  obtain ⟨iℓ, pcℓ, mdℓ, heℓ, hcℓ⟩ := harr ℓ hℓb (by rw [hℓm]; omega)
  have hlead : ∀ K, ∀ j < K, (∃ jj, pathSite.getD j .bar = .elect jj) →
      ∀ pc inst ld', X.get (ℓ, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld'⟩ → ld' = laneOf L ℓ := by
    intro K j _ _ pc inst ld' he
    rw [hlane]
    exact (elect_leader hX he he3 ⟨⟨hℓt, hy0t, by rw [hℓb, hy0b]⟩, by
      rw [hℓm, hy0m]; omega⟩).trans rfl
  have hiℓ : 54 ≤ iℓ := by
    by_contra h
    exact absurd (path_bar_lt hp hX heℓ (lead_path hp hX hℓw (K := iℓ) (by omega) heℓ
      (by intro f hf; cases hf) hcℓ (hlead iℓ) iℓ le_rfl)) h
  obtain ⟨e54, he54⟩ : ∃ e, X.get (ℓ, 54) = some e :=
    ⟨_, List.getElem?_eq_getElem (show 54 < (X.tr ℓ).length by
      have := (List.getElem?_eq_some_iff.mp (show (X.tr ℓ)[iℓ]? = _ from heℓ)).1; omega)⟩
  have hub54 : ∀ f, e54.kind ≠ .ub f := by
    intro f hf
    by_cases h54 : iℓ = 54
    · subst h54; rw [heℓ] at he54; cases he54; cases hf
    · have := ub_last hX (show X.get (ℓ, 54) = some ⟨e54.pc, .ub f⟩ by rw [he54, ← hf]) heℓ
      omega
  have hc54 : ((X.tr ℓ).take 54).countP (Execution.isBarId 0) = 0 := by
    have := countP_take_mono' (Execution.isBarId 0) (X.tr ℓ) hiℓ
    omega
  have hpath := lead_path hp hX hℓw (K := 54) le_rfl he54 hub54 hc54 (hlead 54)
  -- the initialization of the object
  obtain ⟨q, rfl⟩ := objOff_init ho
  have hq := initPos_lt q
  obtain ⟨s, n, hσ, hs, hS⟩ := hpath (initPos q) hq.le
  rw [path_initPos] at hs
  obtain ⟨eq, heq⟩ : ∃ e, X.get (ℓ, initPos q) = some e :=
    ⟨_, List.getElem?_eq_getElem (show initPos q < (X.tr ℓ).length by
      have := (List.getElem?_eq_some_iff.mp (show (X.tr ℓ)[54]? = _ from he54)).1; omega)⟩
  have hubq : ∀ f, eq.kind ≠ .ub f := by
    intro f hf
    have := ub_last hX (show X.get (ℓ, initPos q) = some ⟨eq.pc, .ub f⟩ by rw [heq, ← hf]) he54
    omega
  obtain ⟨t, ins, o', hat, -, hc, hfi⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX heq hσ hubq
  have hx1 : s.x1 = BitVec.ofNat 64 L.sharedBase := (startAt0_of_mid (by rw [hs]; rfl) hS).2.1
  rcases init_ev hp hs hx1 hat hc hfi with ⟨c, hkq⟩ | ⟨f, hkq⟩
  swap; exact absurd hkq (hubq f)
  refine ⟨(ℓ, initPos q), c, ⟨eq.pc, ?_⟩, hℓb, hℓt, by rw [hℓm]; omega, ?_⟩
  · rw [heq, show obj L g (initOff q) = obj L ℓ (initOff q) by simp [obj, hℓb], ← hkq]
  · have := countP_take_mono' (Execution.isBarId 0) (X.tr ℓ) (show initPos q + 1 ≤ 54 by omega)
    simp only
    omega

end table

/-! ### ERR-MBAR-UNINITIALIZED -/

/-- **The startup's initialization of an object is published to every other use of it**: an
event of a lane, fired from a role state with its table's shape, that names an object and is no
initialization of it, has an initialization of the object by a lane of warp 0 of its CTA, before
that lane's CTA barrier, published to it by the CTA barrier's hand-off. -/
theorem use_pub (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {g k : Nat}
    {σ : (thread p L g).D} {e : Event} {l : Loc} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hJ : JR p L g σ)
    (hi : (thread p L g).inv σ) (hev : TEv p L g σ e) (hm : Frame.MbarOf e l)
    (hni : ∀ c, e.kind ≠ .mbInit l c) :
    ∃ j c, X.MbInit j l c ∧ InitPublished L X j (g, k) l ∧ j.1 / L.block = g / L.block ∧
      j.1 < L.threads ∧ j.1 % L.block / 32 = 0 := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have H := Frame.Handoff.of_bar_upTo hX (srcs0 hp hX hT hF) (shape0 hp) (syncs := fun _ => True)
    (fun h j pc cnt mode _ he => (bar0_of hp hX hT hF he).2) 1
    (fun g _ _ ⟨j, pc, hx⟩ => by
      have h1 := exit_bar0 hp hX hT hF hx
      have h2 := countP_take_mono' (Execution.isBarId 0) (X.tr g)
        (show j ≤ (X.tr g).length from (List.getElem?_eq_some_iff.mp
          (show (X.tr g)[j]? = _ from hx)).1.le)
      rw [List.take_length] at h2
      omega)
  obtain ⟨⟨r, hr⟩, o, ho, rfl⟩ := use_obj hp hX he hσ hJ hi hev hm hni
  obtain ⟨σ1, n⟩ := σ
  simp only at hr
  subst hr
  obtain ⟨i, d⟩ := r
  have hb := role_bar0 hp hX k hσ
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[k]? = _ from he)).1
  obtain ⟨j, c, hinit, hcta, hjt, hj0, hup⟩ := init_exists hp hX hT hF hg hk hb ho
  refine ⟨j, c, hinit, .inl (H j.1 g j.2 k ⟨⟨hjt, hg, hcta⟩, by simp [hj0], trivial⟩ hk ?_),
    hcta, hjt, hj0⟩
  simp only [hup]
  omega

/-- **ERR-MBAR-UNINITIALIZED**: every use of an mbarrier has an initialization of its object
published to it, by the CTA barrier's hand-off. -/
theorem noUninit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : ¬ MbarUninit L X := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  refine Frame.RoleTable.noMbarUninitU (T := table p L) (S := (· < L.threads))
    (fun _ hg => thread_sound hp hg) hX hT hF ?_ ?_
  · intro g k σ e l hg hσ hJ hi hev he hm hni
    obtain ⟨j, c, hinit, hpub, -⟩ := use_pub hp hX hFw hg he hσ hJ hi hev hm hni
    exact ⟨j, c, hinit, hpub⟩
  · intro i l hu hn _
    obtain ⟨e, he, -⟩ := Frame.usesMbar_mbarOf hu
    exact absurd (Frame.lt_of_get hX he) hn

end
end PTX.Kernels.TmlFa4Fwd.Proof
