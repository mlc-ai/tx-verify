-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep

@[expose] public section

/-! # The TMA warp's reference invariant is kept by every step

`ref_next`: from a state with `Ref`, an event of the state's shape that the machine follows leads
to a state with `Ref` for the bumped counts (an undefined-behaviour event bumps the class `ub`,
after which `Ref` asks nothing); `ref_init`: the first state has it with no event counted.
`siteOk_step`: every state the machine reaches has its launch facts (`SiteOk`). -/

/-! # The TMA warp's reference invariant across a step of the block loop

One declaration per loop site: the objects of the events are the block's slots (`LoopOk`: the
ring's slot word is `r % 4`, the tile's `r % 2`), the counts advance by `blk_*`; the block's end
(`ok_coordFree`) moves to block `r + 1` with its words (`block_end`) or to the CTA barrier, whose
step reaches the exit (`ok_outBar`). -/

/-! # The TMA warp's reference invariant across a prologue step

`StepOk P L g s`: from a state at site `s` with `RefCore`, an event of the site's kind that is not
undefined behaviour, at a pc of the role, leads to a state with `RefCore` for the bumped counts.
One declaration per prologue site; the successful poll of `bar_last_store_done` enters the block
loop (`ok_storeWait`, by `blocks_pos`) or, for a total below 64, the CTA barrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The step obligation of the reference invariant at site `s`. -/
def StepOk (P : Params) (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ (d d' : D) (n : Cnt → Nat) (e : Event), d.site = s → inRole e = true →
    (∀ f, e.kind ≠ .ub f) → RefCore L g d n → EvK L g d e → succ P L g d e = some (some d') →
    RefCore L g d' (Code.bump cls n e)

/-- A prologue site. -/
macro "pro_ok" : term => `((by refine ⟨rfl, ?_, ?_⟩ <;> simp))

/-- A state after the election's place: the exit, or a prologue site of place `1`. -/
theorem core_place1 {d : D} {m : Cnt → Nat}
    (hs : d.site = .exit ∨ ProSite d.site ∧ d.site.pro = 1)
    (hB : ∀ c, c ≠ .ub → m c = cntAt (objs L g) 1 0 0 0 0 false c) : RefCore L g d m := by
  rcases hs with hs | ⟨hs, h1⟩
  · unfold RefCore
    rw [hs]
    exact Or.inl hB
  · exact (core_pro hs).2 (h1 ▸ hB)

/-- The counts at place `1` after an event of no class at a site of place `1`. -/
theorem bump_place1 {d : D} {n : Cnt → Nat} {e : Event} (hpc : inRole e = true)
    (hk : kindOf e = none) (hd : ProSite d.site) (h1 : d.site.pro = 1) (hJ : RefCore L g d n) :
    ∀ c, c ≠ .ub → Code.bump cls n e c = cntAt (objs L g) 1 0 0 0 0 false c :=
  bump_kind hpc ((core_pro hd).1 hJ) fun c _ => by rw [hk, plus_none', h1]

theorem ok_elect : StepOk P L g .elect := by
  intro d d' n e hs hpc hu hJ hev hn
  simp only [EvK, hs] at hev
  obtain ⟨inst, ld, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .elect := by simp [kindOf, hk]
  have hd : ProSite d.site := by rw [hs]; exact pro_ok
  have hB := bump_kind (B := cntAt (objs L g) 1 0 0 0 0 false) hpc ((core_pro hd).1 hJ)
    fun c _ => by rw [hK, hs]; exact pro_elect c
  simp only [succ, hs, electNext, hk, Option.some.injEq] at hn
  subst hn
  refine core_place1 ?_ hB
  split_ifs
  · unfold leadNext afterTopk lensD
    split_ifs <;> first | exact .inl rfl | exact .inr ⟨pro_ok, rfl⟩
  · exact .inr ⟨pro_ok, rfl⟩

theorem ok_loadTopk : StepOk P L g .loadTopk := by
  intro d d' n e hs hpc hu hJ hev hn
  simp only [EvK, hs] at hev
  obtain ⟨a, bs, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hd : ProSite d.site := by rw [hs]; exact pro_ok
  have hB := bump_place1 hpc (by simp [kindOf, hk]) hd (by rw [hs]; rfl) hJ
  simp only [succ, hs] at hn
  obtain ⟨x, rfl⟩ := word_next hn
  refine core_place1 ?_ hB
  unfold afterTopk lensD
  split_ifs <;> exact .inr ⟨pro_ok, rfl⟩

theorem ok_loadExtra : StepOk P L g .loadExtra := by
  intro d d' n e hs hpc hu hJ hev hn
  simp only [EvK, hs] at hev
  obtain ⟨a, bs, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  have hd : ProSite d.site := by rw [hs]; exact pro_ok
  have hB := bump_place1 hpc (by simp [kindOf, hk]) hd (by rw [hs]; rfl) hJ
  simp only [succ, hs] at hn
  obtain ⟨x, rfl⟩ := word_next hn
  unfold lensD
  exact core_place1 (.inr ⟨pro_ok, rfl⟩) hB

theorem ok_qWait : StepOk P L g .qWait := by
  intro d d' n e hs hpc hu hJ hev hn
  simp only [EvK, Poll, hs] at hev
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  rw [← qUt_eq] at hk
  simp only [succ, hs] at hn
  have hd : ProSite d.site := by rw [hs]; exact pro_ok
  refine pro_wait hpc hk hd pro_ok hJ hn ?_
  rw [hs]
  exact pro_acqU

/-- **The loop's entry**: block `0` with its words, or the barrier for a total below 64. -/
theorem ok_storeWait : StepOk P L g .storeWait := by
  intro d d' n e hs hpc hu hJ hev hn
  simp only [EvK, Poll, hs] at hev
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  rw [← last_eq] at hk
  simp only [succ, hs] at hn
  have hd : ProSite d.site := by rw [hs]; exact pro_ok
  rw [poll_eq hk hn]
  cases ok
  · exact pro_to hpc (kindOf_poll hk) hd hd hJ fun c => by simp [plus_none']
  have hB := bump_kind (B := cntAt (objs L g) 3 0 0 0 0 false) hpc ((core_pro hd).1 hJ)
    fun c _ => by rw [kindOf_poll hk, hs]; exact pro_acqL c
  simp only [↓reduceIte]
  unfold loopEntry
  split_ifs with h
  · unfold RefCore
    simp only [rounds, h, ↓reduceIte]
    exact hB
  · have h' : scmpi .lt .s (tot d.l0 d.l1) 64 = false := by simpa using h
    obtain ⟨h1, h2, hneg⟩ := blocks_pos h'
    have h0 : (i32 0).toNat = 0 := by decide
    refine (core_loop rfl).2 ⟨⟨h', h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [h0, Nat.zero_mod, Nat.zero_div, Nat.add_zero]
    · omega
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact hneg
    · exact hB

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The loop words of a loop state. -/
theorem words_of {d : D} {n : Cnt → Nat} (hs : d.site.inLoop = true) (hJ : RefCore L g d n) :
    LoopOk d :=
  ((core_loop hs).1 hJ).1

/-- A read advances the block's reads. -/
theorem blk_rd_to {O : Objs} {r i i' rd rd' gs gs' : Nat} (hi : i' = i) (hrd : rd' = rd + 1)
    (hg : gs' = gs) :
    ∀ c, plus (cntAt O 3 r i rd gs false) (some .rd) c = cntAt O 3 r i' rd' gs' false c := by
  rw [hi, hrd, hg]; exact blk_rd r i rd gs

/-- A gather advances the block's gathers. -/
theorem blk_gather_to {O : Objs} {r i i' rd rd' gs gs' : Nat} (hi : i' = i) (hrd : rd' = rd)
    (hg : gs' = gs + 1) :
    ∀ c, plus (cntAt O 3 r i rd gs false) (some (.gather (O.raw (r % 2)))) c =
      cntAt O 3 r i' rd' gs' false c := by
  rw [hi, hrd, hg]; exact blk_gather r i rd gs

/-- The place after the last element of quadruple `k`. -/
theorem coord_places (k : Fin 16) : (afterCoord k).stage = 2 ∧
    (afterCoord k).rdN = 4 * k.val + 3 + 1 ∧ (afterCoord k).gN = k.val - 1 := by
  fin_cases k <;> decide

/-- The place after gather `k`. -/
theorem gather_places (k : Fin 16) : (afterGather k).stage = 2 ∧
    (afterGather k).rdN = (Site.gather k).rdN ∧ (afterGather k).gN = k.val + 1 := by
  fin_cases k <;> decide

theorem ok_coordWait : StepOk P L g .coordWait := by
  intro d d' n e hs hpc hu hJ hev hn
  have hd : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨-, -, -, -, -, -, hslot, -, -, -⟩ := words_of hd hJ
  simp only [EvK, Poll, hs] at hev
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  rw [ready_of hslot] at hk
  simp only [succ, hs] at hn
  refine loop_wait hpc hk hd rfl hJ hn ?_
  rw [hs]
  exact blk_ready _

theorem ok_rawWait : StepOk P L g .rawWait := by
  intro d d' n e hs hpc hu hJ hev hn
  have hd : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨-, -, -, -, -, hbuf, -, -, -, -⟩ := words_of hd hJ
  simp only [EvK, Poll, hs] at hev
  obtain ⟨ok, hk⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  rw [free_of hbuf] at hk
  simp only [succ, hs] at hn
  refine loop_wait hpc hk hd rfl hJ hn ?_
  rw [hs]
  exact blk_free _

/-- A coordinate element: one more read. -/
theorem ok_coord {s : Site} (hs4 : ∃ k, s = .coord0 k ∨ s = .coord1 k ∨ s = .coord2 k ∨
    s = .coord3 k) : StepOk P L g s := by
  intro d d' n e hs hpc hu hJ hev hn
  obtain ⟨k, hk4⟩ := hs4
  have hk := k.isLt
  have hd : d.site.inLoop = true := by rw [hs]; rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hev' : (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f := by
    simp only [EvK, hs] at hev
    rcases hk4 with rfl | rfl | rfl | rfl <;> exact hev.imp (fun ⟨a, bs, h, _⟩ => ⟨a, bs, h⟩) id
  obtain ⟨a, bs, hkd⟩ | ⟨f, hf⟩ := hev'
  swap; exact absurd hf (hu f)
  have hK : kindOf e = some .rd := by simp [kindOf, hkd]
  rcases hk4 with rfl | rfl | rfl | rfl <;> simp only [succ, hs] at hn <;>
    obtain ⟨x, rfl⟩ := rd_next hn
  · exact loop_to hpc hK hd rfl id rfl hJ (blk_rd_to (by rw [hs]; rfl) (by rw [hs]; rfl)
      (by rw [hs]; rfl))
  · exact loop_to hpc hK hd rfl id rfl hJ (blk_rd_to (by rw [hs]; rfl) (by rw [hs]; rfl)
      (by rw [hs]; rfl))
  · exact loop_to hpc hK hd rfl id rfl hJ (blk_rd_to (by rw [hs]; rfl) (by rw [hs]; rfl)
      (by rw [hs]; rfl))
  · have hl : (afterCoord k).inLoop = true := by unfold afterCoord; split_ifs <;> rfl
    obtain ⟨p1, p2, p3⟩ := coord_places k
    refine loop_to hpc hK hd hl id rfl hJ (blk_rd_to ?_ ?_ ?_) <;>
      simp only [hs, p1, p2, p3, afterQuad_site] <;> rfl

theorem ok_gather (k : Fin 16) : StepOk P L g (.gather k) := by
  intro d d' n e hs hpc hu hJ hev hn
  have hk := k.isLt
  have hd : d.site.inLoop = true := by rw [hs]; rfl
  simp only [EvK, hs] at hev
  obtain ⟨a, s, hkd, hmb⟩ | ⟨f, hf⟩ := hev
  swap; exact absurd hf (hu f)
  obtain ⟨-, -, -, -, -, hbuf, -, -, -, -⟩ := words_of hd hJ
  rw [raw_of hbuf] at hmb
  have hK : kindOf e = some (.gather ((objs L g).raw (d.cnt.toNat % 2))) := by
    simp [kindOf, hkd, hmb]
  simp only [succ, hs, Option.some.injEq] at hn
  subst hn
  have hl : (afterGather k).inLoop = true := by unfold afterGather; split_ifs <;> rfl
  refine loop_to (d' := { d with site := afterGather k }) hpc hK hd hl id rfl hJ
    (blk_gather_to ?_ ?_ ?_) <;> simp only [hs, gather_places k] <;> rfl

theorem ok_rawArrive : StepOk P L g .rawArrive := by
  intro d d' n e hs hpc hu hJ hev hn
  have hd : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨-, -, -, -, -, hbuf, -, -, -, -⟩ := words_of hd hJ
  have hk : e.kind = .arrive (smLoc L g (rawW L d) 0) 36864 1 true .cta := by
    simpa only [EvK, hs] using hev
  rw [raw_of hbuf] at hk
  have hK : kindOf e = some (.arrive ((objs L g).raw (d.cnt.toNat % 2))) := by simp [kindOf, hk]
  simp only [succ, hs, Option.some.injEq] at hn
  subst hn
  refine loop_to (d' := { d with site := .coordFree }) hpc hK hd rfl id rfl hJ ?_
  rw [hs]
  exact blk_raw _

/-- **The block's end**: block `r + 1` with its words, or the CTA barrier after the last block. -/
theorem ok_coordFree : StepOk P L g .coordFree := by
  intro d d' n e hs hpc hu hJ hev hn
  have hd : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨hlt, h1R, hR, hr, hcnt, hbuf, hslot, hpf, hpr, hneg⟩ := words_of hd hJ
  have hk : e.kind = .arrive (smLoc L g (cfreeW L d) 0) 0 1 true .cta := by
    simpa only [EvK, hs] using hev
  rw [cfree_of hslot] at hk
  have hK : kindOf e = some (.arrive ((objs L g).cfree (d.cnt.toNat % 4))) := by
    simp [kindOf, hk]
  have hB := bump_kind (B := cntAt (objs L g) 3 (d.cnt.toNat + 1) 0 0 0 false) hpc
    ((core_loop hd).1 hJ).2 fun c _ => by rw [hK, hs]; exact blk_end _ c
  simp only [succ, hs, Option.some.injEq] at hn
  subst hn
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := block_end hr hR hcnt hbuf hslot hpf hpr hneg
  rw [e6] at e7
  unfold loopEnd
  simp only [e1, e2, e3, e4, e5, e6, e7]
  have hw : (W (d.cnt.toNat + 1)).toNat = d.cnt.toNat + 1 := toNat_W (by omega)
  split_ifs with hc
  · have hr1 : d.cnt.toNat + 1 < rounds d.l0 d.l1 := by simp at hc; omega
    refine (core_loop rfl).2 ⟨⟨hlt, h1R, hR, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [hw]
    · exact hr1
    · exact hB
  · have hr1 : d.cnt.toNat + 1 = rounds d.l0 d.l1 := by simp at hc; omega
    unfold RefCore
    rw [← hr1]
    exact hB

theorem ok_outBar : StepOk P L g .outBar := by
  intro d d' n e hs hpc hu hJ hev hn
  have hk : e.kind = .bar 12 none .sync := by simpa only [EvK, hs] using hev
  have hK : kindOf e = some (.bar 12) := by simp [kindOf, hk]
  have hJ' : ∀ c, c ≠ .ub → n c = cntAt (objs L g) 3 (rounds d.l0 d.l1) 0 0 0 false c := by
    unfold RefCore at hJ; rw [hs] at hJ; exact hJ
  simp only [succ, hs, Option.some.injEq] at hn
  subst hn
  unfold RefCore
  exact .inr (bump_kind hpc hJ' fun c _ => hK ▸ fin_bar c)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **`RefCore` is kept by every step** on an event of the state's kind that is not undefined
behaviour. -/
theorem core_next {d d' : D} {n : Cnt → Nat} {e : Event} (hpc : inRole e = true)
    (hu : ∀ f, e.kind ≠ .ub f) (hJ : RefCore L g d n) (hev : EvK L g d e)
    (hn : succ P L g d e = some (some d')) : RefCore L g d' (Code.bump cls n e) := by
  have h : StepOk P L g d.site := by
    cases d.site with
    | elect => exact ok_elect
    | loadTopk => exact ok_loadTopk
    | loadExtra => exact ok_loadExtra
    | qWait => exact ok_qWait
    | storeWait => exact ok_storeWait
    | coordWait => exact ok_coordWait
    | rawWait => exact ok_rawWait
    | coord0 k => exact ok_coord ⟨k, .inl rfl⟩
    | coord1 k => exact ok_coord ⟨k, .inr (.inl rfl)⟩
    | coord2 k => exact ok_coord ⟨k, .inr (.inr (.inl rfl))⟩
    | coord3 k => exact ok_coord ⟨k, .inr (.inr (.inr rfl))⟩
    | gather k => exact ok_gather k
    | rawArrive => exact ok_rawArrive
    | coordFree => exact ok_coordFree
    | outBar => exact ok_outBar
    | exit | leave _ =>
      intro d₀ _ _ _ hs _ _ _ _ hn₀
      simp [succ, hs] at hn₀
  exact h d d' n e rfl hpc hu hJ hev hn

/-- **The reference invariant is kept by every step** the machine follows. -/
theorem ref_next {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : Ref L g d n) (hev : Ev L g d e)
    (hn : succ P L g d e = some (some d')) : Ref L g d' (Code.bump cls n e) := by
  intro h0
  have hpc := inRole_next hev.1 hn
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    simp [Code.bump, cls, hpc, kindOf, hf] at h0
  · have hn0 : n .ub = 0 := by
      simp only [Code.bump] at h0
      omega
    exact core_next hpc (fun f h => hu ⟨f, h⟩) (hJ hn0) hev.2 hn

/-- **The first state has the reference invariant** with no event counted. -/
theorem ref_init : Ref L g init fun _ => 0 := fun _ =>
  (core_pro (d := init) ⟨rfl, nofun, nofun⟩).2 fun c _ => by
    cases c <;> simp [cntAt, proCnt, loopCnt, init, Site.pro, useAt, ringUses]

/-! ### The sites' launch facts -/

/-- The sites that `SiteOk` asks nothing of. -/
def Site.free : Site → Bool
  | .loadTopk | .loadExtra | .leave _ => false
  | _ => true

theorem siteOk_free {d : D} (h : d.site.free = true) : SiteOk P L g d := by
  refine ⟨fun hs => ?_, fun hs => ?_, fun s hs => ?_⟩ <;> rw [hs] at h <;> cases h

/-- The elected lane's next state, or a length load's. -/
theorem siteOk_lead {d : D} (x : BitVec 64) :
    SiteOk P L g (leadNext P L g d) ∧ SiteOk P L g (afterTopk P d x) := by
  have ha : ∀ (d : D) x, SiteOk P L g (afterTopk P d x) := by
    intro d x
    unfold afterTopk lensD
    split_ifs with h
    · exact siteOk_free rfl
    · exact ⟨nofun, fun _ => Bool.eq_false_iff.mpr h, nofun⟩
  refine ⟨?_, ha d x⟩
  unfold leadNext
  split_ifs with h1 h2
  · exact siteOk_free rfl
  · exact ha _ _
  · exact ⟨fun _ => Bool.eq_false_iff.mpr h2, nofun, nofun⟩

/-- A poll's successor is its site or the poll. -/
theorem free_poll {d d' d₁ : D} {e : Event} (hd : d.site.free = true) (h₁ : d₁.site.free = true)
    (hn : poll d e d₁ = some (some d')) : d'.site.free = true := by
  unfold poll at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    split_ifs
    · exact h₁
    · exact hd
  · cases hn

/-- **Every state the machine reaches by a step has `SiteOk`.** -/
theorem siteOk_step {d d' : D} {e : Event} (hn : succ P L g d e = some (some d')) :
    SiteOk P L g d' := by
  cases hs : d.site with
  | elect =>
    simp only [succ, hs, electNext] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs
      · exact (siteOk_lead 0).1
      · exact ⟨nofun, nofun, fun s h => by cases h; rfl⟩
    · cases hn
  | loadTopk =>
    simp only [succ, hs] at hn
    obtain ⟨x, rfl⟩ := word_next hn
    exact (siteOk_lead x).2
  | loadExtra =>
    simp only [succ, hs] at hn
    obtain ⟨x, rfl⟩ := word_next hn
    exact siteOk_free rfl
  | exit | leave _ => simp [succ, hs] at hn
  | qWait | storeWait | coordWait | rawWait =>
    simp only [succ, hs] at hn
    refine siteOk_free (free_poll (by rw [hs]; rfl) ?_ hn)
    first | rfl | (unfold loopEntry; split_ifs <;> rfl)
  | coord0 k | coord1 k | coord2 k | coord3 k =>
    simp only [succ, hs] at hn
    obtain ⟨x, rfl⟩ := rd_next hn
    refine siteOk_free ?_
    first | rfl | (show (afterCoord k).free = true; unfold afterCoord; split_ifs <;> rfl)
  | gather k | rawArrive | coordFree | outBar =>
    simp only [succ, hs, Option.some.injEq] at hn
    subst hn
    refine siteOk_free ?_
    first | rfl | (show (afterGather k).free = true; unfold afterGather; split_ifs <;> rfl) |
      (unfold loopEnd; split_ifs <;> rfl)

/-- The first state has `SiteOk`. -/
theorem siteOk_init : SiteOk P L g init := ⟨nofun, nofun, fun _ h => by cases h⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
