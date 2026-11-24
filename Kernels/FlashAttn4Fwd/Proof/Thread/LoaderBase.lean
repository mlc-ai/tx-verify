-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Loader
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWorkPre
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreBase
public import Lemmas.Flow.PointerReg
public import Lemmas.Flow.Segment
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! Definitions and helper facts of the loader's step lemmas: the conclusion of a step
(`Step`), the shape of the launch under `Pre`, the one-instruction steps a segment is cut at
(the peer-bit mask `peer_exec`, a shared pointer plus an offset, the CTA's rank branch), the
steps of the event kinds as continuations by segments (`step_wait_of`, `step_elect_of`,
`step_arrive_of`, `step_copy_of`) and the segment tactic `loader_seg`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000

/-- The conclusion of a step of this role, under the assumptions `A`: the thread leaves the
role, or steps to `d'` at `t'` by a run of `Tau`. -/
def Step (A : List Assumption) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) :
    Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel A L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
      Inv L g d'

/-- A segment of the loader's code from `pc` with facts `F` to the site of `d'`. -/
abbrev SegTo (L : Launch) (g pc : Nat) (F : List (Nat × Value)) (d' : D) : Prop :=
  ∃ k, Seg kernel asms L g k pc F d'.site.pc (facts L g d')

theorem facts_ne {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- Facts at a program counter, restated at another whose live registers are among them. -/
theorem holds_relive {L : Launch} {g pc pc' : Nat} {d d' : D} {R : Nat → Option Value}
    (h : Holds R (factsAt L g pc d)) (hv : valueOf L g d' = valueOf L g d)
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : Holds R (factsAt L g pc' d') := by
  unfold factsAt at h ⊢
  rw [hv]
  exact holds_factsFrom_mono h hl

/-- A table fact at a checkpoint where the register is live. -/
theorem tbl_mem {L : Launch} {g pc : Nat} {d : D} {r : Nat} {v : Value} (hl : r ∈ Flow.live pc)
    (hv : valueOf L g d r = v) : (r, v) ∈ factsAt L g pc d :=
  hv ▸ Flow.mem_factsFrom hl

/-- Facts after one written register, restated at a program counter whose live registers are
the written one and live ones of before. -/
theorem holds_cons_relive {L : Launch} {g pc pc' : Nat} {d d' : D} {R : Nat → Option Value}
    {r : Nat} {v : Value} (h : Holds R ((r, v) :: factsAt L g pc d))
    (hv : valueOf L g d r = v) (hd : valueOf L g d' = valueOf L g d)
    (hl : ∀ x ∈ Flow.live pc', x = r ∨ x ∈ Flow.live pc) : Holds R (factsAt L g pc' d') := by
  unfold factsAt at h ⊢
  rw [hd]
  apply holds_of_pointwise
  intro x hx
  rcases hl x hx with rfl | h'
  · rw [hv]; exact h.1
  · exact holds_mem h.2 (Flow.mem_factsFrom h')

/-- No step: the site of `d'` is the checkpoint itself. -/
theorem segTo_here {L : Launch} {g pc pc0 : Nat} {d d' : D} (hpc : d'.site.pc = pc)
    (hv : valueOf L g d' = valueOf L g d) (hl : ∀ r ∈ Flow.live pc, r ∈ Flow.live pc0) :
    SegTo L g pc (factsAt L g pc0 d) d' :=
  ⟨0, hpc ▸ Seg.weaken_end (Seg.refl _ _) fun _ hR => holds_relive hR hv (hpc ▸ hl)⟩

/-- A segment from the facts at a checkpoint, from the facts at an earlier one. -/
theorem segTo_of {L : Launch} {g pc pc0 pc1 : Nat} {d d0 d' : D}
    (hs : SegTo L g pc (factsAt L g pc0 d0) d') (hv : valueOf L g d0 = valueOf L g d)
    (hl : ∀ r ∈ Flow.live pc0, r ∈ Flow.live pc1) : SegTo L g pc (factsAt L g pc1 d) d' :=
  let ⟨k, hs⟩ := hs
  ⟨k, Seg.weaken_start hs fun _ hR => holds_relive hR hv hl⟩

/-- The bounds of a state at a site of an item. -/
theorem Inv.site {L : Launch} {g : Nat} {d : D} (s : Site) (hi : Inv L g d)
    (hit : s.inItem = true → d.i < T L g) (htr : s.inTrip = true → d.t + 2 ≤ n L)
    (hl : s.leadOnly = true → rank L g = 0)
    (ho : ∀ u j, (s = .elC u j ∨ s = .copy u j) → j.val < u.copies) :
    Inv L g { d with site := s } :=
  ⟨hi.s, hi.ph, hi.qp, hit, htr, hl, ho⟩

/-- `Inv` of a state `d` moved to the site `s` of the same item: each bound from `d`'s or by
evaluation. -/
macro "inv_site" hi:term:max hr:term:max : tactic => `(tactic| (
  refine Inv.site _ $hi ?_ ?_ ?_ ?_
  · intro _; exact ($hi).item rfl
  · intro h
    first | exact ($hi).trip rfl | (simp [Site.inTrip] at h; done)
  · intro h
    first | exact $hr | (simp [Site.leadOnly] at h; done)
  · intro u j h
    rcases h with h | h <;> cases h <;> decide))

/-! ### The launch under `Pre` -/

/-- The bounds the segments use: the shared window, `seqlen_k` and the KV tile count. -/
theorem shape {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    L.sharedBase + 232448 ≤ 2 ^ 18 ∧ skOf L % 128 = 0 ∧ 0 < skOf L ∧ skOf L < 2 ^ 31 ∧
      n L = skOf L / 128 ∧ 1 ≤ n L ∧ n L ≤ 2 ^ 24 := by
  have hb := hpre.sharedRange
  unfold sharedBytes at hb
  have hs : skOf L = P.sk := skOf_eq hpre
  have h1 := hpre.skDiv128
  have h2 := hpre.skPos
  have h3 := hpre.skRange
  refine ⟨hb, by omega, by omega, by omega, ?_, ?_, ?_⟩ <;> unfold n sk <;> omega

/-! ### One-instruction steps a segment is cut at -/

/-- Under `Pre`, the even CTA of a thread's pair. -/
theorem peerCta_even {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) :
    L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2) = some (2 * (ctaOf L g / 2)) := by
  have hcta := cta_lt hg
  have hcl := hpre.cluster
  have hgr := hpre.grid
  unfold ctaOf at hcta ⊢
  have h1 := hpre.oneDimLaunch.1
  simp only [Launch.peerCta, Launch.oneDim_rankOfCta h1, Launch.oneDim_clusterOfCta h1,
    Launch.oneDim_clusterStart h1, Launch.oneDim_clusterSizeOf h1, hcl]
  split_ifs with hh
  · congr 1
    omega
  · exact absurd (by refine ⟨hcta, ?_, ?_⟩ <;> omega) hh

/-- **The peer-bit mask.** `and.b32 d, a, -16777217` of the address `sb + k` at one of the
peer-bit sites is a segment step of `Assumptions.peerBit`: the even CTA's byte (`peerV`). -/
theorem run_peer {P : Params} {L : Launch} {mem0 : Mem0} {g pc : Nat} {t : TState}
    {F : List (Nat × Value)} {d a k : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some d],
      [.reg a, .imm (-16777217)]⟩⟩)
    (hpc : Assumptions.peerBitSites.contains pc = true) (h : At t pc F) (ha : (a, sb L k) ∈ F)
    (hk : L.sharedBase + k < 2 ^ 24) (hd : ∀ p ∈ F, p.1 ≠ d) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) ((d, peerV L g k) :: F) := by
  have hx : (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + k))).toNat = L.sharedBase + k := by
    simp only [truncBits, BitVec.toNat_ofNat]; omega
  have h₁ : Assumption.SegFreePc [Assumptions.idealArith, Assumptions.clusterMbar,
      Assumptions.approx, Assumptions.swExp2] pc := by
    simp only [Assumptions.peerBitSites, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at hpc
    rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl <;> seg_free_pc
  have e : asms = [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.approx,
      Assumptions.swExp2] ++ Assumptions.peerBit :: [Assumptions.tcLd,
      Assumptions.commitOrder, Assumptions.pollAgree] := rfl
  have hr : run kernel asms L g 1 t = some (PTX.next (setReg t d (.ptr 32 false
          (.shared (g / L.block) (2 * (ctaOf L g / 2)))
          (BitVec.ofNat 64 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + k))).toNat)))) := by
    rw [e]
    unfold Assumptions.peerBit
    exact run_pairEvenAt (x := BitVec.ofNat 64 (L.sharedBase + k)) hc h hpc ha
      (by rw [hx]; exact hk)
      (by rw [L.oneDim_clusterSizeOf hpre.oneDimLaunch.1, hpre.cluster])
      (peerCta_even hpre hg) h₁
  rw [hx] at hr
  exact ⟨_, hr, At.set h hd⟩

/-- The step of a shared pointer plus an integer register, keeping the facts. -/
theorem run_ptr {L : Launch} {g pc : Nat} {t : TState} {F : List (Nat × Value)}
    {d r q : Nat} {i c a k b : Nat} {ik : IType}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int ik 32, false, [some d],
      [.reg r, .reg q]⟩⟩) (h : At t pc F)
    (hr : (r, .ptr 32 false (.shared i c) (BitVec.ofNat 64 a)) ∈ F) (hq : (q, b32 k) ∈ F)
    (ha : a + k < 2 ^ 32) (hk : k < 2 ^ 31) (hb : a + k = b) (hd : ∀ p ∈ F, p.1 ≠ d)
    (hik : ik ≠ .b) (hsf : Assumption.SegFreePc asms pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧
      At t' (pc + 1) ((d, .ptr 32 false (.shared i c) (BitVec.ofNat 64 b)) :: F) :=
  ⟨_, run_add_sharedPtr_reg hc h hr hq ha hk hb hik asms_localRule_none hsf, At.set h hd⟩

/-- The peer-bit mask as a piece of a segment. -/
theorem seg_peer {P : Params} {L : Launch} {mem0 : Mem0} {g pc : Nat}
    {F : List (Nat × Value)} {d a k : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some d],
      [.reg a, .imm (-16777217)]⟩⟩)
    (hpc : Assumptions.peerBitSites.contains pc = true) (ha : (a, sb L k) ∈ F)
    (hk : L.sharedBase + k < 2 ^ 24) (hd : ∀ p ∈ F, p.1 ≠ d) :
    Seg kernel asms L g 1 pc F (pc + 1) ((d, peerV L g k) :: F) :=
  fun _ h => run_peer hpre hg hc hpc h ha hk hd

section
variable {L : Launch}

/-- A shared pointer plus an integer register as a piece of a segment. -/
theorem seg_ptr {g pc : Nat} {F : List (Nat × Value)} {d r q : Nat} {i c a k b : Nat} {ik : IType}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int ik 32, false, [some d],
      [.reg r, .reg q]⟩⟩) (hr : (r, .ptr 32 false (.shared i c) (BitVec.ofNat 64 a)) ∈ F)
    (hq : (q, b32 k) ∈ F) (ha : a + k < 2 ^ 32) (hk : k < 2 ^ 31) (hb : a + k = b)
    (hd : ∀ p ∈ F, p.1 ≠ d) (hik : ik ≠ .b := by decide)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    Seg kernel asms L g 1 pc F (pc + 1)
      ((d, .ptr 32 false (.shared i c) (BitVec.ofNat 64 b)) :: F) :=
  fun _ h => run_ptr hc h hr hq ha hk hb hd hik hsf

/-- No fact of a list of explicit facts and a table names a register outside both. -/
theorem cons_ne {g pc : Nat} {d : D} {ex : List (Nat × Value)} {r : Nat} (hex : ∀ p ∈ ex, p.1 ≠ r)
    (hr : r ∉ Flow.live pc) : ∀ p ∈ ex ++ factsAt L g pc d, p.1 ≠ r := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hex p hp
  · exact facts_ne hr p hp

/-- One local instruction whose step is computed separately, as a piece of a segment. -/
theorem seg_one {g pc r : Nat} {F : List (Nat × Value)} {op : Op} {v : Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc F → execLocalA asms L g t op = .ok (PTX.next (setReg t r v)))
    (hd : ∀ p ∈ F, p.1 ≠ r) : Seg kernel asms L g 1 pc F (pc + 1) ((r, v) :: F) :=
  fun t h => ⟨_, run_local hc hl h (hex t h), At.set h hd⟩

/-- A branch on the CTA's rank in its pair. -/
theorem seg_rank {g pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hp : (p, Value.pred (decide (rank L g ≠ 0))) ∈ F)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    Seg kernel asms L g 1 pc F (if rank L g = 0 then pc + 1 else target) F := by
  have hs := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) hc hp
    (fun _ _ => asms_localRule_none) hsf
  by_cases hr : rank L g = 0 <;> simpa [hr] using hs

theorem val52 (L : Launch) (g : Nat) (d : D) :
    valueOf L g d 52 = .pred (decide (rank L g ≠ 0)) := by
  simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]

theorem val92 (L : Launch) (g : Nat) (d : D) :
    valueOf L g d 92 = .pred (decide (rank L g ≠ 0)) := by
  simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]

/-- After a successful poll of use `u`: the leader CTA's election of the arrival, or on the odd
CTA the use's first copy election (from the use's first instruction after the arrival,
`target`). -/
theorem seg_wait_ok {g : Nat} {d : D} {u : UseK} {w p target : Nat} (hw : d.site.pc = w)
    (hc1 : kernel.code[w + 1]? = some ⟨some (p, false), .bra (w + 3) true⟩)
    (hc3 : kernel.code[w + 3]? = some ⟨some (52, false), .bra target false⟩)
    (hA : (Site.elA u).pc = w + 4) (h52 : 52 ∈ Flow.live w)
    (hlA : ∀ r ∈ Flow.live (w + 4), r ∈ Flow.live w)
    (hT : SegTo L g target (factsAt L g target d) { d with site := .elC u 0 })
    (hlT : ∀ r ∈ Flow.live target, r ∈ Flow.live w)
    (hsf1 : Assumption.SegFreePc asms (w + 1) := by seg_free_pc)
    (hsf3 : Assumption.SegFreePc asms (w + 3) := by seg_free_pc) :
    SegTo L g (d.site.pc + 1) ((p, .pred true) :: facts L g d)
      (if rank L g = 0 then { d with site := .elA u } else { d with site := .elC u 0 }) := by
  rw [hw]
  have hF : facts L g d = factsAt L g w d := by rw [← hw]
  rw [hF]
  have h1 := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) hc1
    (List.mem_cons_self (a := (p, Value.pred true)) (l := factsAt L g w d))
    (fun _ _ => asms_localRule_none) hsf1
  simp only [↓reduceIte] at h1
  have h2 := seg_rank (L := L) (g := g) hc3
    (List.mem_cons_of_mem (p, Value.pred true) (tbl_mem h52 (val52 L g d))) hsf3
  have hdrop : ∀ R, Holds R ((p, Value.pred true) :: factsAt L g w d) →
      Holds R (factsAt L g w d) := fun _ hR => hR.2
  by_cases hr : rank L g = 0
  · simp only [hr, ↓reduceIte] at h2 ⊢
    have hA' : ({ d with site := .elA u } : D).site.pc = w + 3 + 1 := hA
    refine ⟨1 + 1, ?_⟩
    rw [hA']
    exact Seg.weaken_end (Seg.comp h1 h2) fun R hR =>
      holds_relive (hdrop R hR) rfl (hA' ▸ hlA)
  · simp only [hr, ↓reduceIte] at h2 ⊢
    obtain ⟨k, hT⟩ := hT
    exact ⟨1 + 1 + k, Seg.comp (Seg.comp h1 h2)
      (Seg.weaken_start hT fun R hR => holds_relive (hdrop R hR) rfl hlT)⟩

/-- `xor.b32` of a parity bit with the selected wrap bit 0 or 1, and with the literal 1. -/
theorem xor_bit_zero {r : Nat} (hr : r < 2) :
    truncBits 32 (BitVec.ofNat 64 r) ^^^ truncBits 32 (truncBits 32 (BitVec.ofInt 64 0)) =
      BitVec.ofNat 64 r := by
  interval_cases r <;> decide

theorem xor_bit_one {r : Nat} (hr : r < 2) :
    truncBits 32 (BitVec.ofNat 64 r) ^^^ truncBits 32 (truncBits 32 (BitVec.ofInt 64 1)) =
      BitVec.ofNat 64 (1 - r) := by
  interval_cases r <;> decide

theorem xor_one {r : Nat} (hr : r < 2) :
    truncBits 32 (BitVec.ofNat 64 r) ^^^ truncBits 32 (BitVec.ofInt 64 1) =
      BitVec.ofNat 64 (1 - r) := by
  interval_cases r <;> decide

theorem pnext_lt {s p : Nat} (hp : p < 2) : pnext s p < 2 := by
  unfold pnext; split_ifs <;> omega

theorem snext_lt {s : Nat} (hs : s < 6) : snext s < 6 := by
  unfold snext; split_ifs <;> omega

/-- A segment through a `selp` on a predicate the evaluation cannot decide: a piece to the
`selp` with the predicate's table fact `decide c`, then a piece for each outcome `b`, with the
fact `(p, .pred b)` in front of the table's. -/
theorem seg_wrap {g kA kB pc0 pcS pcE p : Nat} {F0 G : List (Nat × Value)} {d : D} {c : Prop}
    [Decidable c] (hA : Seg kernel asms L g kA pc0 F0 pcS (factsAt L g pcS d))
    (hmem : (p, Value.pred (decide c)) ∈ factsAt L g pcS d)
    (hB : ∀ b, decide c = b → Seg kernel asms L g kB pcS ((p, .pred b) :: factsAt L g pcS d) pcE G)
    :
    Seg kernel asms L g (kA + kB) pc0 F0 pcE G :=
  Seg.comp hA (Seg.weaken_start (hB _ rfl) fun _ hR => ⟨holds_mem hR hmem, hR⟩)

theorem snext_wrap {x : Nat} (h : x + 1 = 6) : snext x = 0 := by simp [snext, h]
theorem snext_nowrap {x : Nat} (h : ¬ x + 1 = 6) : snext x = x + 1 := by simp [snext, h]
theorem pnext_wrap {x p : Nat} (h : x + 1 = 6) : pnext x p = 1 - p := by simp [pnext, h]
theorem pnext_nowrap {x p : Nat} (h : ¬ x + 1 = 6) : pnext x p = p := by simp [pnext, h]

theorem sAfter_zero (s : Nat) : sAfter 0 s = s := rfl
theorem sAfter_succ (k s : Nat) : sAfter (k + 1) s = snext (sAfter k s) := rfl
theorem pAfter_zero (s p : Nat) : pAfter 0 s p = p := rfl
theorem pAfter_succ (k s p : Nat) : pAfter (k + 1) s p = pnext (sAfter k s) (pAfter k s p) := rfl
theorem sAfter_two (s : Nat) : sAfter 2 s = snext (snext s) := rfl
theorem pAfter_two (s p : Nat) : pAfter 2 s p = pnext (snext s) (pnext s p) := rfl

theorem sAfter_lt {s : Nat} (hs : s < 6) : ∀ k, sAfter k s < 6
  | 0 => hs
  | k + 1 => snext_lt (sAfter_lt hs k)

theorem pAfter_lt {s p : Nat} (hp : p < 2) : ∀ k, pAfter k s p < 2
  | 0 => hp
  | k + 1 => pnext_lt (pAfter_lt hp k)

/-- A conditional branch on a predicate fact `(p, .pred c)`: the segment to `d1` from the
target when `c` holds, to `d2` from the next instruction otherwise. -/
theorem segTo_bra {g pc target p : Nat} {F : List (Nat × Value)} {c : Bool} {d1 d2 : D}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩) (hp : (p, Value.pred c) ∈ F)
    (h1 : c = true → SegTo L g target F d1) (h2 : c = false → SegTo L g (pc + 1) F d2)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    SegTo L g pc F (if c then d1 else d2) := by
  have hb := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) hc hp
    (fun _ _ => asms_localRule_none) hsf
  cases c
  · obtain ⟨k, hs⟩ := h2 rfl
    exact ⟨1 + k, Seg.comp hb hs⟩
  · obtain ⟨k, hs⟩ := h1 rfl
    exact ⟨1 + k, Seg.comp hb hs⟩

/-! ### Steps of the event kinds -/

theorem step_of_seg {g : Nat} {d d' : D} {e : Event} {u : TState} {F : List (Nat × Value)}
    {pc : Nat} (hn : next L g d e = some (some d')) (hi : Inv L g d') (hu : At u pc F)
    (hs : SegTo L g pc F d') : Step asms L g d e u := by
  obtain ⟨k, hs⟩ := hs
  obtain ⟨t', hr, ht'⟩ := hs u hu
  exact .inr ⟨d', t', hn, run_rtg hr, ht', hi⟩

/-- A poll: a failed one returns to the site, a successful one reaches `dok`. -/
theorem step_wait_of {g : Nat} {d dok : D} {t u : TState} {e : Event} {ins : Instr} {p base : Nat}
    {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hop : ins.op = .mbarWait p base off par acq sc) (hp : p ∉ Flow.live d.site.pc)
    (hnf : ∀ m par acq sc, next L g d ⟨d.site.pc, .wait m par false acq sc⟩ = some (some d))
    (hnt : ∀ m par acq sc, next L g d ⟨d.site.pc, .wait m par true acq sc⟩ = some (some dok))
    (hsf : SegTo L g (d.site.pc + 1) ((p, .pred false) :: facts L g d) d)
    (hst : SegTo L g (d.site.pc + 1) ((p, .pred true) :: facts L g d) dok) (hi : Inv L g d)
    (hik : Inv L g dok) (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  rw [hop, ← h.1] at hf
  obtain ⟨m, parity, ok, scope, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := p) (v := .pred ok) h (facts_ne hp)
  rw [h.1]
  cases ok
  · exact step_of_seg (hnf _ _ _ _) hi h1 hsf
  · exact step_of_seg (hnt _ _ _ _) hik h1 hst

/-- An election: the leader reaches `dl`, the other lanes `ds`. -/
theorem step_elect_of {g : Nat} {d dl ds : D} {t u : TState} {e : Event} {ins : Instr} {r p : Nat}
    {mask : Opnd} (hop : ins.op = .warp ⟨.elect, none, [some r, some p], [], some mask⟩)
    (hr : r ∉ Flow.live d.site.pc) (hp : p ∉ Flow.live d.site.pc) (hpr : r ≠ p)
    (hn : ∀ mk inst ld, next L g d ⟨d.site.pc, .elect mk inst ld⟩ =
      some (some (if laneOf L g = ld then dl else ds)))
    (hsl : ∀ ld, SegTo L g (d.site.pc + 1)
      ((p, .pred true) :: (r, .bits 32 (BitVec.ofNat 64 ld)) :: facts L g d) dl)
    (hss : ∀ ld, SegTo L g (d.site.pc + 1)
      ((p, .pred false) :: (r, .bits 32 (BitVec.ofNat 64 ld)) :: facts L g d) ds) (hil : Inv L g dl)
    (his : Inv L g ds) (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  rw [hop] at hf
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h0 : At (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) d.site.pc
      ((r, .bits 32 (BitVec.ofNat 64 ld)) :: facts L g d) :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Function.update_self .., holds_update h.2.2.2.2 (facts_ne hr)⟩
  have hp' : ∀ q ∈ (r, Value.bits 32 (BitVec.ofNat 64 ld)) :: facts L g d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hpr
    · exact facts_ne hp q hq
  by_cases hld : laneOf L g = ld
  · have h1 := At.set (r := p) (v := .pred true) h0 hp'
    have hb : (laneOf L g == ld) = true := by simp [hld]
    rw [hb]
    have hn' := hn mk inst ld
    simp only [hld, ↓reduceIte] at hn'
    exact step_of_seg hn' hil h1 (hsl ld)
  · have h1 := At.set (r := p) (v := .pred false) h0 hp'
    have hb : (laneOf L g == ld) = false := by simp [hld]
    rw [hb]
    have hn' := hn mk inst ld
    simp only [hld, ↓reduceIte] at hn'
    exact step_of_seg hn' his h1 (hss ld)

/-- An arrival whose state destination is not live: to `d'`. -/
theorem step_arrive_of {g : Nat} {d d' : D} {t u : TState} {e : Event} {ins : Instr} {base : Nat}
    {off : Int} {tx count : Opnd} {rel : Bool} {sc : MbarScope} {r : Nat}
    (hop : ins.op = .mbarArrive base off tx count false rel sc (some r))
    (hr : r ∉ Flow.live d.site.pc)
    (hn : ∀ pc m tx c rel sc, next L g d ⟨pc, .arrive m tx c rel sc⟩ = some (some d'))
    (hs : SegTo L g (d.site.pc + 1) (facts L g d) d') (hi : Inv L g d')
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  rw [hop] at hf
  obtain ⟨rfl, m, tx', c, rel', sc', hk, -⟩ := Store.fires_arrive_state hf
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact step_of_seg (hn _ _ _ _ _ _) hi (Store.At.clear h (facts_ne hr)) hs

/-- A tensor load's issue: to `d'`. -/
theorem step_copy_of {g : Nat} {d d' : D} {t u : TState} {e : Event} {ins : Instr} {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {pol : Option Opnd} (hop : ins.op = .cpTensor ca grp dst off map cs mb moff none lm pol)
    (hn : ∀ a s, next L g d ⟨d.site.pc, .tensorIssue a s⟩ = some (some d'))
    (hs : SegTo L g (d.site.pc + 1) (facts L g d) d') (hi : Inv L g d')
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  rw [hop] at hf
  obtain ⟨a, s, rfl, rfl, -⟩ := fires_cpTensor_issue hf
  exact step_of_seg (hn a s) hi (At.next h) hs
end

/-! ### Tactics -/

/-- A closed fact about the live registers at a state's site. -/
macro "live_dec" : tactic => `(tactic| ((try dsimp only [Site.pc]); table_decide))

/-- Evaluate a loader segment from `h` and close the facts of its end state: by unfolding the
code's terms (`rfl`), the normal form of integer values and predicates (with the launch's
shape under `Pre` in context), or the signed rules. -/
syntax "loader_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| loader_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hsh := shape $hpre
      have hrk : rank L g < 2 := Nat.mod_lt _ (by decide)
      seg_fp $h using
        try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
          Option.getD_none, $extra,*]
        all_goals (try launch_norm $hpre)
        all_goals first
          | w_rfl [qRowW]
          | seg_close [Prologue.sb, $extra,*]
          | norm_signed [Prologue.sb, rank, $extra,*]
          | rfl))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
