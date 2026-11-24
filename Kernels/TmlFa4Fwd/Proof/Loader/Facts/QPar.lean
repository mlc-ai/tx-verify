-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.CountFact
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasAcq
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The parity of the drain's poll of the second Q stage

Standalone fact. On warp 14 the drain's parity register `%r7192` is the parity of the lane's
successful polls of barrier 24 plus one: 1 when the tile has no block, 0 after a tile's one poll
(`QPar`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Scan)

noncomputable section
set_option maxRecDepth 100000

/-- The polls of barrier 24 before a site, on warp 14 (the drain has either count). -/
def qCnt : Site → Option Nat
  | .tw t => some (if 2 < t.val then 1 else 0)
  | .te t _ | .ta t | .tc t _ => some (if 2 ≤ t.val then 1 else 0)
  | .pgLd per _ | .pgSt per _ | .rwSt per _ => some (if per = .prime then 0 else 1)
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    some (if per = .prime ∧ v = false then 0 else 1)
  | .word sk | .down sk | .up sk _ | .total sk => some (if sk.late then 1 else 0)
  | .vote l | .pre l | .tiles l => some (if l then 1 else 0)
  | .setmax | .q0 | .q1 | .uk => some 0
  | _ => none

/-- The sites at which the parity register is the next poll's. -/
def qpLive : Site → Bool
  | .vote l | .pre l | .tiles l => l
  | .dw _ | .dq => true
  | _ => false

/-- The sites whose step may write the register. -/
def qpWr : Site → Bool
  | .total _ | .tiles _ => true
  | _ => false

theorem qpWr_wr {s : Site} (h : qpWr s = false) : wr s .qp = false := by
  cases s <;> simp_all [qpWr, wr]

def qpChk (b : Bool) (s s' : Site) : Bool :=
  b || (
    let t := if tag s s' = .acq 24 then 1 else 0
    (match qCnt s' with
      | none => true
      | some c => match qCnt s with | none => false | some c0 => c == c0 + t) &&
    (!qpLive s' || t == 0) && (qpWr s || !qpLive s' || qpLive s))

theorem qp_self : AllSites fun s => qpChk false s s = true := by unfold AllSites; decide +kernel

theorem qp_edges : Edges qpChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def QPar (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  w = 14 → (∀ c, qCnt dn.1.site = some c → dn.2 (.acquire (bl L g 24)) = c) ∧
    (qpLive dn.1.site = true →
      dn.1.v.qp = BitVec.ofNat 64 ((dn.2 (.acquire (bl L g 24)) + 1) % 2))

variable {p : Params} {L : Launch} {g w : Nat}

/-- A successor of a scan's end: the register is `1 - late` where it is live. -/
def QLive (late : Bool) (s : Site) (v : V) : Prop :=
  qpLive s = true → v.qp = BitVec.ofNat 64 (if late then 0 else 1)

theorem scanExit_live {late : Bool} {d : D} {gx cur : BitVec 64} :
    QLive late (scanExit p late d gx cur).site (scanExit p late d gx cur).v := by
  refine ite_ind (P := QLive late) ?_ ?_ <;> intro h <;> cases late <;>
    first | rfl | simp [qpLive] at h

theorem loopHead_live {late : Bool} {d : D} {grp acc : BitVec 64} :
    QLive late (loopHead p L g late d grp acc).site (loopHead p L g late d grp acc).v := by
  refine ite_ind (P := QLive late) scanExit_live (ite_ind (P := QLive late) ?_ ?_) <;>
    intro h <;> simp [qpLive] at h

theorem afterTotal_live {k : Scan} {d : D} {x : BitVec 64} :
    QLive k.late (afterTotal p L g k d x).site (afterTotal p L g k d x).v := by
  cases k
  · exact ite_ind (P := QLive false) scanExit_live loopHead_live
  · exact ite_ind (P := QLive false) loopHead_live scanExit_live
  · exact ite_ind (P := QLive true) scanExit_live loopHead_live
  · exact ite_ind (P := QLive true) loopHead_live scanExit_live

theorem qp_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D}
    (hn : succ p L g w dn.1 e = some (some d'))
    (hm : Move L g w dn e d') (h : QPar L g w dn) :
    QPar L g w (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  intro hw
  obtain ⟨h1, h2⟩ := h hw
  simp only at h1 h2 hn ⊢
  have hn14 : not14 w = false := by subst hw; rfl
  have hc : qpChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · rw [h', hn14]
      exact AllSites.ok qp_self d.site
    · exact qp_edges.ok h'
  rw [hn14] at hc
  simp only [qpChk, Bool.false_or, Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c3⟩, c2⟩ := hc
  have hb : Code.bump (cls L g) n e (.acquire (bl L g 24)) = n (.acquire (bl L g 24)) +
      if tag d.site d'.site = .acq 24 then 1 else 0 := by
    rw [bump_tag hm]
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
        Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
    case acqRing δ =>
      have hne : ¬ 56 + 8 * ((n .commit + δ) % 3) = 24 := by omega
      simp [hne]
  rw [hb]
  refine ⟨fun c hc' => ?_, fun hl => ?_⟩
  · rw [hc'] at c1
    simp only at c1
    cases h0 : qCnt d.site with
    | none => simp [h0] at c1
    | some c0 =>
      rw [h0] at c1
      rw [h1 c0 h0]
      exact (beq_iff_eq.mp c1).symm
  rw [hl] at c3 c2
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq, Bool.or_false] at c3 c2
  rw [c3, Nat.add_zero]
  by_cases hwr : qpWr d.site = true
  swap
  · have hwf : qpWr d.site = false := by simpa using hwr
    rw [hwf, Bool.false_or] at c2
    have hk : d'.v.qp = d.v.qp := hm.keep .qp (qpWr_wr hwf)
    rw [hk]
    exact h2 c2
  obtain ⟨site, v, kk⟩ := d
  cases site <;> simp only [qpWr, Bool.false_eq_true] at hwr
  case total k =>
    have hcnt := h1 _ (show qCnt (.total k) = some (if k.late then 1 else 0) from rfl)
    rw [hcnt]
    have hL : QLive k.late d'.site d'.v := by
      obtain ⟨pc, kd⟩ := e
      simp only [succ] at hn
      split at hn
      · rename_i val _ _
        cases val <;> simp only [word32] at hn
        all_goals (try split at hn)
        all_goals first
          | (simp only [Option.some.injEq] at hn; subst hn; exact afterTotal_live)
          | (simp only [Option.some.injEq, reduceCtorEq] at hn)
      · simp at hn
    rw [hL hl]
    cases k.late <;> rfl
  case tiles late =>
    have hcnt := h1 _ (show qCnt (.tiles late) = some (if late then 1 else 0) from rfl)
    rw [hcnt]
    obtain ⟨pc, kd⟩ := e
    simp only [succ] at hn
    split at hn
    swap
    · simp at hn
    split at hn
    swap
    · simp at hn
    cases late
    · simp only [Bool.false_eq_true, ↓reduceIte, afterTiles, Option.map_eq_some_iff] at hn
      obtain ⟨d1, hd, hn⟩ := hn
      simp only [Option.some.injEq] at hn
      subst hn
      split at hd
      swap
      · cases hd
      split at hd
      swap
      · cases hd
      simp only [Option.some.injEq] at hd
      subst hd
      exact ite_ind (P := QLive false) (fun h => by simp [qpLive] at h) (fun _ => rfl) hl
    · simp only [↓reduceIte, Option.some.injEq] at hn
      subst hn
      have := h2 rfl
      rw [hcnt] at this
      exact this

/-- **The drain's parity** at every state of a loader lane. -/
theorem q_par {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : QPar L g (wOf b) (d, LdWarp.lcn n) :=
  LdWarp.count_at (I := fun w dn _ => QPar L g w dn) (c := fun _ => false)
    (fun _ h => by cases h)
    (fun b _ => ⟨fun c h => by simpa [qCnt] using h, fun h => by simp [qpLive] at h⟩)
    (fun _ _ _ _ _ _ _ _ _ hn hm h => qp_step hn hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
