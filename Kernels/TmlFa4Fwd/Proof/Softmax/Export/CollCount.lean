-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.CollKind
public import Kernels.TmlFa4Fwd.Proof.Lib.StartColl
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.Start0
import Kernels.TmlFa4Fwd.Proof.Lib.CountRef
import Kernels.TmlFa4Fwd.Proof.SmWarp.P2Count
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Places
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warp collectives of the softmax warps

Besides the scheduler's shuffles and ballots, a softmax lane makes a warp barrier and an election in
every round, after its P-full arrival; a lane of warp 0 makes the startup's sixteen elections. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (nexts lz allSites mem_allSites)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The softmax warps' sites whose event is a warp collective. -/
def Softmax.Site.wcoll : Softmax.Site → Bool
  | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .pws _ | .pel _ => true
  | _ => false

/-- **The kind of a softmax event.** -/
theorem soft_ev_kind {d : Softmax.D} {e : Event} (hev : Softmax.EvS p L g d e) :
    CollKindW e.kind d.site.wcoll := by
  obtain ⟨hev, hub⟩ := hev
  obtain ⟨s, v, kk, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  case down | up | total | pre | tiles => exact .inl (epi_kind hev (by simp [Softmax.Site.toE]) hub)
  case vote => obtain ⟨_, h⟩ := hev; rw [h]; exact .inl (.vote _ _ _ (by norm_num))
  case setmax => obtain ⟨_, _, _, h⟩ := hev; rw [h]; exact .inl (.setMax _ _ _)
  case bar1 | bsync | narr | finarr => rw [hev]; exact .inl (.bar _ _ _)
  case barEnd =>
    rcases hev with h | ⟨f, h⟩
    · rw [h]; exact .inl (.bar _ _ _)
    · exact absurd h (hub f)
  case wq | ws | wb | pwend | wend => obtain ⟨_, h⟩ := hev; rw [h]; exact .inl (.wait _ _ _ _ _)
  case barr | parr | parr2 => rw [hev]; exact .inl (.arrive _ _ _ _ _)
  case word | q0 | q1 | uk | bld =>
    rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .inl (.rd _ _)
    · exact absurd h (hub f)
  case sld =>
    rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .inl (.tc _)
    · exact absurd h (hub f)
  case sldw =>
    split at hev
    · rcases hev with h | ⟨f, h⟩
      · rw [h]; exact .inl (.tc _)
      · exact absurd h (hub f)
    · rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
      · rw [h]; exact .inl (.tc _)
      · exact absurd h (hub f)
  case pst =>
    split at hev
    · rw [hev]; exact .inl (.tc _)
    · rcases hev with ⟨_, _, _, h⟩ | ⟨f, h⟩
      · rw [h]; exact .inl (.tc _)
      · exact absurd h (hub f)
  case pwst =>
    rcases hev with h | ⟨f, h⟩
    · rw [h]; exact .inl (.tc _)
    · exact absurd h (hub f)
  case stat | fin =>
    rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .inl (.wr _ _)
    · exact absurd h (hub f)
  case fence => obtain ⟨_, _, h⟩ := hev; rw [h]; exact .inl (.fenceProxy _ _)
  case pws =>
    rcases hev with ⟨_, h⟩ | ⟨f, h⟩
    · rw [h]; exact .inr ⟨⟨_, _, rfl⟩, rfl⟩
    · exact absurd h (hub f)
  case pel =>
    rcases hev with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · rw [h]; exact .inl (.elect _ _ _)
    · exact absurd h (hub f)
  case exit => rw [hev]; exact .inl .exit

/-- The round's collective sites. -/
def Softmax.Site.rcoll : Softmax.Site → Bool
  | .pws _ | .pel _ => true
  | _ => false

/-- A softmax event that is an election or a warp barrier is at the round's collective sites. -/
theorem soft_roundColl {d : Softmax.D} {e : Event} (hev : Softmax.EvS p L g d e) :
    roundColl e = d.site.rcoll := by
  obtain ⟨hev, hub⟩ := hev
  obtain ⟨s, v, kk, acc⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals (try simp only [Epilogue.Ev, Softmax.Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals first
    | (subst_vars; rfl)
    | exact absurd rfl (hub _)

/-- The round's collectives a site has to come after its P-full arrival. -/
def Softmax.Site.rem : Softmax.Site → Nat
  | .pst _ q => if q.val = 3 then 2 else 0
  | .pwst _ c => if c.val = 1 then 2 else 0
  | .pws _ => 2
  | .pel _ => 1
  | _ => 0

/-- How a move from `s` changes `rem`. -/
private def remOk (s s' : Softmax.Site) : Bool :=
  match s with
  | .parr _ => s'.rem == 2
  | .pws _ => s'.rem == 1
  | .pel _ => s'.rem == 0
  | _ => s'.rem == s.rem

private theorem rem_moves : [false, true].all (fun lz =>
    allSites.all fun s => (nexts lz s).all (remOk s)) = true := by decide +kernel

private theorem rem_move {b : Bool} {s s' : Softmax.Site} (h : s' ∈ nexts b s) :
    remOk s s' = true := by
  have h1 := List.all_eq_true.mp rem_moves b (by cases b <;> simp)
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 s (mem_allSites s)) s' h

private theorem remOk_eq {s s' : Softmax.Site} (h : remOk s s' = true)
    (hp : ¬ ∃ r, s = .parr r) : (if s.rcoll then 1 else 0) + s'.rem = s.rem := by
  cases s <;> first
    | exact absurd ⟨_, rfl⟩ hp
    | (simp only [remOk, beq_iff_eq] at h
       rw [h]
       first | rfl | simp [Softmax.Site.rcoll])

/-- **The relation at a thread state** of warp `w`. -/
def CollInv (p : Params) (L : Launch) (w g : Nat) : (thread p L g).D → Nat → Prop
  | (.inl s, _), n => n = startCnt w s.site
  | (.inr ⟨.softmax, d⟩, nn), n => n + d.site.rem = startEl w + 2 * nn (.soft (.arrive 96))
  | _, _ => True

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X)
  (hg : g < L.threads) {w : Nat} (hw8 : w < 8) (hw : Prologue.warpIndex L g = w)
include hp hX hub hg hw8 hw

/-- **The elections and warp barriers of a softmax lane.** -/
theorem soft_coll_inv : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
    CollInv p L w g σ (((X.tr g).take k).countP roundColl) := by
  refine countRef (J := SmWarp.Ref p L w) (fun k => SmWarp.good hp hX hw8 hg hw k) roundColl
    (P := CollInv p L w g) rfl ?_
  rintro k ⟨σ, nn⟩ e ⟨σ', nn'⟩ n he hσ hJ hB hn hJ'
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ with s | ⟨i, d⟩
  · obtain ⟨hS, -, hZ⟩ := hJ
    have hev := (start_fired hp hX he hσ).1
    simp only [CollInv] at hB
    simp only [glued, Code.glue, Startup.code] at h1
    cases hsu : Startup.succ L g s e with
    | none => rw [hsu] at h1; simp at h1
    | some o =>
      cases o with
      | none => rw [hsu] at h1; simp at h1
      | some s' =>
        rw [hsu] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        have hz : w ≠ 0 → roundColl e = false := fun h0 => by
          simp only [SmWarp.StartW, h0, ite_false] at hS
          obtain ⟨pc, kind⟩ := e
          obtain ⟨site, x1, x2, x3⟩ := s
          cases site <;> simp only [StartAt] at hS
          case sh j =>
            fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, h⟩ := hev <;>
              subst h <;> rfl
          case fence => simp only [Startup.Ev] at hev; subst hev; rfl
          case bar => simp only [Startup.Ev] at hev; subst hev; rfl
        unfold Code.enter at hJ' ⊢
        split
        · -- the role
          rename_i r hx
          have hbar : s.site = .bar := by
            obtain ⟨site', y1, y2, y3⟩ := s'
            cases site' with
            | enter r' => exact bar_of_enter hsu rfl
            | _ => simp [exit] at hx
          have hk : e.kind = .bar 0 none .sync := by
            simpa only [Startup.Ev, hbar] using hev
          have hr0 : roundColl e = false := by
            obtain ⟨pc, kd⟩ := e
            simp only at hk
            subst hk
            rfl
          rw [hbar] at hB
          cases r <;> first
            | trivial
            | (simp only [CollInv, hr0, hB]
               have ha : Code.bump (cls L g) nn e (.soft (.arrive 96)) = 0 := by
                 obtain ⟨pc, kd⟩ := e
                 simp only at hk
                 subst hk
                 simp [Code.bump, cls, Softmax.cls, hZ (.arrive 96)]
               rw [ha]
               rfl)
        · -- the startup goes on
          rename_i hx
          simp only [hx] at hJ'
          simp only [CollInv]
          rw [hB]
          by_cases h0 : w = 0
          · subst h0
            exact (startCnt_step0 hS hev hne hsu hJ'.1).symm
          · rw [cnt_ne h0, cnt_ne h0, hz h0]
            rfl
  · cases i with
    | softmax =>
      have hr := hn
      change (thread p L g).next (SmWarp.sinj p L g d nn) e = _ at hr
      rw [SmWarp.next_sinj] at hr
      obtain ⟨o, ho, hm⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨d1, rfl, hd1⟩ := Option.map_eq_some_iff.mp hm
      obtain rfl := congrArg Prod.fst hd1
      have hev := (SmWarp.fired_soft hp hX he hσ hne).1
      have hpl := Softmax.Control.succ_places (d := d) ho
      have hw' : g % L.block / 32 < 8 := by rw [show g % L.block / 32 = w from hw]; exact hw8
      have h96 := soft_arr96 hw' hev.1
      have hrc := soft_roundColl hev
      simp only [CollInv] at hB ⊢
      simp only [Code.bump]
      have h0 : (¬ ∃ r, d.site = .parr r) → cls L g (.soft (.arrive 96)) e = false :=
        fun h => Bool.eq_false_iff.mpr fun hc => h (h96.mp hc)
      rcases hpl with ⟨hs', hno⟩ | hM
      · have hq : roundColl e = false ∧ cls L g (.soft (.arrive 96)) e = false := by
          obtain ⟨pc, kd⟩ := e
          rcases hno with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨hd, -⟩
          · simp only at hk
            subst hk
            exact ⟨rfl, by simp [cls, Softmax.cls]⟩
          · simp only at hk
            subst hk
            exact ⟨rfl, by simp [cls, Softmax.cls]⟩
          · have hd' : d.site.delayed = true := hd
            refine ⟨?_, h0 ?_⟩
            · rw [hrc]
              change d.site.rcoll = false
              revert hd'
              cases d.site <;> simp [Softmax.Site.delayed, Softmax.Site.rcoll]
            · revert hd'
              cases d.site <;> simp [Softmax.Site.delayed]
        rw [hq.1, hq.2]
        change d1.site = d.site at hs'
        rw [hs']
        simpa using hB
      · have hmv := rem_move hM.1
        change remOk d.site d1.site = true at hmv
        change roundColl e = d.site.rcoll at hrc
        rw [hrc]
        change _ ↔ ∃ r, d.site = .parr r at h96
        by_cases hp' : ∃ r, d.site = .parr r
        · rw [h96.mpr hp']
          obtain ⟨r, hp'⟩ := hp'
          rw [hp'] at hmv hB ⊢
          simp only [remOk, beq_iff_eq] at hmv
          simp only [Softmax.Site.rem] at hB
          simp only [hmv, Softmax.Site.rcoll, Bool.false_eq_true, ite_true, ite_false]
          omega
        · rw [h0 hp']
          have hp2 : ¬ ∃ r, d.scheduler.site = .parr r := hp'
          have this := remOk_eq hmv hp2
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          change (if d.site.rcoll then 1 else 0) + d1.site.rem = d.site.rem at this
          omega
    | _ => exact hJ.elim

omit hp hX hub hg hw8 hw in
private theorem start_coll_kind {s : Startup.D} {n : Cls → Nat} {e : Event}
    (hS : SmWarp.StartW L w s n) (hev : Startup.Ev L g s e) (hub : ∀ f, e.kind ≠ .ub f) :
    CollKindW e.kind (match s.site with | .sh _ | .elect _ => true | _ => false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, h⟩ := hev <;> subst h <;>
      exact .inl (.shfl _ _ _ _ _ _)
  | fence => simp only [Startup.Ev] at hev; subst hev; exact .inl .fenceInit
  | bar => simp only [Startup.Ev] at hev; subst hev; exact .inl (.bar _ _ _)
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · subst h; exact .inl (.elect _ _ _)
    · exact absurd h (hub f)
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
    · subst h; exact .inl (.mbInit _ _)
    · exact absurd h (hub f)
  | enter r =>
    exfalso
    unfold SmWarp.StartW at hS
    split at hS <;> simp [StartAt0, StartAt] at hS

/-- Whether a thread state of a softmax warp is at a collective site. -/
def softAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Bool :=
  match σ with
  | (.inl s, _) => match s.site with | .sh _ | .elect _ => true | _ => false
  | (.inr ⟨.softmax, d⟩, _) => d.site.wcoll
  | _ => false

/-- **An event of a softmax warp** is a warp collective exactly at a collective site, and is a
shuffle, a full ballot, an election or a warp barrier. -/
theorem soft_event_coll {k : Nat} {σ : (thread p L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Sched.isWarpColl e = softAt p L g σ ∧ (if Sched.isWarpColl e then 1 else 0) =
      (if isColl e then 1 else 0) + (if roundColl e then 1 else 0) := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  have hR := (SmWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · exact (start_coll_kind hR.1 (start_fired hp hX he hσ).1 hne).counts
  · exact (soft_ev_kind (SmWarp.fired_soft hp hX he hσ hne).1).counts

/-- **The collectives before a state of a softmax warp.** -/
theorem soft_cnt_eq {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ((X.tr g).take k).countP Sched.isWarpColl =
      σ.2 .shfl + σ.2 .vote + ((X.tr g).take k).countP roundColl := by
  have h1 : ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take k).countP isColl + ((X.tr g).take k).countP roundColl := by
    clear hσ
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.take_add_one]
      cases he : (X.tr g)[k]? with
      | none => simpa using ih
      | some e =>
        have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := fun pc f hf =>
          hub ⟨(g, k), pc, f, show (X.tr g)[k]? = _ by rw [he, hf]⟩
        obtain ⟨σ', hσ', -⟩ := good_state hp hX (show X.get (g, k) = some e from he) hne
          (SmWarp.good hp hX hw8 hg hw k)
        have := (soft_event_coll hp hX hub hg hw8 hw (show X.get (g, k) = some e from he) hσ').2
        simp only [Option.toList_some, List.countP_append, List.countP_singleton]
        omega
  obtain ⟨hs, hv⟩ := counts hσ
  rw [h1, countColl, hs, hv]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
