-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.MaxSum
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Region

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data

/-- The score-ready poll, the four P stores and the factor store of a round. -/
inductive Marker where
  | start (r : Rd)
  | pack (r : Rd) (q : Fin 4)
  | factor (plain : Bool)
  deriving DecidableEq

def Marker.round : Marker → Rd
  | .start r | .pack r _ => r
  | .factor b => if b then .plain else .bias

def Marker.site : Marker → Site
  | .start r => .ws r
  | .pack r q => .pst r q
  | .factor b => .stat b

def Marker.region (m : Marker) (s : Site) : Bool :=
  decide (m.site.pos < s.pos ∧ s.pos ≤ (Site.pwend m.round).pos)

def Marker.view : Marker → V → V
  | .start _, v => { mf := v.mf, mr := v.mr, rs := v.rs }
  | _, v => v

def Site.tail : Site → Bool
  | .stat .. | .narr .. | .pst .. | .pwst .. | .parr .. | .pws .. | .pel .. | .parr2 .. => true
  | _ => false

private theorem tail_same {p L g d d' e} (tail : Site.tail d.site = true)
    (h : succ p L g d e = some (some d')) : d'.v = d.v := by
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | pst r q =>
    cases r <;> (match q with | 0 | 1 | 2 | 3 => ?_) <;> sc_split <;> rfl
  | stat _ | narr _ | pwst _ _ | parr _ | pws _ | pel _ | parr2 _ => sc_split <;> rfl
  | _ => cases tail

theorem Marker.cut (m : Marker) (b : Bool) :
    Values.entersOnly m.region (· == m.site) b = true ∧ m.region (.pwend m.round) = true := by
  cases m with
  | start r => cases r <;> revert b <;> decide +kernel
  | pack r q => cases r <;> revert q b <;> decide +kernel
  | factor z => cases z <;> revert b <;> decide +kernel

private theorem table (m : Marker) : allSites.all (fun s =>
    (!m.region s || pollOff s != 80) &&
    (!(m.region s || s == m.site) || (match m with
    | .start _ => !s.special
    | _ => Site.tail s) || s == .pwend m.round) &&
    (!(s == .pwend m.round) || [false,true].all (fun b => (nexts b s).all (!m.region ·)))) =
      true := by
  cases m with
  | start r => cases r <;> decide +kernel
  | pack r q => cases r <;> revert q <;> decide +kernel
  | factor z => cases z <;> decide +kernel

theorem Marker.off (m : Marker) {s : Site} (hr : m.region s = true) : pollOff s ≠ 80 := by
  have tab := List.all_eq_true.mp (table m) s (mem_allSites _)
  simp only [Bool.and_eq_true] at tab
  have eq := tab.1.1
  simpa only [hr,Bool.not_true,Bool.false_or,bne_iff_ne] using eq

/-- Loads may change local operands after the starting poll. The running statistics persist.
After the factor or a P store, all fields persist through the closing poll. -/
theorem Marker.frame (m : Marker) {p L g d d' e} (hn : succ p L g d e = some (some d'))
    (prev : m.region d.site = true ∨ d.site = m.site) (dst : m.region d'.site = true) :
    m.view d'.v = m.view d.v := by
  have tab := List.all_eq_true.mp (table m) d.site (mem_allSites _)
  simp only [Bool.and_eq_true] at tab
  obtain ⟨⟨_,ok⟩,closed⟩ := tab
  have mem : (m.region d.site || d.site == m.site) = true := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using prev
  simp only [mem,Bool.not_true,Bool.false_or,Bool.or_eq_true,beq_iff_eq] at ok
  rcases ok with regular | last
  · cases m with
    | start r =>
      rcases succ_stats hn with ⟨hf,hm,hs⟩ | ⟨r',site,_⟩
      · simp only [Marker.view,hf,hm,hs]
      · rw [site] at regular; cases regular
    | pack r q => exact tail_same regular hn
    | factor z => exact tail_same regular hn
  · rcases succ_cases hn with ⟨_,same,_⟩ | move
    · rw [same]
    · simp only [last,beq_self_eq_true,Bool.not_true,Bool.false_or] at closed
      have no := List.all_eq_true.mp (List.all_eq_true.mp closed (lz L g)
        (by cases lz L g <;> simp)) d'.site (last ▸ move.1)
      rw [dst] at no; cases no

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
