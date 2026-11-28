-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.ElectCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open Prologue.Control

/-- The two startup syncs are followed by one setup sync, then five
rendezvous per preloaded block. Query loads and elected lanes do not affect it. -/
def preloadPosition (p : Nat) : Site → Nat
  | .sMax | .ld _ | .el _ | .init _ | .fnc0 | .bar2 => 2
  | .pb b j => 3+5*b.val+j.val
  | .arr b | .lb b 0 => 3+5*b.val+1
  | .psh b => 3+5*b.val+2
  | .lb b 1 => 3+5*b.val+3
  | .pel b j | .ptc b j => 3+5*b.val+2+j.val
  | _ => 3+5*p

def preloadSync : Site → Bool
  | .pb .. | .bar2 => true
  | _ => false

/-- Shuffles of the prologue before the site: one per preloaded block, taken at `psh`. -/
def shflPosition (p : Nat) : Site → Nat
  | .sMax | .ld _ | .el _ | .init _ | .fnc0 | .bar2 => 0
  | .pb b j => b.val+(if 2≤j.val then 1 else 0)
  | .arr b | .lb b 0 | .psh b => b.val
  | .lb b 1 | .pel b _ | .ptc b _ => b.val+1
  | _ => p

def Site.isShuffle : Site → Bool
  | .psh _ => true
  | _ => false

/-- Rendezvous, shuffles and elections before the site. -/
def prePosition (p : Nat) (s : Site) : Nat × Nat × Nat :=
  (preloadPosition p s,shflPosition p s,electPosition p s)

private theorem query_pos (t d k p) : prePosition p (querySite t d k)=(3+5*p,p,12+4*p) := by
  unfold querySite
  split_ifs <;> rfl

private theorem copy_pos {n p} (t d b j) (cap : min 3 n=p) (lt : b.val<n) :
    prePosition p (afterCopy d t n b j)=(3+5*b.val+2+j.val,b.val+1,12+4*b.val+j.val+1) := by
  fin_cases j
  all_goals try rfl
  fin_cases b <;> simp only [afterCopy] <;> split_ifs
  all_goals first | rfl | (rw [query_pos]; dsimp only at lt ⊢; simp only [Prod.mk.injEq]; omega)

private theorem query_advance (t d p j) : prePosition p (afterQuery d t j)=(3+5*p,p,12+4*p) := by
  unfold afterQuery
  split_ifs <;> first | rfl | exact query_pos ..

private theorem store_advance (i j p) :
    prePosition p (Control.afterStore i j)=(3+5*p,p,12+4*p) := by
  unfold Control.afterStore
  split_ifs <;> rfl

theorem preload_pair_next {Q L g d dn ev p} (move : Control.next Q L g d ev=some (some dn))
    (cap : 180≤d.site.pc → min 3 (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)=p)
    (gate : OpenBlock d (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)) :
    prePosition p dn.site=(preloadPosition p d.site+(preloadSync d.site).toNat,
      shflPosition p d.site+d.site.isShuffle.toNat,
      electPosition p d.site+d.site.isElect.toNat) := by
  obtain ⟨s,f,l,q,e,b⟩ := d
  cases s with
  | ld j =>
    fin_cases j <;> simp only [Control.next] at move <;> split at move <;> cases move <;> rfl
  | el j | init j =>
    simp only [Control.next] at move
    repeat' split at move
    all_goals cases move
    all_goals first | rfl | (unfold afterInit; split <;> first | rfl | (
      have := j.isLt
      simp [prePosition, preloadPosition, shflPosition, electPosition, preloadSync,
        Site.isShuffle, Site.isElect]
      omega))
  | bar2 =>
    simp only [Control.next] at move
    split at move <;> cases move
    · rw [query_pos]
      have value := cap (by change 180≤180; decide)
      simp_all [preloadPosition,preloadSync,shflPosition,Site.isShuffle,electPosition,Site.isElect]
      omega
    · rfl
  | pb b j => fin_cases j <;> simp only [Control.next] at move <;> repeat' split at move
              all_goals cases move
              all_goals rfl
  | lb b j => fin_cases j <;> cases move <;> rfl
  | pel b j | ptc b j =>
    have big : ∀ b j, 180≤pelPc b j ∧ 180≤ptcPc b j := by decide +kernel
    have bound := gate b rfl
    have known := cap (by first | exact (big b j).1 | exact (big b j).2)
    simp only [Control.next] at move
    repeat' split at move
    all_goals cases move
    all_goals first | rfl | exact copy_pos _ _ _ _ known bound
  | ldq j => cases move; exact query_advance ..
  | stq i j => cases move; exact store_advance ..
  | st9 j => fin_cases j <;> cases move <;> rfl
  | exit => cases move
  | _ => cases move; rfl

theorem preload_sync_next {Q L g d dn ev p} (move : Control.next Q L g d ev=some (some dn))
    (cap : 180≤d.site.pc → min 3 (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)=p)
    (gate : OpenBlock d (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)) :
    preloadPosition p dn.site=preloadPosition p d.site+(preloadSync d.site).toNat :=
  congrArg Prod.fst (preload_pair_next move cap gate)

theorem preload_shfl_next {Q L g d dn ev p} (move : Control.next Q L g d ev=some (some dn))
    (cap : 180≤d.site.pc → min 3 (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)=p)
    (gate : OpenBlock d (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)) :
    shflPosition p dn.site=shflPosition p d.site+d.site.isShuffle.toNat :=
  congrArg (·.2.1) (preload_pair_next move cap gate)

theorem elect_next {Q L g d dn ev p} (move : Control.next Q L g d ev=some (some dn))
    (cap : 180≤d.site.pc → min 3 (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)=p)
    (gate : OpenBlock d (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)) :
    electPosition p dn.site=electPosition p d.site+d.site.isElect.toNat :=
  congrArg (·.2.2) (preload_pair_next move cap gate)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
