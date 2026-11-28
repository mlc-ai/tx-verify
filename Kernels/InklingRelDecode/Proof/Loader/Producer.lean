-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Time
public import Kernels.InklingRelDecode.Proof.Loader.RefNext
import Lemmas.Flow.Arith32Word
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

/-- The arrival is issued by lane zero. Each of the eight copy instructions is
issued by the election winner for its pair. -/
inductive Issue where
  | arrival
  | copy (pair : Fin 4) (second : Bool)
  deriving DecidableEq

def Issue.site : Issue → Site
  | .arrival => .arrive
  | .copy p b => .copy p b

def Issue.slot (op : Issue) (r : Nat) := slotTime r + op.site.position

def Issue.before (op : Issue) (r : Nat) (d : D) :=
  match d.site with
  | .dec | .first | .second | .beginBar => True
  | .endBar | .inc | .dispatch => False
  | s => (bits d.counter).toNat < r ∨
      ((bits d.counter).toNat=r ∧ s.position≤op.site.position)

theorem Issue.early {op : Issue} {r d} (h : op.before r d) : time d ≤ op.slot r := by
  obtain ⟨s,i,n,a,b⟩ := d
  have pos := position_bound s
  cases s <;> simp only [before,time,slot,slotTime,Lib.Slots.enter,Lib.Slots.reuse,
    Lib.Slots.frame,Lib.Slots.stride] at * <;> omega

theorem Issue.at_slot {op : Issue} {r d} (early : op.before r d) (hit : time d=op.slot r) :
    d.site=op.site ∧ (bits d.counter).toNat=r := by
  have uniquePos (s : Site) :
      s.position=op.site.position → s=op.site := by
    clear early hit
    cases op with
    | arrival => cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    | copy p b => revert p b; cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨s,i,n,a,b⟩ := d
  have pos := position_bound s
  have target := position_bound op.site
  by_cases loop : s.inLoop
  · have h : time ⟨s,i,n,a,b⟩=slotTime (bits i).toNat+s.position := by
      cases s <;> first | rfl | cases loop
    rw [h] at hit
    simp only [slot,slotTime,Lib.Slots.frame,Lib.Slots.stride] at hit
    change s=op.site ∧ (bits i).toNat=r
    exact ⟨uniquePos s (by omega),by omega⟩
  · cases s <;> simp only [Site.inLoop] at loop <;> try contradiction
    all_goals simp only [before,time,slot,slotTime,Lib.Slots.frame,Lib.Slots.stride,
      Lib.Slots.enter,Lib.Slots.reuse] at early hit; omega

private theorem finish_earlier {op : Issue} {r j hi s a b} (p : Fin 4)
    (jj : j<r) (rh : r<hi) (lim : hi<2^31) :
    op.before r (finishPair ⟨s,b32 j,b32 hi,a,b⟩ p) := by
  have num : (bits (b32 j)).toNat=j := by
    rw [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  fin_cases p
  all_goals dsimp only [finishPair]
  all_goals try (apply Or.inl; change (bits (b32 j)).toNat<r; rwa [num])
  rw [bits_b32 (by omega : j<2^32),bits_b32 (by omega : hi<2^32)]
  have inc : truncBits 32 (BitVec.ofNat 64 j + 1) = BitVec.ofNat 64 (j+1) := by
    change Arith32.r32 (BitVec.ofNat 64 j + BitVec.ofNat 64 1)=_
    rw [←BitVec.ofNat_add]
    exact Arith32.r32_W (by omega)
  have diff : BitVec.ofNat 64 (j+1) ≠ BitVec.ofNat 64 hi := by
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j+1<2^64),
      Nat.mod_eq_of_lt (by omega : hi<2^64)] at h
    omega
  rw [inc,ite_eq_right_iff.mpr (fun eq => (diff eq).elim)]
  change (bits (b32 (j+1))).toNat<r ∨ ((bits (b32 (j+1))).toNat=r ∧ 0≤_)
  rw [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

def Issue.producer (op : Issue) (L : Launch) (g : Nat) (e : Event) : Prop :=
  match op with
  | .arrival => laneOf L g=0
  | .copy .. => ∀ mask inst lead, e.kind=.elect mask inst lead → laneOf L g=lead

private def arriveNext (zero : Bool) := if zero then Site.arrive else Site.page false

private def afterPair (p : Fin 4) : Site :=
  match p.val with
  | 0 => .warpBar 1
  | 1 => .page true
  | 2 => .warpBar 3
  | _ => .poll

/-- The twelve positions at which a packet can branch are finite. Crossing a
producer position in its own iteration requires executing its instruction. -/
private def edgeOk (op : Issue) (s t : Site) :=
  s.position≤op.site.position → s≠op.site → t.position≤op.site.position

private theorem packet_edges (op : Issue) :
    edgeOk op .poll .readyBar ∧ edgeOk op .arrive (.page false) ∧
    (∀ p, edgeOk op (.warpBar p) (.elect p)) ∧
    (∀ p, edgeOk op (.elect p) (.copy p false)) ∧
    (∀ p, edgeOk op (.copy p false) (.copy p true)) ∧
    (∀ b, edgeOk op (.page b) (.warpBar (if b then 2 else 0))) ∧
    (∀ zero, (op=.arrival → zero=true) → edgeOk op .readyBar (arriveNext zero)) ∧
    (∀ p, edgeOk op (.copy p true) (afterPair p)) ∧
    (op=.arrival → ∀ p, edgeOk op (.elect p) (afterPair p)) := by
  unfold edgeOk
  cases op with
  | arrival => (repeat' apply And.intro) <;> decide
  | copy p b => (repeat' apply And.intro) <;> revert p b <;> decide +kernel

private theorem advance {op : Issue} {r d} {s : Site} (old : d.site.inLoop)
    (dest : s.inLoop) (before : op.before r d)
    (miss : d.site=op.site → (bits d.counter).toNat≠r)
    (edge : edgeOk op d.site s) : op.before r {d with site := s} := by
  have eq (d : D) (loop : d.site.inLoop) : op.before r d ↔
      (bits d.counter).toNat<r ∨ ((bits d.counter).toNat=r ∧ d.site.position≤op.site.position) := by
    obtain ⟨s,i,n,a,b⟩ := d; cases s <;> first | rfl | cases loop
  apply (eq _ dest).mpr
  rcases (eq d old).mp before with lo|⟨pos,h⟩
  · exact .inl lo
  · exact .inr ⟨pos,edge h (fun site => miss site pos)⟩

private theorem finish_step {op : Issue} {d lo hi r} (p : Fin 4)
    (origin : d.site=.copy p true ∨ (d.site=.elect p ∧ op=.arrival))
    (ref : Ref lo hi d) (size : hi<2^31) (rh : r<hi) (before : op.before r d)
    (miss : d.site=op.site → (bits d.counter).toNat≠r) :
    op.before r (finishPair d p) := by
  obtain ⟨s,i,n,a,b⟩ := d
  change s=_ ∨ s=_ ∧ _ at origin
  have loop : s.inLoop := by rcases origin with rfl|⟨rfl,_⟩ <;> rfl
  obtain ⟨j,_,jh,rfl,rfl⟩ := ref_loop ref loop
  have num : (bits (b32 j)).toNat=j := by
    rw [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases lt : j<r
  · exact finish_earlier p lt rh size
  obtain ⟨_,_,_,_,_,_,_,last,skip⟩ := packet_edges op
  have edge : edgeOk op s (afterPair p) := by
    rcases origin with rfl|⟨rfl,arr⟩
    · exact last p
    · exact skip arr p
  have go := advance (d := ⟨s,b32 j,b32 hi,a,b⟩) loop
    (show (afterPair p).inLoop by fin_cases p <;> rfl) before miss edge
  fin_cases p
  · exact go
  · exact go
  · exact go
  · exfalso
    rcases origin with rfl|⟨rfl,rfl⟩
    · change _<r ∨ (_=r ∧ (Site.copy 3 true).position≤op.site.position) at before
      rw [num] at before
      have same : ∀ z : Issue, (Site.copy 3 true).position≤z.site.position →
          Site.copy 3 true=z.site := by
        intro z; cases z with
        | arrival => decide
        | copy p b => revert p b; decide
      exact miss (same _ (before.resolve_left lt).2) (num.trans (before.resolve_left lt).1)
    · change _<r ∨ (_=r ∧ (Site.elect 3).position≤Issue.arrival.site.position) at before
      rw [num] at before
      exact (by decide : ¬ (Site.elect 3).position≤Issue.arrival.site.position)
        (before.resolve_left lt).2

/-- Until the selected instruction fires in block r, the producer remains on
the early side of its slot. The instruction may be selected before the first election. -/
theorem Issue.before_next {op : Issue} {L g lo hi r d dn e} (run : next L g d e=some (some dn))
    (ref : Ref lo hi d) (lim : hi<2^31) (lr : lo≤r) (rh : r<hi) (h : op.before r d)
    (producer : op.producer L g e) (miss : d.site=op.site → (bits d.counter).toNat≠r) :
    op.before r dn := by
  obtain ⟨poll,arr,bar,vote,copy,page,ready,_,_⟩ := packet_edges op
  obtain ⟨s,i,n,a,b⟩ := d
  cases s with
  | dec => cases run; trivial
  | first | second =>
    obtain ⟨_,_,v,_,_,rfl⟩ := read_next run
    trivial
  | page upper =>
    cases upper
    all_goals obtain ⟨_,_,v,_,_,rfl⟩ := read_next run
    · exact advance (by rfl) (by rfl) h miss (page false)
    · exact advance (by rfl) (by rfl) h miss (page true)
  | beginBar =>
    obtain ⟨rfl,rfl⟩ := ref
    simp only [next] at run
    rw [bits_b32 (by omega),bits_b32 (by omega),Arith32.toSigned_W lim,
      Arith32.toSigned_W (by omega : lo<2^31)] at run
    simp only [show ¬(hi : Int)≤lo by omega,↓reduceIte] at run
    cases run
    change (bits (b32 lo)).toNat<r ∨ ((bits (b32 lo)).toNat=r ∧ 0≤_)
    rw [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  | poll =>
    simp only [next] at run
    split at run <;> try contradiction
    cases run
    split
    · exact advance (by rfl) (by rfl) h miss poll
    · exact h
  | readyBar =>
    cases run
    have zero : op=.arrival → decide (laneOf L g=0)=true := by
      rintro rfl; exact decide_eq_true producer
    have edge := ready _ zero
    by_cases z : laneOf L g=0 <;> simp only [z,decide_true,decide_false,arriveNext,
      Bool.false_eq_true,↓reduceIte] at edge ⊢ <;> exact advance (by rfl) (by rfl) h miss edge
  | arrive => cases run; exact advance (by rfl) (by rfl) h miss arr
  | warpBar p => cases run; exact advance (by rfl) (by rfl) h miss (bar p)
  | elect p =>
    simp only [next] at run
    split at run <;> try contradiction
    rename_i mask inst lead kind
    split at run
    · cases run; exact advance (by rfl) (by rfl) h miss (vote p)
    · rename_i lose
      cases run
      have arrival : op=.arrival := by
        cases op with
        | arrival => rfl
        | copy => exact False.elim (lose (producer mask inst lead kind))
      exact finish_step p (.inr ⟨rfl,arrival⟩) ref lim rh h miss
  | copy p b' =>
    cases b' <;> cases run
    · exact advance (by rfl) (by rfl) h miss (copy p)
    · exact finish_step p (.inl rfl) ref lim rh h miss
  | inc | endBar | dispatch => exact False.elim h

end PTX.Kernels.InklingRelDecode.Proof.Loader
