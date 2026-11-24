-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's step spec

What one step of the loader's machine does, stated once for every fact (`Move`, proved by
`step_spec` in `RefNext.lean` with the step proofs of the reference invariant):

* `edge`: the successor's site is the site itself (a failed poll, an address load's first word)
  or one of the literal successors `nexts` (`not14 w` selects warp 15's branches, and warp 15 has
  no TMA group or Q wait).
* `keep`: a field the site does not write (`wr`, a literal table per site family) is unchanged.
* `cnt`: the event's ledger classes are those of the edge's tag (`tag`, a literal table over the
  edges; at most one class per event). A ring slot's class is resolved from the commits: the slot
  of the packet after `c + δ` commits (`acqRing δ`), the slot of the last committed packet (`pub`).

A standalone fact (`Facts/`) proves its preservation from `Move` alone: its site function is
checked against `nexts` and `tag` by evaluation over `allSites`, and the counts move by
`bump_tag`. It never unfolds `succ`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Scan loopOf)

deriving instance DecidableEq for Cnt

/-! ### Fields -/

/-- The fields of a state's values. -/
inductive Fld where
  | sc | ukw | pw | lp | lr | l0 | l1 | x0 | x1 | rnd | slot | par | bq0 | bq1 | qp | len | r56
  | co | su
  deriving DecidableEq

/-- Field `f` is the same in `v` and `v'`. -/
def Fld.same : Fld → V → V → Prop
  | .sc, v, v' => v'.sc = v.sc
  | .ukw, v, v' => v'.ukw = v.ukw
  | .pw, v, v' => v'.pw = v.pw
  | .lp, v, v' => v'.lp = v.lp
  | .lr, v, v' => v'.lr = v.lr
  | .l0, v, v' => v'.l0 = v.l0
  | .l1, v, v' => v'.l1 = v.l1
  | .x0, v, v' => v'.x0 = v.x0
  | .x1, v, v' => v'.x1 = v.x1
  | .rnd, v, v' => v'.rnd = v.rnd
  | .slot, v, v' => v'.slot = v.slot
  | .par, v, v' => v'.par = v.par
  | .bq0, v, v' => v'.bq0 = v.bq0
  | .bq1, v, v' => v'.bq1 = v.bq1
  | .qp, v, v' => v'.qp = v.qp
  | .len, v, v' => v'.len = v.len
  | .r56, v, v' => v'.r56 = v.r56
  | .co, v, v' => v'.co = v.co
  | .su, v, v' => v'.su = v.su

/-- The fields a step from a site may write (per site family). -/
def wr : Site → Fld → Bool
  | .setmax, f | .word _, f | .down _, f | .up _ _, f | .vote _, f | .pre _, f | .q0, f
  | .q1, f => f == .sc
  | .total _, f | .tiles _, f => [Fld.sc, .co, .slot, .par, .qp].contains f
  | .uk, f => [Fld.ukw, .su, .pw].contains f
  | .pgLd _ _, f | .rwSt _ _, f => f == .pw
  | .ptP _ _ _, f => f == .lp
  | .ptR _ _ _, f => f == .lr
  | .ptS _ _ _, f => f == .len
  | .lw _ _ _, f => f == .l0 || f == .l1
  | .xl _ _ _, f => f == .x0
  | .xh _ _ _, f => f == .x1
  | .arrive _ _, f => [Fld.bq0, .bq1, .slot, .par, .r56, .rnd, .pw, .sc].contains f
  | .te _ _, f | .tc _ _, f => [Fld.bq0, .bq1, .rnd, .pw, .sc].contains f
  | _, _ => false

/-! ### Edges -/

/-- A scheduler pass's start. -/
def passNexts (late : Bool) : List Site :=
  if late then [.down .second, .word .second] else [.down .first, .word .first]

/-- After the warm rounds (`afterTail`): the second pass or the steady loop. -/
def tailNexts : List Site := passNexts true ++ [.pgSt .steady 0, .pgLd .steady 0]

/-- After the warm rounds on warp `w` (`afterWarm`): warp 14's last Bias group, or the tail. -/
def warmNexts (n14 : Bool) : List Site := (if n14 then [] else [.tw 6]) ++ tailNexts

/-- After TMA group `t` (`groupEnd`). -/
def groupNexts (t : Fin 7) : List Site :=
  match t.val with
  | 0 => [.tw 1] | 1 => [.tw 2] | 2 => [.tw 3] | 3 => [.slot .prime true] | 4 => [.tw 5]
  | 5 => [.slot .warm true] | _ => tailNexts

/-- **The successors of a site** other than the site itself (`n14`: the warp is not warp 14). -/
def nexts (n14 : Bool) : Site → List Site
  | .setmax => passNexts false
  | .word k => [.down k]
  | .down k => [.up k 0]
  | .up k j => if h : j.val < 4 then [.up k ⟨j.val + 1, by omega⟩] else [.total k]
  | .total k => [.dw 0, .vote k.late, .down (loopOf k.late), .word (loopOf k.late)]
  | .vote l => [.tiles l, .pre l]
  | .pre l => [.tiles l]
  | .tiles l => if l then [.dw 0] else [.q0, .dw 0]
  | .q0 => [.q1]
  | .q1 => [.uk]
  | .uk => [.pgSt .prime 0, .pgLd .prime 0]
  | .pgLd per it => [.pgSt per it]
  | .pgSt per it => [.rwSt per it]
  | .rwSt per it => if it.val = 0 then [.pgSt per 1, .pgLd per 1] else [.slot per false]
  | .slot per v => [.ptP per v 0]
  | .ptP per v it => [.ptR per v it]
  | .ptR per v it => [.ptS per v it]
  | .ptS per v it => if it.val = 0 then [.ptP per v 1] else [.lw per v 0]
  | .lw per v h => [.xl per v ⟨8 * h.val, by omega⟩]
  | .xl per v i => [.xh per v i]
  | .xh per v i => [.cp per v i 0]
  | .cp per v i c =>
    if c.val = 0 then [.cp per v i 1] else if i.val = 7 then [.lw per v 1]
    else if i.val = 15 then [.commit per v] else [.xl per v (i + 1)]
  | .commit per v => [.arrive per v]
  | .arrive .prime false => if n14 then [.slot .prime true] else [.tw 0]
  | .arrive .prime true => warmNexts n14 ++ [.pgSt .warm 0, .pgLd .warm 0]
  | .arrive .warm false => if n14 then [.slot .warm true] else [.tw 4]
  | .arrive .warm true => [.pgSt .warm 0, .pgLd .warm 0] ++ warmNexts n14
  | .arrive .steady false => [.slot .steady true]
  | .arrive .steady true => [.pgSt .steady 0, .pgLd .steady 0] ++ passNexts true
  | .tw t => if n14 then [] else [.te t 0]
  | .te t i =>
    if n14 then [] else
    match i.val with
    | 0 => [.ta t, .te t 1]
    | 1 => [.tc t 0, .te t 2]
    | _ => .tc t 1 :: groupNexts t
  | .ta t => if n14 then [] else [.te t 1]
  | .tc t c => if n14 then [] else if c.val = 0 then [.te t 2] else groupNexts t
  | .dw j => if j.val = 0 then [.dw 1] else if j.val = 1 then [.dw 2]
    else if n14 then [.exit] else [.dq]
  | .dq => if n14 then [] else [.de]
  | .de => if n14 then [] else [.da, .exit]
  | .da => if n14 then [] else [.exit]
  | .exit => []

/-- The scans and the periods. -/
def scans : List Scan := [.first, .loop, .second, .loop2]
def pers : List Per := [.prime, .warm, .steady]

theorem mem_scans (k : Scan) : k ∈ scans := by cases k <;> simp [scans]
theorem mem_pers (per : Per) : per ∈ pers := by cases per <;> simp [pers]

/-- `P` holds at every site, family by family (a decidable statement for a decidable `P`). -/
def AllSites (P : Site → Prop) : Prop :=
  P .setmax ∧ P .q0 ∧ P .q1 ∧ P .uk ∧ P .dq ∧ P .de ∧ P .da ∧ P .exit ∧ (∀ j : Fin 3, P (.dw j)) ∧
  (∀ k ∈ scans, P (.word k) ∧ P (.down k) ∧ P (.total k) ∧ ∀ j : Fin 5, P (.up k j)) ∧
  (∀ l : Bool, P (.vote l) ∧ P (.pre l) ∧ P (.tiles l)) ∧
  (∀ per ∈ pers, (∀ it : Fin 2, P (.pgLd per it) ∧ P (.pgSt per it) ∧ P (.rwSt per it)) ∧
    ∀ v : Bool, P (.slot per v) ∧ P (.commit per v) ∧ P (.arrive per v) ∧
      (∀ it : Fin 2, P (.ptP per v it) ∧ P (.ptR per v it) ∧ P (.ptS per v it) ∧
        P (.lw per v it)) ∧
      ∀ i : Fin 16, P (.xl per v i) ∧ P (.xh per v i) ∧ ∀ c : Fin 2, P (.cp per v i c)) ∧
  ∀ t : Fin 7, P (.tw t) ∧ P (.ta t) ∧ (∀ i : Fin 3, P (.te t i)) ∧ ∀ c : Fin 2, P (.tc t c)

theorem AllSites.ok {P : Site → Prop} (h : AllSites P) (s : Site) : P s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hs, hl, hp, ht⟩ := h
  cases s with
  | setmax => exact h1
  | q0 => exact h2
  | q1 => exact h3
  | uk => exact h4
  | dq => exact h5
  | de => exact h6
  | da => exact h7
  | exit => exact h8
  | dw j => exact h9 j
  | word k => exact (hs k (mem_scans k)).1
  | down k => exact (hs k (mem_scans k)).2.1
  | total k =>
    obtain ⟨_, _, h, _⟩ := hs k (mem_scans k)
    exact h
  | up k j =>
    obtain ⟨_, _, _, h⟩ := hs k (mem_scans k)
    exact h j
  | vote l => exact (hl l).1
  | pre l => exact (hl l).2.1
  | tiles l => exact (hl l).2.2
  | pgLd per it => exact ((hp per (mem_pers per)).1 it).1
  | pgSt per it => exact ((hp per (mem_pers per)).1 it).2.1
  | rwSt per it => exact ((hp per (mem_pers per)).1 it).2.2
  | slot per v => exact ((hp per (mem_pers per)).2 v).1
  | commit per v => exact ((hp per (mem_pers per)).2 v).2.1
  | arrive per v =>
    obtain ⟨_, _, h, _⟩ := (hp per (mem_pers per)).2 v
    exact h
  | ptP per v it =>
    obtain ⟨_, _, _, h, _⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨h0, _, _, _⟩ := h it
    exact h0
  | ptR per v it =>
    obtain ⟨_, _, _, h, _⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨_, h1, _, _⟩ := h it
    exact h1
  | ptS per v it =>
    obtain ⟨_, _, _, h, _⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨_, _, h2, _⟩ := h it
    exact h2
  | lw per v it =>
    obtain ⟨_, _, _, h, _⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨_, _, _, h3⟩ := h it
    exact h3
  | xl per v i =>
    obtain ⟨_, _, _, _, h⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨h0, _, _⟩ := h i
    exact h0
  | xh per v i =>
    obtain ⟨_, _, _, _, h⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨_, h1, _⟩ := h i
    exact h1
  | cp per v i c =>
    obtain ⟨_, _, _, _, h⟩ := (hp per (mem_pers per)).2 v
    obtain ⟨_, _, h2⟩ := h i
    exact h2 c
  | tw t =>
    obtain ⟨h0, _, _, _⟩ := ht t
    exact h0
  | ta t =>
    obtain ⟨_, h1, _, _⟩ := ht t
    exact h1
  | te t i =>
    obtain ⟨_, _, h2, _⟩ := ht t
    exact h2 i
  | tc t c =>
    obtain ⟨_, _, _, h3⟩ := ht t
    exact h3 c

/-- A check of every edge, for both warps. -/
def Edges (chk : Bool → Site → Site → Bool) : Prop :=
  AllSites fun s => ∀ b : Bool, (nexts b s).all (chk b s) = true

theorem Edges.ok {chk : Bool → Site → Site → Bool} (h : Edges chk) {b : Bool} {s s' : Site}
    (hs : s' ∈ nexts b s) : chk b s s' = true :=
  List.all_eq_true.mp (AllSites.ok h s b) s' hs

/-! ### Tags -/

/-- The local array a pointer round stores to: the second one for a later block's K half. -/
def ptOff (per : Per) (b : Bool) : Nat := if per ≠ .prime ∧ b = false then 32 else 0

/-- The barrier of a TMA group's wait. -/
def twOff (t : Fin 7) : Nat := [16, 336, 24, 344, 336, 344, 336].getD t.val 0

/-- The barrier of a group's expect-tx arrival. -/
def taOff (t : Fin 7) : Nat := [0, 320, 8, 328, 320, 328, 320].getD t.val 0

/-- What an edge counts. -/
inductive Tag where
  | none
  /-- A local store at an offset. -/
  | lst (o : Nat)
  /-- A successful poll of the empty barrier of the ring slot of the packet after `c + δ`
  commits. -/
  | acqRing (δ : Nat)
  /-- A successful poll of the barrier at an offset. -/
  | acq (o : Nat)
  | copy
  | commit
  /-- The copy arrival on the full barrier of the last committed packet's slot. -/
  | pub
  /-- A won election at a program counter. -/
  | won (pc : Nat)
  /-- An expect-tx arrival on the barrier at an offset. -/
  | arr (o : Nat)
  deriving DecidableEq

/-- **The tag of an edge**: none for a self-loop. -/
def tag (s s' : Site) : Tag :=
  if s' = s then .none else
  match s with
  | .pgSt _ it => .lst (96 + 4 * it.val)
  | .rwSt _ it => .lst (64 + 4 * it.val)
  | .ptS per v it => .lst (ptOff per v + 8 * it.val)
  | .slot _ _ => .acqRing 0
  | .cp _ _ _ _ | .tc _ _ => .copy
  | .commit _ _ => .commit
  | .arrive _ _ => .pub
  | .tw t => .acq (twOff t)
  | .te t i => match s' with | .ta _ | .tc _ _ => .won (tePc t i) | _ => .none
  | .ta t => .arr (taOff t)
  | .dw j => .acqRing j.val
  | .dq => .acq 24
  | .de => if s' = .da then .won 1896 else .none
  | .da => .arr 8
  | _ => .none

/-- The ledger class a tag counts, after `c` commits. -/
def Tag.cnt (L : Launch) (g c : Nat) : Tag → Option Cnt
  | .none => Option.none
  | .lst o => some (.lst o)
  | .acqRing δ => some (.acquire (bl L g (56 + 8 * ((c + δ) % 3))))
  | .acq o => some (.acquire (bl L g o))
  | .copy => some .copy
  | .commit => some .commit
  | .pub => some (.asyncArrive (bl L g (32 + 8 * ((c - 1) % 3))))
  | .won pc => some (.won pc)
  | .arr o => some (.arrive (bl L g o))

/-! ### Ring counts -/

/-- The occurrences of ring slot `s` among the first `n` packets. -/
def ringCnt (n s : Nat) : Nat := ((List.range n).filter (· % 3 = s)).length

theorem ringCnt_succ (n s : Nat) :
    ringCnt (n + 1) s = ringCnt n s + if n % 3 = s then 1 else 0 := by
  simp only [ringCnt, List.range_succ, List.filter_append, List.length_append]
  split <;> simp_all

/-! ### The step spec -/

/-- **What a step from `dn` on event `e` to `d'` does.** -/
structure Move (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) (e : Event) (d' : D) : Prop where
  edge : d'.site = dn.1.site ∨ d'.site ∈ nexts (not14 w) dn.1.site
  keep : ∀ f, wr dn.1.site f = false → f.same dn.1.v d'.v
  cnt : ∀ c, cls L g c e = decide ((tag dn.1.site d'.site).cnt L g (dn.2 .commit) = some c)

variable {L : Launch} {g w : Nat}

/-- **The counts after a step**: one more in the class of the edge's tag. -/
theorem bump_tag {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hm : Move L g w dn e d') (c : Cnt) :
    Code.bump (cls L g) dn.2 e c =
      dn.2 c + if (tag dn.1.site d'.site).cnt L g (dn.2 .commit) = some c then 1 else 0 := by
  simp only [Code.bump, hm.cnt c, decide_eq_true_eq]

/-- A self-loop counts nothing. -/
theorem tag_self (s : Site) : tag s s = .none := by simp [tag]

end PTX.Kernels.TmlFa4Fwd.Proof.Loader
