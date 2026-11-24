-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Softmax
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWorkPre
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Bits
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.SegFree
public import Lemmas.Flow.OrBits
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of the softmax warps' step lemmas: the conclusion of a step
(`Step`), its construction from a run (`step_of_run`), the invariant of a successor
(`inv_of`), the checkpoint facts (`factsX`) and the segment tactic `sm_seg`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- No assumption has a local rule for the packs `mov.b64 d, {a, b}` (`SegD.packs`). -/
theorem noPack_asms : NoPack asms := fun _ _ _ _ _ _ => asms_localRule_none

/-- The conclusion of a step of this role: the machine stops at a dead thread, or steps to `d'`
at a concrete state of it reached by local steps. -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) ∨
    ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
    (t'.pc = d'.site.pc ∧ t'.sub = d'.site.sub ∧ t'.acc = [] ∧ t'.fault = none ∧
      Holds t'.regs (facts L g d')) ∧ Inv L g d'

/-- A step whose event continues at `u` and whose segment from `u` reaches `d'`, a state at
the first sub-step of its instruction without extra facts. -/
theorem step_of_run {L : Launch} {g : Nat} {d d' : D} {e : Event} {u : TState}
    (hn : next L g d e = some (some d')) (hi : Inv L g d') (hsub : d'.site.sub = 0)
    (hx : d'.site.extra = [])
    (hr : ∃ k t', run kernel asms L g k u = some t' ∧
      At t' d'.site.pc (factsAt L g d'.site.pc d')) :
    Step L g d e u := by
  obtain ⟨k, t', hr, ht'⟩ := hr
  refine .inr ⟨d', t', hn, run_rtg hr,
    ⟨ht'.1, ht'.2.1.trans hsub.symm, ht'.2.2.1, ht'.2.2.2.1, ?_⟩, hi⟩
  have := ht'.2.2.2.2
  simpa [facts, factsAt, hx] using this

/-- A step whose event continues at `u`, whose run from `u` reaches `d'` under the condition `C`
and kills the thread otherwise, and whose successor is `d'` under `C` and none otherwise. -/
theorem step_of_segD {L : Launch} {g : Nat} {d d' : D} {e : Event} {u : TState} {C : Prop}
    {n pc : Nat} {F : List (Nat × Value)} (hy : C → next L g d e = some (some d'))
    (hn : ¬ C → next L g d e = none) (hi : Inv L g d') (hsub : d'.site.sub = 0)
    (hx : d'.site.extra = [])
    (hs : SegD kernel asms L g n pc F d'.site.pc (factsAt L g d'.site.pc d') C)
    (hu : At u pc F) : Step L g d e u := by
  by_cases hc : C
  · obtain ⟨t', hr, ht'⟩ := (hs u hu).1 hc
    exact step_of_run (hy hc) hi hsub hx ⟨n, t', hr, ht'⟩
  · exact .inl ⟨hn hc, (hs u hu).2 hc⟩

/-- The invariant of a successor inside an item, at the same item and trip, of the same kind
of site (first tile or loop trip) and not at the item's end. -/
theorem inv_move {L : Launch} {g : Nat} {d d' : D} (hi : Inv L g d) (hp : d.site.inItem = true)
    (hi' : d'.i = d.i) (ht' : d'.t = d.t) (hs : d'.site.inItem = true)
    (h0 : d'.site.tile0 = true → d.site.tile0 = true)
    (htr : d'.site.inTrip = true → d.site.inTrip = true)
    (hl : d'.site ≠ .lSt ∧ d'.site ≠ .gen 2) (hL : d'.l = d.l := by rfl) : Inv L g d' where
  warp := hi.warp
  item _ := hi' ▸ hi.item hp
  tail h := by rcases h with h | h | h <;> simp [h, Site.inItem] at hs
  start h := by rcases h with h | h <;> simp [h, Site.inItem] at hs
  tile0 h := ht' ▸ hi.tile0 (h0 h)
  trip h := ht' ▸ hi.trip (htr h)
  last h := absurd h (by tauto)
  lBytes := hL ▸ hi.lBytes

/-- The value of `r` in state `d`, with the registers of `ex` valued as given (predicates
and intermediate values at a checkpoint inside a segment). -/
def valueX (L : Launch) (g : Nat) (d : D) (ex : List (Nat × Value)) (r : Nat) : Value :=
  (ex.lookup r).getD (valueOf L g d r)

/-- The facts at `pc` under `valueX`. -/
def factsX (L : Launch) (g pc : Nat) (d : D) (ex : List (Nat × Value)) :
    List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueX L g d ex)

/-- A state at a site without extra facts: its facts are those of its `pc`. -/
theorem facts_eq {L : Launch} {g : Nat} {d : D} (hx : d.site.extra = []) :
    facts L g d = factsAt L g d.site.pc d := by
  simp [facts, factsAt, hx]

/-- Clearing a register no fact names keeps the facts. -/
theorem facts_ne {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- A register live at a site holds its table value. -/
theorem reg_of {L : Launch} {g : Nat} {d : D} {t : TState} {pc r : Nat}
    (h : At t pc (Flow.factsFrom (Flow.live pc ++ d.site.extra) (valueOf L g d)))
    (hr : r ∈ Flow.live pc) : t.regs r = some (valueOf L g d r) :=
  holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨r, List.mem_append_left _ hr, rfl⟩)

/-- A register live at a site whose table value is the Tensor Memory address of column
`col`. -/
theorem reg_tmem {L : Launch} {g : Nat} {d : D} {t : TState} {pc : Nat} (r col : Nat)
    (h : At t pc (facts L g d)) (hr : r ∈ Flow.live pc)
    (hv : valueOf L g d r = b32 (tmem L g col)) (hpc : d.site.pc = pc := by rfl) :
    t.regs r = some (b32 (tmem L g col)) := by
  subst hpc
  exact (reg_of h hr).trans (congrArg some hv)

/-- The Tensor Memory addresses of the warp's lanes fit a word. -/
theorem tmem_lt {L : Launch} {g : Nat} (hw : warpOf L g < 8) (col : Nat) (hc : col < 2 ^ 20) :
    tmem L g col < 2 ^ 32 := by
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  simp only [tmem, stOf, kOf] at hk ⊢
  omega

/-- Facts of the same registers with values equal register by register. -/
theorem at_congr {t : TState} {pc : Nat} {l : List Nat} {v v' : Nat → Value}
    (h : At t pc (Flow.factsFrom l v)) (heq : ∀ r ∈ l, v r = v' r) :
    At t pc (Flow.factsFrom l v') :=
  At.mono h (holds_of_pointwise fun r hr =>
    (holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨r, hr, rfl⟩)).trans (congrArg some (heq r hr)))

/-- A scalar store at its first element continues at the next instruction. -/
theorem afterStore_one {t : TState} {src : Opnd} (h : t.sub = 0) :
    afterStore t [src] = PTX.next t := by
  cases t
  simp_all [afterStore, PTX.next]

/-- `and.b32 x, a, -4`. -/
theorem land_m4 (a : Nat) : a &&& 4294967292 = a % 2 ^ 32 / 4 * 4 :=
  land_field a 32 2 (by norm_num)

/-- A parity register toggled by `xor.b32 r, r, 1`. -/
theorem xor_par (x : Nat) : Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (x % 2)) ^^^
    truncBits 32 (BitVec.ofInt 64 1)) = b32 ((x + 1) % 2) := by
  have e : (x + 1) % 2 = 1 - x % 2 := by omega
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

/-- The trip count is below `2 ^ 31`. -/
theorem trips_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    trips L < 2 ^ 31 := by
  have := skOf_eq hpre
  have := hpre.skRange
  simp only [trips, Work.n, Work.sk]
  omega

/-- The lane field of a Tensor Memory address: `(tid << 16) & 0x600000` is the warp's index in
its group of four, at bit 21. -/
theorem tmem_lane (x : Nat) :
    (x % 4294967296 * 65536 % 4294967296 &&& 6291456) % 4294967296 = x / 32 % 4 * 2097152 := by
  rw [show (6291456 : Nat) = 2 ^ 23 - 2 ^ 21 by norm_num, land_field _ 23 21 (by norm_num)]
  omega

theorem tmem_base (b y : Nat) (hb : b = 0 ∨ b = 128) (hy : y % 256 = 0) :
    b ||| y = b + y := by
  rcases hb with rfl | rfl
  · simp
  · rw [Nat.or_comm, lor_eq_add (k := 8) hy (by norm_num)]
    omega

/-- A Tensor Memory address as the code builds it: the stage's column base `b` (`0` or `128`)
`or` the lane field, `or` the column offset `c`. -/
theorem tmem_addr (b x c : Nat) (hb : b = 0 ∨ b = 128) (hc : c < 128) :
    ((b ||| (x % 4294967296 * 65536 % 4294967296 &&& 6291456) % 4294967296) % 4294967296 |||
      c) % 18446744073709551616 = b + x / 32 % 4 * 2097152 + c := by
  rw [tmem_lane, tmem_base _ _ hb (by omega), lor_eq_add (k := 7) (by omega) (by omega)]
  omega

theorem tmem_addr0 (b x : Nat) (hb : b = 0 ∨ b = 128) :
    (b ||| (x % 4294967296 * 65536 % 4294967296 &&& 6291456) % 4294967296) %
      18446744073709551616 = b + x / 32 % 4 * 2097152 + 0 := by
  rw [tmem_lane, tmem_base _ _ hb (by omega)]
  omega

/-- The table's address: the same number. -/
theorem tmem_rhs (x b c : Nat) (hx : x / 32 < 8) (hb : b = 128 * (x / 32 / 4)) (hc : c < 128) :
    b + x / 32 % 4 * 2097152 + c =
      (2097152 * (x / 32 % 4) + 128 * (x / 32 / 4) + c) % 18446744073709551616 := by
  subst hb
  rw [Nat.mod_eq_of_lt (show 2097152 * (x / 32 % 4) + 128 * (x / 32 / 4) + c <
    18446744073709551616 by omega)]
  omega

/-- Close the equation of a Tensor Memory address register. -/
macro "tmem_close" : tactic => `(tactic| (
  show Value.bits _ _ = _
  nf_simp [tmem, stOf, kOf, warpOf]
  first
    | rw [tmem_addr _ _ _ (by omega) (by omega)]
    | rw [tmem_addr0 _ _ (by omega)]
  exact tmem_rhs _ _ _ (by simp only [warpOf] at *; omega) (by simp only [warpOf] at *; omega)
    (by omega)))

/-- Evaluate a softmax segment from `h` and close the facts of its end state: by unfolding
the code's terms (`rfl`), the item register's operations (`w_rfl`), or the normal form of
integer values (shared addresses, bounded by `Pre.sharedRange`). -/
syntax "sm_seg" term:max term:max : tactic
macro_rules
  | `(tactic| sm_seg $h $hpre) => `(tactic| (
      have hbase := ($hpre).sharedRange
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [valueX, valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, Prologue.sb, List.lookup_cons, List.lookup_nil,
          Nat.reduceBEq]
        all_goals (try launch_norm $hpre)
        all_goals first
          | w_rfl
          | tmem_close
          | seg_close [xor_par, land_m4, statsIdx, tileIdx, Site.tile0, stOf, kOf, Nat.mul_add,
              Nat.mul_one, Nat.add_mul, Nat.one_mul,
              decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true']))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
