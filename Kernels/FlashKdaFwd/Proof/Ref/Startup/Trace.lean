-- SPDX-License-Identifier: Apache-2.0
-- The case analysis of `good_at` is written by Gen/ref_startup_trace.py.
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Scan
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Shapes

@[expose] public section

/-! # The reference invariant of the startup phase along every thread

`startup_inv_upto`, `startup_inv_of_shfl`: in a consistent execution, before each event of a
launched thread the state of the thread's machine satisfies the invariant of the startup phase
(`Inv`: a position, its register facts, its ledger), or the thread has left the phase through
its exit (`Out` held at an earlier position). `startup_followed`: at a state of the phase the
machine does not give up on the thread's event: this is the startup part of the tracking
theorem (`Frame.tracked_of`), and the only part with content, since the machine's only give-up
is at the 21 loads of the offsets array. The final form of the invariant, `startup_inv`, is in
`Startup/Shfl.lean`: there the hypothesis `hS` below is proved.

Hypotheses, stated exactly:

* `hpre : Pre P L mem0`: the launch facts of `Common`, the ranges of `Arith`, and (in
  `returned_offs`) the launch content of the offsets array;
* `hC : ∀ g < L.threads, (code L g).Sound`: soundness of the generated machine. It gives the
  concrete state and the firing fact at each event (`Frame.fired_site`); tracking is **not**
  assumed;
* `hX : Consistent L kernel Assumptions.all mem0 X`;
* `hS : ShflWarp X g`, or `ShflBefore X g n` for the events before position `n`: every shuffle
  of thread `g` returned a value whose word is the thread's warp index (a fact about the other
  lanes of the warp; `Startup/Shfl.lean: shflWarp` proves it by induction on the ordinal of
  the shuffle, with `startup_inv_upto` for the earlier events; the two other returned-value
  facts, elections and offset loads, are proved here from `hX` and `hpre`).

The proof is `phase_inv` (`Ref/Lib.lean`) with one step per position (`good_at`): the event's
closed form (`ev_at`), what it returned (`RetEv`), the transition equation `nextR_<site>` and
the site's lemma of `Steps` or `Scan`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- Every shuffle of thread `g` returned a value whose word is the thread's warp index. -/
def ShflWarp (X : Execution) (g : Nat) : Prop :=
  ∀ {k pc b c : Nat} {md : ShflMode} {a v : Value} {ok : Bool},
    X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩ → wordOf v = some (warp g)

/-- **The returned-value facts of a thread** in a consistent execution under `Pre`. -/
theorem returned (hpre : Pre P L mem0) {K : Kernel}
    (hX : Consistent L K Assumptions.all mem0 X) (hS : ShflWarp X g) : Returned P X g :=
  ⟨returned_elect hX, hS, fun hi hpc hl he => returned_offs hpre hX hi hpc hl he⟩

/-- What one event of the thread returned. -/
structure RetEv (P : Params) (g : Nat) (e : Event) : Prop where
  elect : ∀ {pc inst ld : Nat}, e = ⟨pc, .elect 4294967295 inst ld⟩ → ld = 0
  shfl : ∀ {pc b c : Nat} {md : ShflMode} {a v : Value} {ok : Bool},
    e = ⟨pc, .shfl md a b c v ok⟩ → wordOf v = some (warp g)
  offs : ∀ {pc i : Nat} {bs : List (Option Byte)}, i ≤ P.sequences →
    Assumptions.inputReadSites.contains pc = true → bs.length = 8 →
    e = ⟨pc, .rd { loc := P.offsetLoc i, size := 8 } bs⟩ →
      rebuild 3 bs = .ok (.bits 64 (W (firstToken P.length i)))

theorem retEv_of (hR : Returned P X g) {k : Nat} (he : X.get (g, k) = some e) :
    RetEv P g e :=
  ⟨fun h => hR.elect (h ▸ he), fun h => hR.shfl (h ▸ he),
    fun hi hpc hl h => hR.offs hi hpc hl (h ▸ he)⟩

/-- **One step from a position**: the successor is at a position of the phase, with the
ledger advanced by the event, or it is the exit. -/
def Step (P : Params) (g : Nat) (pos : Pos) (w : Nat → BitVec 64) (e : Event) (d' : D) :
    Prop :=
  (∃ pos', RefAt P g pos' d' ∧ led g pos' = led g pos + ledEv e ∧
      elects g pos' = elects g pos + elOf pos ∧
      leftP P g pos' d'.w + (if e.counts = true then 1 else 0) ≤ leftP P g pos w) ∨
    (Exit P g d' ∧ ledExit g = led g pos + ledEv e ∧
      electsExit g = elects g pos + elOf pos ∧
      13 + (if e.counts = true then 1 else 0) ≤ leftP P g pos w)

/-- **A position is good for an event**: the event is not undefined behaviour, the machine's
successor is a state (not a give-up, not dead), and that state is a step of the phase. -/
def Good (P : Params) (L : Launch) (g : Nat) (pos : Pos) (w : Nat → BitVec 64)
    (p : Nat → Bool) (x : Nat → Value) (e : Event) : Prop :=
  (∀ pc f, e ≠ ⟨pc, .ub f⟩) ∧
    ∃ d', Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d') ∧ Step P g pos w e d'

theorem good_plain {pos : Pos} {δ : Led} {aft : D}
    (hnx : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some aft)) (h : Succ P g pos w δ aft)
    (hδ : ledEv e = δ) (hnu : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hcn : e.counts = true) :
    Good P L g pos w p x e := by
  obtain ⟨pos', h1, h2, h3, h4⟩ := h
  exact ⟨hnu, aft, hnx, .inl ⟨pos', h1, by rw [h2, hδ], h3, by simpa [hcn] using h4⟩⟩

theorem good_elect (hpre : Pre P L mem0) {pos : Pos} {f : Nat → Bool → D} {pc : Nat}
    (hnx : Thread.next L g ⟨pos.site, w, p, x⟩ e = elNext L g e f) (hret : RetEv P g e)
    (hev : ∃ inst ld, e = ⟨pc, .elect 4294967295 inst ld⟩)
    (h : Succ P g pos w ⟨0, 0, 0, 0, 0, 0⟩ (f 0 (decide (lane g = 0)))) :
    Good P L g pos w p x e := by
  obtain ⟨inst, ld, rfl⟩ := hev
  obtain rfl := hret.elect rfl
  obtain ⟨pos', h1, h2, h3, h4⟩ := h
  refine ⟨(fun _ _ h' => by cases h'), f 0 (decide (lane g = 0)), ?_, .inl ⟨pos', h1, (by
    rw [h2]; rfl), h3, h4⟩⟩
  rw [hnx]
  by_cases h0 : lane g = 0 <;> simp [elNext, laneOf_eq hpre, h0]

theorem good_electB (hpre : Pre P L mem0) {pos : Pos} {f : Nat → Bool → D} {pc : Nat}
    (hnx : Thread.next L g ⟨pos.site, w, p, x⟩ e = elNextB L g e f) (hret : RetEv P g e)
    (hev : ∃ inst ld, e = ⟨pc, .elect 4294967295 inst ld⟩)
    (h : Succ P g pos w ⟨0, 0, 0, 0, 0, 0⟩ (f 0 (decide (lane g = 0)))) :
    Good P L g pos w p x e := by
  obtain ⟨inst, ld, rfl⟩ := hev
  obtain rfl := hret.elect rfl
  obtain ⟨pos', h1, h2, h3, h4⟩ := h
  refine ⟨(fun _ _ h' => by cases h'), f 0 (decide (lane g = 0)), ?_, .inl ⟨pos', h1, (by
    rw [h2]; rfl), h3, h4⟩⟩
  have hb : (lane g == 0) = decide (lane g = 0) := by
    by_cases h0 : lane g = 0 <;> simp [h0]
  rw [hnx]
  simp only [elNextB, laneOf_eq hpre, hb]

theorem good_shfl {pos : Pos} {f : BitVec 64 → Bool → D} {pc b c : Nat} {a : Value}
    (hnx : Thread.next L g ⟨pos.site, w, p, x⟩ e = shNext e f) (hret : RetEv P g e)
    (hev : ∃ v ok, e = ⟨pc, .shfl .idx a b c v ok⟩)
    (h : ∀ ok, Succ P g pos w ⟨0, 0, 0, 0, 0, 1⟩ (f (W (warp g)) ok)) :
    Good P L g pos w p x e := by
  obtain ⟨v, ok, rfl⟩ := hev
  have hv := hret.shfl rfl
  obtain ⟨pos', h1, h2, h3, h4⟩ := h ok
  refine ⟨(fun _ _ h' => by cases h'), f (W (warp g)) ok, ?_, .inl ⟨pos', h1, (by
    rw [h2]; rfl), h3, h4⟩⟩
  rw [hnx]
  simp only [shNext, hv]

/-- The sites of the 21 load positions are the load instructions of the assumption
`inputReadOnly`. -/
theorem load_site (j : Fin 21) :
    Assumptions.inputReadSites.contains (Pos.load j).site.pc = true := by
  fin_cases j <;> rfl

/-- **A load through a pointer to entry `b` with displacement `8 k`** reads the eight bytes of
entry `b + k`; the address is a multiple of 8, so the load is not undefined behaviour. -/
theorem offsets_rd (hpre : Pre P L mem0) {pc base b k : Nat} {off : Int} {ds : List Nat}
    (hf : Fires pc (loadTmpl Assumptions.all L g t .global false 64 ds base off) e o)
    (hr : t.regs base = some (.bits 64 (W (P.offsetsBase + 8 * b)))) (hs : t.sub = 0)
    (hoff : off = ((8 * k : Nat) : Int)) (hk : b + k ≤ P.sequences) (hds : ds.length = 1) :
    ∃ bs, bs.length = 8 ∧ e = ⟨pc, .rd { loc := P.offsetLoc (b + k), size := 8 } bs⟩ := by
  have hlt := offsets_lt hpre
  have hal := hpre.offsetsAlign
  subst hoff
  have hl : (truncBits 64 (W (P.offsetsBase + 8 * b)) + BitVec.ofInt 64 ((8 * k : Nat) : Int)).toNat
      = P.offsetsBase + 8 * (b + k) := by
    simp only [truncBits, W, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  refine shape_ldM (P := fun e' => ∃ bs, bs.length = 8 ∧
      e' = ⟨pc, .rd { loc := P.offsetLoc (b + k), size := 8 } bs⟩) hf (effAddr_global_bits hr) hs
    (fun bs hbs => ⟨bs, hbs, ?_⟩) (fun hm => ?_)
  · simp only [Loc.at, hl, Params.offsetLoc, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]
  · exfalso
    simp only [hl, hds, Nat.reduceDiv, Nat.mul_one] at hm
    omega

theorem good_load (hpre : Pre P L mem0) {j : Fin 21} {ptr k : Nat} {aft : BitVec 64 → D}
    (hnx : Thread.next L g ⟨(Pos.load j).site, w, p, x⟩ e = loadWord e aft) (hret : RetEv P g e)
    (hok : LoadOK P g j ptr k w aft)
    (hacc : ∀ b, w ptr = W (P.offsetsBase + 8 * b) → b + k ≤ P.sequences → ∃ bs,
      bs.length = 8 ∧ e = ⟨(Pos.load j).site.pc,
        .rd { loc := P.offsetLoc (b + k), size := 8 } bs⟩) :
    Good P L g (.load j) w p x e := by
  obtain ⟨b, hb, hk, pos', h1, h2, h3, h4⟩ := hok
  obtain ⟨bs, hl, rfl⟩ := hacc b hb hk
  have hx := hret.offs hk (load_site j) hl rfl
  refine ⟨(fun _ _ h' => by cases h'), aft (W (cu P (b + k))), ?_, .inl ⟨pos', h1, (by
    rw [h2]; rfl), h3, h4⟩⟩
  rw [hnx, loadWord_rd hx, onWord64_bits]

theorem good_wait (hpre : Pre P L mem0) (h : RefAt P g .wait ⟨.mbarWait 0, w, p, x⟩)
    (hev : Ev P L g .wait e) : Good P L g .wait w p x e := by
  obtain ⟨ok, rfl⟩ := hev
  have hnx := nextR_mbarWait_0 (L := L) (g := g) w p x
    ⟨384, .wait ⟨.shared, g / L.block, P.sharedBase + 98384⟩ 0 ok true .cta⟩
  refine ⟨(fun _ _ h' => by cases h'), ?_⟩
  cases ok
  · obtain ⟨pos', h1, h2, h3, h4⟩ := st_wait_no (L := L) hpre h
    exact ⟨_, hnx, .inl ⟨pos', h1, (by rw [h2]; rfl), h3, h4⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := st_wait_ok (L := L) hpre h
    exact ⟨_, hnx, .inr ⟨h1, (by rw [h2]; rfl), h3, h4⟩⟩

/-- `load_acc r k`: the access of the load of the current case, through the pointer register
`r` with displacement `8 k`. -/
syntax "load_acc " num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| load_acc $r $k) => `(tactic| (
      intro b hb hk
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      have r1 := reg_w hat (r := $r) (by lit_mem) (n := 64) rfl
      dsimp only at r1
      rw [hb] at r1
      tmpl_unfold hf PTX.loadTmpl
      dsimp only [PTX.DType.width] at hf
      exact offsets_rd hpre hf r1 hat.2.1 (k := $k) rfl hk rfl))

set_option maxRecDepth 8000 in
/-- **Every position of the phase is good for the event fired at it.** -/
theorem good_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hret : RetEv P g e) : Good P L g pos w p x e := by
  cases pos with
  | elect j =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    fin_cases j
    · exact good_elect hpre (nextR_elect_0 w p x e) hret hev (st_elect_0 hpre h)
    · exact good_elect hpre (nextR_elect_1 w p x e) hret hev (st_elect_1 hpre h)
    · exact good_elect hpre (nextR_elect_2 w p x e) hret hev (st_elect_2 hpre h)
    · exact good_elect hpre (nextR_elect_3 w p x e) hret hev (st_elect_3 hpre h)
    · exact good_electB hpre (nextR_elect_4 w p x e) hret hev (st_elect_4 hpre h)
  | shfl j =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    fin_cases j
    · obtain ⟨v, ok, rfl⟩ := hev
      exact good_plain (nextR_shfl_0 w p x _) (st_shfl_0 hpre ok h) rfl
          (fun _ _ h' => by cases h') rfl
    · exact good_shfl (nextR_shfl_1 w p x e) hret hev fun ok => st_shfl_1 hpre ok h
    · exact good_shfl (nextR_shfl_2 w p x e) hret hev fun ok => st_shfl_2 hpre ok h
  | init j =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    fin_cases j
    · exact good_plain (nextR_mbarInit_0 w p x e) (st_init_0 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_1 w p x e) (st_init_1 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_2 w p x e) (st_init_2 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_3 w p x e) (st_init_3 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_4 w p x e) (st_init_4 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_5 w p x e) (st_init_5 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_6 w p x e) (st_init_6 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_7 w p x e) (st_init_7 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_8 w p x e) (st_init_8 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_9 w p x e) (st_init_9 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_mbarInit_10 w p x e) (st_init_10 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
  | fence j =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    fin_cases j
    · exact good_plain (nextR_fenceMbarInit_0 w p x e) (st_fence_0 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_fenceMbarInit_1 w p x e) (st_fence_1 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_fenceMbarInit_2 w p x e) (st_fence_2 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
  | bar j =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    fin_cases j
    · exact good_plain (nextR_bar_0 w p x e) (st_bar_0 hpre hg h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_bar_1 w p x e) (st_bar_1 hpre hg h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_bar_2 w p x e) (st_bar_2 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
  | load j =>
    fin_cases j
    · exact good_load hpre (nextR_load_0 w p x e) hret (st_load_0 hpre h) (by load_acc 2264 0)
    · exact good_load hpre (nextR_load_1 w p x e) hret (st_load_1 hpre h) (by load_acc 2264 1)
    · exact good_load hpre (nextR_load_2 w p x e) hret (st_load_2 hpre h) (by load_acc 2247 0)
    · exact good_load hpre (nextR_load_3 w p x e) hret (st_load_3 hpre h) (by load_acc 2266 1)
    · exact good_load hpre (nextR_load_4 w p x e) hret (st_load_4 hpre h) (by load_acc 2266 2)
    · exact good_load hpre (nextR_load_5 w p x e) hret (st_load_5 hpre h) (by load_acc 2266 3)
    · exact good_load hpre (nextR_load_6 w p x e) hret (st_load_6 hpre h) (by load_acc 2266 4)
    · exact good_load hpre (nextR_load_7 w p x e) hret (st_load_7 hpre h) (by load_acc 2266 5)
    · exact good_load hpre (nextR_load_8 w p x e) hret (st_load_8 hpre h) (by load_acc 2266 6)
    · exact good_load hpre (nextR_load_9 w p x e) hret (st_load_9 hpre h) (by load_acc 2266 7)
    · exact good_load hpre (nextR_load_10 w p x e) hret (st_load_10 hpre h) (by load_acc 2266 8)
    · exact good_load hpre (nextR_load_11 w p x e) hret (st_load_11 hpre h) (by load_acc 2275 1)
    · exact good_load hpre (nextR_load_12 w p x e) hret (st_load_12 hpre h) (by load_acc 2275 0)
    · exact good_load hpre (nextR_load_13 w p x e) hret (st_load_13 hpre h) (by load_acc 2275 2)
    · exact good_load hpre (nextR_load_14 w p x e) hret (st_load_14 hpre h) (by load_acc 2275 3)
    · exact good_load hpre (nextR_load_15 w p x e) hret (st_load_15 hpre h) (by load_acc 2275 4)
    · exact good_load hpre (nextR_load_16 w p x e) hret (st_load_16 hpre h) (by load_acc 2286 0)
    · exact good_load hpre (nextR_load_17 w p x e) hret (st_load_17 hpre h) (by load_acc 2282 1)
    · exact good_load hpre (nextR_load_18 w p x e) hret (st_load_18 hpre h) (by load_acc 2282 0)
    · exact good_load hpre (nextR_load_19 w p x e) hret (st_load_19 hpre h) (by load_acc 2282 2)
    · exact good_load hpre (nextR_load_20 w p x e) hret (st_load_20 hpre h) (by load_acc 2288 1)
  | arrive =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    exact good_plain (nextR_mbarArrive_0 w p x e) (st_arrive hpre hg h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
  | copy j =>
    have hev := ev_at hpre hg _ h hat hc hf (fun hs => hs)
    fin_cases j
    · exact good_plain (nextR_tensorCopy_0 w p x e) (st_copy_0 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_1 w p x e) (st_copy_1 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_2 w p x e) (st_copy_2 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_3 w p x e) (st_copy_3 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_4 w p x e) (st_copy_4 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_5 w p x e) (st_copy_5 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_6 w p x e) (st_copy_6 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_7 w p x e) (st_copy_7 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_8 w p x e) (st_copy_8 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_9 w p x e) (st_copy_9 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_10 w p x e) (st_copy_10 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_11 w p x e) (st_copy_11 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_12 w p x e) (st_copy_12 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_13 w p x e) (st_copy_13 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_14 w p x e) (st_copy_14 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
    · exact good_plain (nextR_tensorCopy_15 w p x e) (st_copy_15 hpre h) (by rw [hev]; rfl)
        (by rw [hev]; intro _ _ h'; cases h') (by rw [hev]; rfl)
  | wait => exact good_wait hpre h (ev_at hpre hg _ h hat hc hf (fun hs => hs))

/-- The event of a load of the offsets array, from the step lemma of its site (the pointer and
its range) and the access the pointer gives. -/
theorem load_ev {j : Fin 21} {ptr k : Nat} {aft : BitVec 64 → D}
    (hok : LoadOK P g j ptr k w aft)
    (hacc : ∀ b, w ptr = W (P.offsetsBase + 8 * b) → b + k ≤ P.sequences → ∃ bs,
      bs.length = 8 ∧ e = ⟨(Pos.load j).site.pc,
        .rd { loc := P.offsetLoc (b + k), size := 8 } bs⟩) : Ev P L g (.load j) e := by
  obtain ⟨b, hb, hk, -⟩ := hok
  obtain ⟨bs, hl, rfl⟩ := hacc b hb hk
  exact ⟨b + k, hk, bs, hl, rfl⟩

set_option maxRecDepth 8000 in
/-- **The event at a load of the offsets array**: a read of the eight bytes of an entry
`i ≤ N` of the array (never undefined behaviour: the address is a multiple of 8). -/
theorem ev_load (hpre : Pre P L mem0) (j : Fin 21)
    (h : RefAt P g (.load j) ⟨(Pos.load j).site, w, p, x⟩)
    (hat : (code L g).AtD ⟨(Pos.load j).site, w, p, x⟩ t)
    (hc : kernel.code[(Pos.load j).site.pc]? = some ins)
    (hf : Fires (Pos.load j).site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Ev P L g (.load j) e := by
  fin_cases j
  · exact load_ev (st_load_0 hpre h) (by load_acc 2264 0)
  · exact load_ev (st_load_1 hpre h) (by load_acc 2264 1)
  · exact load_ev (st_load_2 hpre h) (by load_acc 2247 0)
  · exact load_ev (st_load_3 hpre h) (by load_acc 2266 1)
  · exact load_ev (st_load_4 hpre h) (by load_acc 2266 2)
  · exact load_ev (st_load_5 hpre h) (by load_acc 2266 3)
  · exact load_ev (st_load_6 hpre h) (by load_acc 2266 4)
  · exact load_ev (st_load_7 hpre h) (by load_acc 2266 5)
  · exact load_ev (st_load_8 hpre h) (by load_acc 2266 6)
  · exact load_ev (st_load_9 hpre h) (by load_acc 2266 7)
  · exact load_ev (st_load_10 hpre h) (by load_acc 2266 8)
  · exact load_ev (st_load_11 hpre h) (by load_acc 2275 1)
  · exact load_ev (st_load_12 hpre h) (by load_acc 2275 0)
  · exact load_ev (st_load_13 hpre h) (by load_acc 2275 2)
  · exact load_ev (st_load_14 hpre h) (by load_acc 2275 3)
  · exact load_ev (st_load_15 hpre h) (by load_acc 2275 4)
  · exact load_ev (st_load_16 hpre h) (by load_acc 2286 0)
  · exact load_ev (st_load_17 hpre h) (by load_acc 2282 1)
  · exact load_ev (st_load_18 hpre h) (by load_acc 2282 0)
  · exact load_ev (st_load_19 hpre h) (by load_acc 2282 2)
  · exact load_ev (st_load_20 hpre h) (by load_acc 2288 1)

/-- **The event at every position of the phase**, in closed form (`Ev`); in particular it is
not undefined behaviour (`Ev.noUb`). -/
theorem ev_full (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) : Ev P L g pos e := by
  cases pos with
  | load j => exact ev_load hpre j h hat hc hf
  | _ => exact ev_at hpre hg _ h hat hc hf (fun hs => hs)

/-! ### Along the trace -/

/-- Every shuffle among the first `n` events of thread `g` returned a value whose word is the
thread's warp index. -/
def ShflBefore (X : Execution) (g n : Nat) : Prop :=
  ∀ {k pc b c : Nat} {md : ShflMode} {a v : Value} {ok : Bool}, k < n →
    X.get (g, k) = some ⟨pc, .shfl md a b c v ok⟩ → wordOf v = some (warp g)

theorem ShflWarp.before (hS : ShflWarp X g) (n : Nat) : ShflBefore X g n := fun _ he => hS he

/-- What the event `k` returned, when the shuffles before `n > k` are known. -/
theorem retEv_upto (hpre : Pre P L mem0) {K : Kernel}
    (hX : Consistent L K Assumptions.all mem0 X) {n k : Nat} (hS : ShflBefore X g n)
    (hk : k < n) (he : X.get (g, k) = some e) : RetEv P g e :=
  ⟨fun h => returned_elect hX (h ▸ he), fun h => hS hk (h ▸ he),
    fun hi hpc hl h => returned_offs hpre hX hi hpc hl (h ▸ he)⟩

/-- **The warp collectives of an event of a position**: a shuffle at a shuffle position (the
ledger counts it), an election at an election position. -/
theorem Ev.coll {pos : Pos} (h : Ev P L g pos e) :
    (if Sched.isWarpColl e = true then 1 else 0) = (ledEv e).shfls + elOf pos := by
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at h
  · obtain ⟨inst, ld, rfl⟩ := h
    rfl
  · obtain ⟨v, ok, rfl⟩ := h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · obtain ⟨i, hi, bs, hbs, rfl⟩ := h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · obtain ⟨ok, rfl⟩ := h
    rfl

/-- **The invariant with the count of warp collectives**: `Inv`, and the thread's shuffles and
elections before position `k` are the position's shuffles (ledger) plus its elections
(`elects`). -/
def InvE (P : Params) (X : Execution) (g k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ ledOf ((X.tr g).take k) = led g pos ∧
    ((X.tr g).take k).countP Sched.isWarpColl = (led g pos).shfls + elects g pos

/-- **The exit condition with the count of warp collectives.** -/
def OutE (P : Params) (X : Execution) (g k : Nat) (d : D) : Prop :=
  Out P X g k d ∧ ((X.tr g).take k).countP Sched.isWarpColl = 3 + electsExit g

theorem InvE.inv {k : Nat} {d : D} (h : InvE P X g k d) : Inv P X g k d :=
  let ⟨pos, h1, h2, _⟩ := h
  ⟨pos, h1, h2⟩

section
variable (hpre : Pre P L mem0) (hC : ∀ g < L.threads, (code L g).Sound)
  (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
include hpre hC hX hg

omit hC hX in
/-- The step of `phase_inv` for the startup phase. -/
theorem inv_step (k : Nat) (e : Event) (s s' : D) (t : TState) (ins : Instr)
    (o : Option TState) (he : X.get (g, k) = some e) (hI : InvE P X g k s)
    (hat : (code L g).AtD s t) (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hret : RetEv P g e)
    (hn : Thread.next L g s e = some (some s')) :
    InvE P X g (k + 1) s' ∨ OutE P X g (k + 1) s' := by
  obtain ⟨pos, hr, hl, hcl⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  have hled : ledOf ((X.tr g).take (k + 1)) = ledOf ((X.tr g).take k) + ledEv e := by
    simp only [ledOf, ledEv, Led.add_def, count_snoc _ he]
  have hcc := count_snoc Sched.isWarpColl he
  have hco := (ev_full hpre hg pos hr hat hc hf).coll
  obtain ⟨-, d', hd, hstep⟩ := good_at hpre hg pos hr hat hc hf hret
  rw [hd] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  rcases hstep with ⟨pos', h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩
  · refine .inl ⟨pos', h1, by rw [hled, hl, h2], ?_⟩
    have h4 : (led g pos').shfls = (led g pos).shfls + (ledEv e).shfls := by
      rw [h2]
      rfl
    rw [hcc, hcl, h4, h3]
    omega
  · refine .inr ⟨⟨h1, by rw [hled, hl, h2]⟩, ?_⟩
    have h4 : (ledExit g).shfls = (led g pos).shfls + (ledEv e).shfls := by
      rw [h2]
      rfl
    have h5 : (ledExit g).shfls = 3 := rfl
    rw [hcc, hcl, h3]
    omega

/-- **The counted events left at a state, at most**: a function of the state (the site's
instruction and, inside the scan's loop of eight, the loop's index register); `leftP` of
`Steps.lean` at the state's position (`leftOf_pos`). The exit state of the phase has 13. -/
def leftOf (P : Params) (g : Nat) (d : D) : Nat :=
  (400 - d.site.pc) + 100 * (if d.site.pc < 131 then seqOf P g - seqOf P g % 8
    else if d.site.pc ≤ 196 then seqOf P g - seqOf P g % 8 - (d.w 2097).toNat else 0)

omit hpre hC hX hg in
theorem leftOf_pos (pos : Pos) (w : Nat → BitVec 64) (p : Nat → Bool) (x : Nat → Value) :
    leftOf P g ⟨pos.site, w, p, x⟩ = leftP P g pos w := by
  rcases pos with j | j | j | j | j | j | _ | j | _ <;> (try fin_cases j) <;> rfl

omit hC hX in
/-- **Every step from a state of the phase lowers the measure by the event's count**: a
counted event (every event but a failed poll) lowers `leftOf` by at least one, a failed poll
does not raise it. -/
theorem left_step (k : Nat) (e : Event) (s s' : D) (t : TState) (ins : Instr)
    (o : Option TState) (hI : Inv P X g k s)
    (hat : (code L g).AtD s t) (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) (hret : RetEv P g e)
    (hn : Thread.next L g s e = some (some s')) :
    leftOf P g s' + (if e.counts = true then 1 else 0) ≤ leftOf P g s := by
  obtain ⟨pos, hr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨-, d', hd, hstep⟩ := good_at hpre hg pos hr hat hc hf hret
  rw [hd] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  rw [leftOf_pos]
  rcases hstep with ⟨pos', h1, -, -, h4⟩ | ⟨h1, -, -, h4⟩
  · obtain ⟨site', w', p', x'⟩ := d'
    obtain rfl : site' = pos'.site := h1.site
    rw [leftOf_pos]
    exact h4
  · have h13 : leftOf P g d' = 13 := by
      obtain ⟨site', w', p', x'⟩ := d'
      obtain rfl : site' = .fenceProxy 0 := h1.site
      rfl
    rw [h13]
    exact h4

set_option maxRecDepth 8000 in
/-- **The invariant with the count of warp collectives, up to position `n`**: it needs the
shuffles' values only for the events before `n`. -/
theorem startup_invE_upto {n : Nat} (hS : ShflBefore X g n) {k : Nat} {s : D} (hkn : k ≤ n)
    (hk : k < (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    InvE P X g k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧
      OutE P X g j s0 := by
  have h0 : (0 ≤ n → InvE P X g 0 (init L g)) := fun _ => by
    obtain ⟨pos, h1, h2, h3⟩ := st_init (L := L) (g := g) hpre
    refine ⟨pos, h1, ?_, ?_⟩
    · rw [h2, List.take_zero]
      rfl
    · rw [h2, h3, List.take_zero]
      rfl
  have key := phase_inv (C := code L) hC hX (fun k s => k ≤ n → InvE P X g k s)
    (fun k s => k ≤ n ∧ OutE P X g k s) h0 (by
      intro k e s s' t ins o he _ hI hat hc hf hub hn
      by_cases hkn : k + 1 ≤ n
      · rcases inv_step hpre hg k e s s' t ins o he (hI (by omega)) hat hc hf hub
            (retEv_upto hpre hX hS (by omega) he) hn with h | h
        · exact .inl fun _ => h
        · exact .inr ⟨hkn, h⟩
      · exact .inl fun h => absurd h hkn) k s hk hσ
  rcases key with h | ⟨j, hj, s0, h1, -, h2⟩
  · exact .inl (h hkn)
  · exact .inr ⟨j, hj, s0, h1, h2⟩

/-- **The reference invariant of the startup phase, up to position `n`**: it needs the
shuffles' values only for the events before `n`. -/
theorem startup_inv_upto {n : Nat} (hS : ShflBefore X g n) {k : Nat} {s : D} (hkn : k ≤ n)
    (hk : k < (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧
      Out P X g j s0 := by
  rcases startup_invE_upto hpre hC hX hg hS hkn hk hσ with h | ⟨j, hj, s0, h1, h2⟩
  · exact .inl h.inv
  · exact .inr ⟨j, hj, s0, h1, h2.1⟩

/-- **The reference invariant of the startup phase, given the shuffles' values**: before each
event of a launched thread, the state of its machine is at a position of the phase with the
position's register facts and ledger, or the thread has left the phase through its exit. -/
theorem startup_inv_of_shfl (hS : ShflWarp X g) {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧
      Out P X g j s0 :=
  startup_inv_upto hpre hC hX hg (hS.before k) le_rfl hk hσ

/-- **At a state of the phase the thread's event is not undefined behaviour and the machine's
successor is a state** (not a give-up, not dead), at every site of the phase. `hret` is what
the event returned (`retEv_upto`). -/
theorem startup_ok {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hret : RetEv P g e) :
    (∀ pc f, e ≠ ⟨pc, .ub f⟩) ∧ ∃ s', Thread.next L g s e = some (some s') := by
  obtain ⟨pos, hr, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
  obtain ⟨h1, d', h2, -⟩ := good_at hpre hg pos hr hat hc hf hret
  exact ⟨h1, d', h2⟩

/-- **The machine follows the thread through the startup phase**: at a state of the phase the
successor along the thread's event is not a give-up. -/
theorem startup_followed {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hret : RetEv P g e) : Thread.next L g s e ≠ some none := by
  obtain ⟨-, s', h⟩ := startup_ok hpre hC hX hg he hσ hI hret
  rw [h]
  intro h'
  cases h'

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
