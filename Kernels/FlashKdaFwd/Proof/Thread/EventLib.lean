-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.Lib
public import Kernels.FlashKdaFwd.Proof.Thread.DataLib
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.SegDead
public import Lemmas.Flow.Step.SiteCases
public meta import Lean

@[expose] public section

/-! # Paths of local code as outcomes

Generic lemmas and tactics of the thread layer (nothing here names the kernel's code).

After most events the local code up to the next site is not one evaluated segment: it meets an
instruction that evaluation cannot run (a parameter load, which needs a launch fact; a `mapa`,
which the launch may refuse), or a data run that continues only under a condition on opaque
values. Such a path is cut into pieces, and each piece is proved on its own.

* `Local C q F o`: the local code from program counter `q` with the facts `F` has the
  **outcome** `o : Option (Option C.D)`: `some (some d')` (local steps reach the site of the
  state `d'`, with its facts), `none` (every such thread is dead), `some none` (the machine
  stops following; nothing is claimed).
* The pieces: `Local.site` (evaluated code up to the successor's site), `Local.cut` (evaluated
  code up to a checkpoint, then the rest), `Local.run` (a conditional piece `SegD … P`, a data
  run, then the rest under `P`; the outcome is `under P o`), `Local.ite` / `Local.iteD` (a
  branch the file decides), `Local.ldParam`, `Local.ldParamObj`, `Local.mapa` (one local
  instruction each), `Local.onWord64` (the registers a 64-bit load wrote, when the machine
  follows integer values only), `Local.dead_of`.
* `Local.cont`: what a step obligation asks after the event (`Code.Cont`), from the outcome of
  the local code after it. The continuation-form combinators of `DataLib.lean` (`step_load_x`,
  `step_matrix_x`, …) hand the caller the state after the event and ask `Code.Cont`; with
  `Local.cont` the rest is a path of pieces.
* Step combinators in outcome form, one per event class (`step_issue_o`, `step_arrive_o`,
  `step_wait_o`, `step_elect_o`, `step_load_o`, `step_store_o`, `step_ldv_mid_o`,
  `step_ldv_last_o`), `step_trap`, and the tactics `ev_<class>` that apply them at a literal
  site. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section

section Generic

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-! ### Outcomes of local code -/

/-- **The outcome of the local code from `q` with the facts `F`**: `some (some d')` when local
steps reach the site of `d'` with its facts (at sub-step 0, with an empty accumulator, and
`d'`'s invariant), `none` when every such thread is dead. Nothing is asked of `some none` (the
machine stops following): a transition that never returns it never uses that case. -/
structure Local (C : Code K A L g) (q : Nat) (F : List (Nat × Value))
    (o : Option (Option C.D)) : Prop where
  seg : ∀ d', o = some (some d') →
    (∃ n, Seg K A L g n q F (C.pc d') (C.facts d')) ∧ C.sub d' = 0 ∧ C.acc d' = [] ∧ C.inv d'
  dead : o = none → DeadFrom K A L g q F

/-- What `StepAt.step` asks, from the outcome of the local code after the event. -/
theorem Local.cont {d : C.D} {e : Event} {u : TState} {s : Nat} {F : List (Nat × Value)}
    {o : Option (Option C.D)} (hl : Local C s F o) (hn : C.next d e = o) (hu : At u s F) :
    C.Cont d e u := by
  rcases o with _ | _ | d'
  · exact .inr ⟨hn, hl.dead rfl u hu⟩
  · exact .inl (.inl hn)
  · obtain ⟨⟨n, hseg⟩, hs, ha, hi⟩ := hl.seg d' rfl
    obtain ⟨t', hr, ht⟩ := hseg u hu
    exact .inl (.inr ⟨d', t', hn, run_rtg hr,
      ⟨⟨ht.1, ht.2.1.trans hs.symm, ht.2.2.1.trans ha.symm, ht.2.2.2.1, ht.2.2.2.2⟩, hi⟩⟩)

/-- The rest of the path is evaluated code up to the site of the successor. -/
theorem Local.site {q : Nat} {F : List (Nat × Value)} {d' : C.D}
    (hseg : ∃ n, Seg K A L g n q F (C.pc d') (C.facts d')) (hs : C.sub d' = 0)
    (ha : C.acc d' = []) (hi : C.inv d') : Local C q F (some (some d')) :=
  ⟨fun _ h => (by cases h; exact ⟨hseg, hs, ha, hi⟩), fun h => (by cases h)⟩

/-- Evaluated code up to the checkpoint `q'` with the facts `H`, then the rest. -/
theorem Local.cut {q q' : Nat} {F H : List (Nat × Value)} {o : Option (Option C.D)}
    (h1 : ∃ n, Seg K A L g n q F q' H) (h2 : Local C q' H o) : Local C q F o :=
  ⟨fun d' h => ⟨Seg.comp_ex h1 (h2.seg d' h).1, (h2.seg d' h).2⟩,
    fun h => DeadFrom.of_seg h1 (h2.dead h)⟩

/-- More or restated facts at the start. -/
theorem Local.weaken {q : Nat} {F F' : List (Nat × Value)} {o : Option (Option C.D)}
    (hF : ∀ R, Holds R F → Holds R F') (h : Local C q F' o) : Local C q F o :=
  ⟨fun d' hd => by
      obtain ⟨⟨n, hs⟩, hr⟩ := h.seg d' hd
      exact ⟨⟨n, hs.weaken_start hF⟩, hr⟩,
    fun hd u hu => h.dead hd u (At.mono hu (hF _ hu.2.2.2.2))⟩

/-- Every thread at `q` with the facts `F` is dead. -/
theorem Local.dead_of {q : Nat} {F : List (Nat × Value)} (h : DeadFrom K A L g q F) :
    Local C q F none :=
  ⟨fun _ h => (by cases h), fun _ => h⟩

/-- A branch the transition decides from the file: each side under its hypothesis (the walk of
the segment decides the branch's predicate with it). -/
theorem Local.ite {q : Nat} {F : List (Nat × Value)} {c : Bool} {o1 o2 : Option (Option C.D)}
    (h1 : c = true → Local C q F o1) (h2 : c = false → Local C q F o2) :
    Local C q F (if c = true then o1 else o2) := by
  cases c
  · simpa using h2 rfl
  · simpa using h1 rfl

/-- A branch of a transition whose two arms are states: each arm under its hypothesis. -/
theorem Local.iteD {q : Nat} {F : List (Nat × Value)} {c : Bool} {a b : C.D}
    (h1 : c = true → Local C q F (some (some a))) (h2 : c = false → Local C q F (some (some b))) :
    Local C q F (some (some (if c = true then a else b))) := by
  cases c
  · simpa using h2 rfl
  · simpa using h1 rfl

/-! ### Conditional pieces: data runs -/

/-- **An outcome under a condition**: `o` when `P` holds, a dead thread otherwise (the
generalization of `across P d'`, which is `under P (some (some d'))`). -/
def under {D : Type} (P : Prop) (o : Option (Option D)) : Option (Option D) :=
  haveI := Classical.propDecidable P
  if P then o else none

theorem under_pos {D : Type} {P : Prop} {o : Option (Option D)} (h : P) : under P o = o := by
  simp [under, h]

theorem under_neg {D : Type} {P : Prop} {o : Option (Option D)} (h : ¬ P) : under P o = none := by
  simp [under, h]

theorem under_ne {D : Type} {P : Prop} {o : Option (Option D)} (h : o ≠ some none) :
    under P o ≠ some none := by
  by_cases hP : P
  · rwa [under_pos hP]
  · rw [under_neg hP]; simp

theorem under_state {D : Type} (P : Prop) (d' : D) : under P (some (some d')) = across P d' :=
  rfl

/-- **A conditional piece, then the rest**: a piece that reaches the checkpoint `q'` with the
facts `H` under `P` and kills the thread otherwise (`SegD`, the form of a data run), then the
outcome `o` from there. -/
theorem Local.run {q q' n : Nat} {F H : List (Nat × Value)} {P : Prop}
    {o : Option (Option C.D)} (h1 : SegD K A L g n q F q' H P) (h2 : P → Local C q' H o) :
    Local C q F (under P o) := by
  by_cases hP : P
  · rw [under_pos hP]
    exact Local.cut ⟨n, h1.seg hP⟩ (h2 hP)
  · rw [under_neg hP]
    exact Local.dead_of fun u hu => (h1 u hu).2 hP

/-- The last piece of a path is a conditional piece to the successor's site (`across`). -/
theorem Local.across {q n : Nat} {F : List (Nat × Value)} {P : Prop} {d' : C.D}
    (h : SegD K A L g n q F (C.pc d') (C.facts d') P) (hs : C.sub d' = 0) (ha : C.acc d' = [])
    (hi : C.inv d') : Local C q F (across P d') := by
  by_cases hP : P
  · rw [across_pos hP]
    exact Local.site ⟨n, h.seg hP⟩ hs ha hi
  · rw [across_neg hP]
    exact Local.dead_of fun u hu => (h u hu).2 hP

/-! ### A loaded register the machine follows as a 64-bit word only -/

/-- **The transition after a load whose value the machine follows only when it is a 64-bit
integer** (the loads of the read-only offsets array, whose content an assumption pins): the
state `k x` for the integer `x`, and for any other value the machine stops following
(`some none`), the one give-up of the thread machine. -/
def onWord64 {D : Type} (v : Value) (k : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 64 x => some (some (k x))
  | _ => some none

theorem onWord64_bits {D : Type} (x : BitVec 64) (k : BitVec 64 → D) :
    onWord64 (.bits 64 x) k = some (some (k x)) := rfl

theorem onWord64_ne_none {D : Type} (v : Value) (k : BitVec 64 → D) : onWord64 v k ≠ none := by
  unfold onWord64; split <;> simp

/-- The machine stops following exactly on a value that is not a 64-bit integer. -/
theorem onWord64_eq_giveUp {D : Type} {v : Value} {k : BitVec 64 → D} :
    onWord64 v k = some none ↔ ∀ x, v ≠ .bits 64 x := by
  unfold onWord64
  split
  · simp
  · rename_i h
    simp only [true_iff]
    intro x hx
    exact h x hx

/-- **The transition at such a load**: the event is a read; bytes that do not rebuild fault the
thread (`none`), and a value that rebuilds is followed when it is a 64-bit integer
(`onWord64`). -/
def loadWord {D : Type} (e : Event) (k : BitVec 64 → D) : Option (Option D) :=
  match e.kind with
  | .rd _ bs =>
    match rebuild 3 bs with
    | .ok v => onWord64 v k
    | .error _ => none
  | _ => none

theorem loadWord_rd {D : Type} {pc : Nat} {a : Acc} {bs : List (Option Byte)} {v : Value}
    {k : BitVec 64 → D} (hv : rebuild 3 bs = .ok v) :
    loadWord ⟨pc, .rd a bs⟩ k = onWord64 v k := by
  simp only [loadWord, hv]

theorem loadWord_err {D : Type} {pc : Nat} {a : Acc} {bs : List (Option Byte)} {f : Fault}
    {k : BitVec 64 → D} (hv : rebuild 3 bs = .error f) : loadWord ⟨pc, .rd a bs⟩ k = none := by
  simp only [loadWord, hv]

/-- On bytes that rebuild to a 64-bit integer the machine follows the thread. -/
theorem loadWord_bits {D : Type} {pc : Nat} {a : Acc} {bs : List (Option Byte)} {x : BitVec 64}
    {k : BitVec 64 → D} (hv : rebuild 3 bs = .ok (.bits 64 x)) :
    loadWord ⟨pc, .rd a bs⟩ k = some (some (k x)) := by
  rw [loadWord_rd hv]; rfl

/-- **The machine stops following at such a load only on a read whose bytes rebuild to a value
that is not a 64-bit integer.** -/
theorem loadWord_giveUp {D : Type} {e : Event} {k : BitVec 64 → D}
    (h : loadWord e k = some none) :
    ∃ a bs v, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ ∀ x, v ≠ .bits 64 x := by
  obtain ⟨pc, kind⟩ := e
  unfold loadWord at h
  split at h
  · rename_i a bs hk
    split at h
    · rename_i v hv
      exact ⟨a, bs, v, hk, hv, onWord64_eq_giveUp.mp h⟩
    · cases h
  · cases h

/-- The outcome after such a load: for an integer the rest of the path, with the destination
holding it; nothing is claimed for another value. -/
theorem Local.onWord64 {q r : Nat} {v : Value} {F : List (Nat × Value)} {k : BitVec 64 → C.D}
    (h : ∀ x, Local C q ((r, .bits 64 x) :: F) (some (some (k x)))) :
    Local C q ((r, v) :: F) (onWord64 v k) := by
  unfold PTX.Kernels.FlashKdaFwd.Proof.Thread.onWord64
  split
  · exact h _
  · exact ⟨fun _ h => (by cases h), fun h => (by cases h)⟩

/-! ### Parameters -/

/-- **A scalar `ld.param`**, then the rest. -/
theorem Local.ldParam {q d w : Nat} {p : String} {x : BitVec 64} {ty : DType}
    {F : List (Nat × Value)} {o : Option (Option C.D)}
    (hc : K.code[q]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }⟩)
    (hx : L.params p = some x) (hd : ∀ r ∈ F, r.1 ≠ d)
    (hL : NoRuleAt A L g q (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }))
    (hA : Assumption.SegFreePc A q) (hw : ty.width = w)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] } = some .threadMove)
    (h : Local C (q + 1) ((d, .bits w (truncBits w x)) :: F) o) : Local C q F o :=
  Local.cut ⟨1, seg_ldParam hc hx hd hL hA hw hr⟩ h

/-- **`ld.param` of one field of a by-value parameter object, through a parameter pointer**
(`ld.param.b32 d, [r + off]` with `r` holding the object's address): one step to the
little-endian number of the field's bytes, given that the launch declares the object with the
field inside it and aligned, and supplies the field's bytes. -/
theorem Local.ldParamObj {q d r rw w off : Nat} {p : String} {ty : DType}
    {decl : ParamObjectDecl} {base : Nat} {F : List (Nat × Value)} {o : Option (Option C.D)}
    (hc : K.code[q]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.reg r rw, (off : Int)⟩, dsts := [some d] }⟩)
    (hr : (r, .ptr 64 false (.param p) 0) ∈ F) (hd : ∀ x ∈ F, x.1 ≠ d)
    (hobj : L.paramObjects p = some (decl, base)) (hin : off + w / 8 ≤ decl.bytes)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ decl.alignment % (w / 8) = 0)
    (hsup : ParamSupplied L p off (w / 8)) (hne : w ≠ 128)
    (hL : NoRuleAt A L g q (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.reg r rw, (off : Int)⟩, dsts := [some d] }))
    (hA : Assumption.SegFreePc A q) (hw : ty.width = w)
    (hrule : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.reg r rw, (off : Int)⟩, dsts := [some d] } = some .threadMove)
    (h : Local C (q + 1) ((d, .bits w (BitVec.ofNat 64 (paramNat L p off (w / 8)))) :: F) o) :
    Local C q F o := by
  refine Local.cut ⟨1, fun t ht => ⟨_, run_local hc rfl ht ?_, At.set ht hd⟩⟩ h
  subst hw
  have hreg := holds_mem ht.2.2.2.2 hr
  rw [execLocalA_core hL hA ht.1, execLocal_mem hrule]
  simp [execMove, MemAccess.regs, paramObjectOf, readReg, hreg, hobj, hin, hal,
    loadParamObject, paramObjectBits_eq hsup, paramElem_of_ne hne, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

/-! ### `mapa` -/

/-- The peer location `mapa.shared::cluster.u32 d, a, rank` names, for an address register
holding the word `xa` and a rank register holding `xr`, as Core's rule computes it: the thread
and its CTA are of the launch, and the launch maps the address into the CTA of that rank. -/
def mapaPeer (L : Launch) (g : Nat) (xa xr : BitVec 64) : Option Loc :=
  if g < L.threads ∧ g / L.block < L.grid then
    L.mapShared (g / L.block) (truncBits 32 xr).toNat
      ⟨.shared, g / L.block, (truncBits 32 xa).toNat⟩
  else none

/-- The pointer `mapa` writes for the peer location `peer`. -/
abbrev mapaVal (L : Launch) (g : Nat) (peer : Loc) : Value :=
  .ptr 32 false (.shared (g / L.block) peer.cta) (BitVec.ofNat 64 peer.addr)

/-- The transition after a `mapa`: the rest on the peer location, or a dead thread. -/
def mapaThen {D : Type} (L : Launch) (g : Nat) (xa xr : BitVec 64)
    (k : Loc → Option (Option D)) : Option (Option D) :=
  match mapaPeer L g xa xr with
  | some peer => k peer
  | none => none

theorem truncBits32_lt (x : BitVec 64) : (truncBits 32 x).toNat < 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

theorem execMapa {t : TState} {d a r wa wr : Nat} {xa xr : BitVec 64}
    (ha : t.regs a = some (.bits wa xa)) (hr : t.regs r = some (.bits wr xr)) :
    execSharedAddress L g t (.mapa false 32 d (.reg a) (.reg r)) =
      match mapaPeer L g xa xr with
      | some peer => .ok (PTX.next (setReg t d (mapaVal L g peer)))
      | none => .error .badValue := by
  have hlt := truncBits32_lt xa
  have hlt' : (truncBits 32 xa).toNat < 4294967296 := hlt
  unfold mapaPeer
  by_cases hg : g < L.threads ∧ g / L.block < L.grid
  · simp only [execSharedAddress, readSharedAddress, readValue, readReg, ha, hr, readBits, hg,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    cases hm : L.mapShared (g / L.block) (truncBits 32 xr).toNat
        ⟨.shared, g / L.block, (truncBits 32 xa).toNat⟩ <;>
      simp [hlt', hm]
  · simp only [execSharedAddress, readSharedAddress, readValue, readReg, ha, hr, readBits,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    simp [hg]

/-- **`mapa.shared::cluster.u32 d, a, rank` of two word registers**: one step to the peer
pointer in `d` and the rest, or a dead thread where the launch gives no peer location. -/
theorem Local.mapa {q d a r wa wr : Nat} {xa xr : BitVec 64} {F : List (Nat × Value)}
    {k : Loc → Option (Option C.D)}
    (hc : K.code[q]? = some ⟨none, .addr (.mapa false 32 d (.reg a) (.reg r))⟩)
    (ha : (a, .bits wa xa) ∈ F) (hr : (r, .bits wr xr) ∈ F) (hd : ∀ x ∈ F, x.1 ≠ d)
    (hL : NoRuleAt A L g q (.addr (.mapa false 32 d (.reg a) (.reg r))))
    (hA : Assumption.SegFreePc A q)
    (hk : ∀ peer, mapaPeer L g xa xr = some peer →
      Local C (q + 1) ((d, mapaVal L g peer) :: F) (k peer)) :
    Local C q F (mapaThen L g xa xr k) := by
  have hrule : (AddrInstr.mapa false 32 d (.reg a) (.reg r)).rule =
      some .threadSharedPointer := rfl
  have hex : ∀ t : TState, t.pc = q → Holds t.regs F →
      execLocalA A L g t (.addr (.mapa false 32 d (.reg a) (.reg r))) =
        match mapaPeer L g xa xr with
        | some peer => .ok (PTX.next (setReg t d (mapaVal L g peer)))
        | none => .error .badValue := by
    intro t htq hF
    rw [execLocalA_core hL hA htq, execLocal_shared hrule,
      execMapa (holds_mem hF ha) (holds_mem hF hr)]
  unfold mapaThen
  cases hm : mapaPeer L g xa xr with
  | none =>
    refine Local.dead_of (DeadFrom.local_error hc rfl fun R cf hR => ⟨.badValue, ?_⟩)
    rw [hex ⟨q, R, cf, 0, [], none⟩ rfl hR, hm]
  | some peer =>
    refine Local.cut ⟨1, fun t ht => ⟨_, run_local hc rfl ht ?_, At.set ht hd⟩⟩ (hk peer hm)
    rw [hex t ht.1 ht.2.2.2.2, hm]

theorem mapaThen_ne {D : Type} {L : Launch} {g : Nat} {xa xr : BitVec 64}
    {k : Loc → Option (Option D)} (h : ∀ peer, k peer ≠ some none) :
    mapaThen L g xa xr k ≠ some none := by
  unfold mapaThen
  split
  · exact h _
  · simp

/-! ### `trap` -/

/-- A `trap` instruction is undefined behaviour: a thread that reaches it is dead. -/
theorem deadFrom_trap {q : Nat} {F : List (Nat × Value)}
    (hc : K.code[q]? = some ⟨none, .trap⟩) : DeadFrom K A L g q F := by
  intro u hu
  refine Machine.dead_of_ub (f := .trap) ?_
  have hc' : K.code[u.pc]? = some ⟨none, .trap⟩ := by rw [hu.1]; exact hc
  simp [out, hu.2.2.2.1, hc', guardHolds, Op.isLocal, eventTmpl, pure, Except.pure]

/-- A `trap` fires no event that continues (the step obligation of a state at a `trap`). -/
theorem step_trap {d : C.D} {gd : Option (Nat × Bool)}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .trap⟩) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  simp [eventTmpl, Fires] at hf

/-! ### Step combinators in outcome form -/

/-- An event that continues at the next instruction whatever it observed (`step_issue`), with
any outcome of the local code after it. -/
theorem step_issue_o {d : C.D} {o : Option (Option C.D)} {ins0 : Instr}
    (hc0 : K.code[C.pc d]? = some ins0)
    (hadv : ∀ {t e u}, Fires (C.pc d) (eventTmpl A L g t ins0.op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = o) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : Local C (C.pc d + 1) (C.facts d) o) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := hadv hf
  exact hl.cont (hn e) (At.next (at_of_atD h hs ha))

/-- An arrival without a state register (`step_arrive`), with any outcome after it. -/
theorem step_arrive_o {d : C.D} {o : Option (Option C.D)} {gd : Option (Nat × Bool)}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster release : Bool} {sc : MbarScope}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarArrive base off tx count cluster release sc none⟩)
    (hn : ∀ e, C.next d e = o) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : Local C (C.pc d + 1) (C.facts d) o) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := fires_arrive_next hf
  exact hl.cont (hn e) (At.next (at_of_atD h hs ha))

/-- An mbarrier poll into predicate `p` (`step_wait`): the successor is any function `ov` of
whether the phase was found complete. -/
theorem step_wait_o {d : C.D} {ov : Bool → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mbarWait p base off par acq sc⟩)
    (hp : ∀ q ∈ C.facts d, q.1 ≠ p)
    (hn : ∀ m q ok a s, C.next d ⟨C.pc d, .wait m q ok a s⟩ = ov ok)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ ok, Local C (C.pc d + 1) ((p, .pred ok) :: C.facts d) (ov ok)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  rw [← h.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [h.1]
  exact (hl ok).cont (hn m q ok acq s) (At.set (r := p) (v := .pred ok) h0 hp)

/-- An election into predicate `p` and the leader register `r` (`step_elect`): the successor is
any function `ov` of the elected lane and of whether this lane is it. -/
theorem step_elect_o {d : C.D} {ov : Nat → Bool → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hrp : r ≠ p)
    (hn : ∀ mk inst ld, C.next d ⟨C.pc d, .elect mk inst ld⟩ = ov ld (laneOf L g == ld))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ ld b, Local C (C.pc d + 1)
      ((p, .pred b) :: (r, .bits 32 (BitVec.ofNat 64 ld)) :: C.facts d) (ov ld b)) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  have h1 : At (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) (C.pc d)
      ((r, .bits 32 (BitVec.ofNat 64 ld)) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  exact (hl ld (laneOf L g == ld)).cont (hn mk inst ld)
    (At.set h1 (keys_cons hrp hp))

/-- A scalar load into register `r` (`step_load_dead`): the successor is any function `nv` of
the value read; bytes that do not rebuild fault the thread. -/
theorem step_load_o {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} {r : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same) (hregs : a.regs = [r])
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ v, Local C (C.pc d + 1) ((r, v) :: C.facts d) (nv v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hst : { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } =
        PTX.next (setReg t r v) := by
      have hs0 := h0.2.1
      have ha0 := h0.2.2.1
      cases t
      simp_all [PTX.next, setReg]
    rw [afterLoad_ok h0.2.1 h0.2.2.1 hv, hst]
    exact (hl v).cont (hok x bs v hv) (At.set h0 hr)

/-- The last element of a store (`step_vec_last`), with any outcome after it. -/
theorem step_store_o {d : C.D} {o : Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .store)
    (hsub : ¬ C.sub d + 1 < a.srcs.length) (hn : ∀ e, C.next d e = o)
    (ha : C.acc d = []) (hl : Local C (C.pc d + 1) (C.facts d) o) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_st hk hf
  rw [afterStore_last (by rw [h.2.1]; exact hsub)]
  exact hl.cont (hn _) ⟨by simp [h.1], rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩

/-- An element of a vector load other than the last (`step_ldv_mid`): the machine moves to
`dok v`, the state at the same instruction one sub-step later that has accumulated `v`. -/
theorem step_ldv_mid_o {d : C.D} {dok : Value → C.D} {gd : Option (Nat × Bool)}
    {a : MemAccess} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hsub : C.sub d + 1 < a.regs.length)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none)
    (hpc : ∀ v, C.pc (dok v) = C.pc d) (hs : ∀ v, C.sub (dok v) = C.sub d + 1)
    (ha : ∀ v, C.acc (dok v) = C.acc d ++ [v]) (hF : ∀ v, C.facts (dok v) = C.facts d)
    (hinv : ∀ v, C.inv d → C.inv (dok v)) : C.StepOk d :=
  step_ldv_mid hc0 hk hnc he hsub hok herr hpc hs ha hF hinv

/-- The last element of a vector load (`step_ldv_last_sel`): the destinations receive the
accumulated values and the last one, and the successor is any function `nv` of the value read,
with any outcome of the local code after the load. -/
theorem step_ldv_last_o {d : C.D} {nv : Value → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : ¬ C.sub d + 1 < a.regs.length) (hnd : a.regs.Nodup)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none)
    (hl : ∀ v, Local C (C.pc d + 1) (vecFacts a.regs (C.acc d ++ [v]) (C.facts d)) (nv v)) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hm : ¬ t.sub + 1 < a.regs.length := by rw [h.2.1]; exact hsub
    have hu : afterLoad t a.regs bs =
        { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hm]
    rw [hu]
    have hsk := setRegs_skel t a.regs (t.acc ++ [v])
    refine (hl v).cont (hok x bs v hv) ⟨?_, rfl, rfl, ?_, ?_⟩
    · show t.pc + 1 = C.pc d + 1
      rw [h.1]
    · show (setRegs t a.regs (t.acc ++ [v])).fault = none
      rw [hsk.2.2.2]; exact h.2.2.2.1
    · show Holds (setRegs t a.regs (t.acc ++ [v])).regs _
      rw [h.2.2.1]; exact holds_vecFacts hnd h.2.2.2.2

/-- **The last element of a vector load**, in continuation form (as `step_load_x`): for bytes
that rebuild to `v` the caller gets the state after the load, where the destinations hold the
accumulated values and `v`; bytes that do not rebuild fault the thread. -/
theorem step_ldv_last_x {d : C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hsub : ¬ C.sub d + 1 < a.regs.length) (hnd : a.regs.Nodup)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.inv d →
      ∀ u, At u (C.pc d + 1) (vecFacts a.regs (C.acc d ++ [v]) (C.facts d)) →
        C.Cont d ⟨C.pc d, .rd x bs⟩ u)
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    have hm : ¬ t.sub + 1 < a.regs.length := by rw [h.2.1]; exact hsub
    have hu : afterLoad t a.regs bs =
        { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hm]
    rw [hu]
    have hsk := setRegs_skel t a.regs (t.acc ++ [v])
    refine hok x bs v hv hi _ ⟨?_, rfl, rfl, ?_, ?_⟩
    · show t.pc + 1 = C.pc d + 1
      rw [h.1]
    · show (setRegs t a.regs (t.acc ++ [v])).fault = none
      rw [hsk.2.2.2]; exact h.2.2.2.1
    · show Holds (setRegs t a.regs (t.acc ++ [v])).regs _
      rw [h.2.2.1]; exact holds_vecFacts hnd h.2.2.2.2

end Generic

end

/-! ### Tactics -/

/-- Close a segment: evaluation on the footprint, each value equation by `rfl`, else by
deciding the conditions of the stated value (`sym_close`). -/
macro "ev_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- A piece of evaluated code, `∃ n, Seg … s F b G`, between two cut points: the walk through
the branches the hypotheses in context decide (`seg_sym`), else plain evaluation (`seg_auto`). -/
macro "lseg" : tactic => `(tactic| (
  site_norm
  try drop_norm
  first
    | seg_sym using ev_seg
    | seg_auto using ev_seg))

/-- `∀ x ∈ F, x.1 ≠ d` for facts `F` that are explicit facts in front of a table: the register
`d` is none of the explicit keys and is not live in the table. -/
macro "fresh_key" : tactic => `(tactic| (
  site_norm
  repeat (first
    | exact PTX.Flow.not_mem_factsFrom (by lit_not_mem)
    | refine PTX.Kernels.FlashKdaFwd.Proof.Thread.keys_cons (by decide) ?_)))

/-- `ev_issue o hl trans [lemmas]`: the obligation `C.StepAt d` of a literal site whose event
continues at the next instruction whatever it observed (an initialization, a fence, a copy
issue, a barrier, a commit, a group wait), with the outcome `o` of the local code after it,
proved by `hl : Local C (pc + 1) (C.facts d) o`. -/
syntax "ev_issue " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_issue $o $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_issue_o (o := $o)
        ?hc ?hadv ?hn ?hs ?ha ?hl)
      case hc => code_lookup
      case hadv => advances
      case hs => rfl
      case ha => rfl
      case hn => intro e; next_simp [$ls,*]; done
      case hl => site_norm; exact $hl))

/-- `ev_arrive o hl trans [lemmas]`: the same for an mbarrier arrival without a state
register. -/
syntax "ev_arrive " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_arrive $o $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_arrive_o (o := $o)
        ?hc ?hn ?hs ?ha ?hl)
      case hc => code_lookup
      case hs => rfl
      case ha => rfl
      case hn => intro e; next_simp [$ls,*]; done
      case hl => site_norm; exact $hl))

/-- `ev_store o hl trans [lemmas]`: the same for a scalar store. -/
syntax "ev_store " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_store $o $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_store_o (o := $o)
        ?hc ?hk ?hsub ?hn ?ha ?hl)
      case hc => code_lookup
      case hk => rfl
      case hsub => exact of_decide_eq_false rfl
      case ha => rfl
      case hn => intro e; next_simp [$ls,*]; done
      case hl => site_norm; exact $hl))

/-- `ev_wait ov hl trans [lemmas]`: the obligation of a literal `mbarrier.try_wait` site whose
successor is the function `ov` of the poll's outcome, with
`hl : ∀ ok, Local C (pc + 1) ((p, .pred ok) :: C.facts d) (ov ok)`. -/
syntax "ev_wait " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_wait $ov $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_wait_o (ov := $ov)
        ?hc ?hp ?hn ?hs ?ha ?hl)
      case hc => code_lookup
      case hp => fact_free
      case hs => rfl
      case ha => rfl
      case hn => intro m q ok a s; next_simp [$ls,*]; done
      case hl => site_norm; exact $hl))

/-- `ev_elect ov hl trans [lemmas]`: the obligation of a literal election site whose successor
is the function `ov` of the elected lane and of whether this lane is it, with
`hl : ∀ ld b, Local C (pc + 1) ((px, .pred b) :: (rx, leader) :: C.facts d) (ov ld b)`. -/
syntax "ev_elect " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_elect $ov $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_elect_o (ov := $ov)
        ?hc ?hp ?hr ?hrp ?hn ?hs ?ha ?hl)
      case hc => code_lookup
      case hp => fact_free
      case hr => fact_free
      case hrp => decide
      case hs => rfl
      case ha => rfl
      case hn => intro mk inst ld; next_simp [$ls,*]; done
      case hl => site_norm; exact $hl))

/-- `ev_load nv hl trans [lemmas]`: the obligation of a literal scalar load site whose
successor is the function `nv` of the value read, with
`hl : ∀ v, Local C (pc + 1) ((r, v) :: C.facts d) (nv v)`. -/
syntax "ev_load " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_load $nv $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_load_o (nv := $nv)
        ?hc ?hk ?hnc ?he ?hregs ?hr ?hok ?herr ?hs ?ha ?hl)
      case hc => code_lookup
      case hk => rfl
      case hnc => rfl
      case he => rfl
      case hregs => rfl
      case hs => rfl
      case ha => rfl
      case hr => fact_free
      case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
      case herr => intro x bs f hv; next_simp [hv, $ls,*]; done
      case hl => site_norm; exact $hl))

/-- `ev_ldv_mid dok trans [lemmas]`: the obligation of a literal state at an element of a
vector load other than the last; `dok v` is the state one sub-step later. -/
syntax "ev_ldv_mid " term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_ldv_mid $dok trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_ldv_mid_o (dok := $dok)
        ?hc ?hk ?hnc ?he ?hsub ?hok ?herr ?hpc ?hs ?ha ?hF ?hinv)
      case hc => code_lookup
      case hk => rfl
      case hnc => rfl
      case he => rfl
      case hsub => exact of_decide_eq_true rfl
      case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
      case herr => intro x bs f hv; next_simp [hv, $ls,*]; done
      case hpc => intro v; rfl
      case hs => intro v; rfl
      case ha => intro v; rfl
      case hF => intro v; rfl
      case hinv => intro v _; trivial))

/-- `ev_ldv_last nv hl trans [lemmas]`: the obligation of a literal state at the last element
of a vector load, whose successor is the function `nv` of the value read, with `hl` the outcome
of the local code from the facts after the load (`vecFacts`, written out by `vec_facts_norm`). -/
syntax "ev_ldv_last " term:max term:max " trans " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ev_ldv_last $nv $hl trans [$ls,*]) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of ?site ?_
      case site => site_event (trivial)
      refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_ldv_last_o (nv := $nv)
        ?hc ?hk ?hnc ?he ?hsub ?hnd ?hok ?herr ?hl)
      case hc => code_lookup
      case hk => rfl
      case hnc => rfl
      case he => rfl
      case hsub => exact of_decide_eq_false rfl
      case hnd => decide
      case hok => intro x bs v hv; next_simp [hv, $ls,*]; done
      case herr => intro x bs f hv; next_simp [hv, $ls,*]; done
      case hl => intro v; site_norm; vec_facts_norm; exact $hl v))

/-- `ev_trap`: the obligation of a literal state at a `trap` (no event continues). -/
macro "ev_trap" : tactic => `(tactic| (
  refine PTX.Flow.Code.StepAt.of ?site ?_
  case site => site_event (trivial)
  refine' (PTX.Kernels.FlashKdaFwd.Proof.Thread.step_trap ?hc)
  case hc => code_lookup))

end PTX.Kernels.FlashKdaFwd.Proof.Thread
