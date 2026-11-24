-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

/-! # The interface between the thread layer and the layers above

The layers above the thread layer see the threads only through `ThreadFacts`: what each thread
does along its own events, stated with the abstract state its machine (`codes`) is in before an
event (`stateAt`): the event of its site (`siteTmpl`), its position in the trace (`D.idx`), the
numbers of barrier arrivals and shuffles before it (`D.bc0`, `D.bc1`, `D.sc`), and how the data
the state holds derive from the earlier events of its row (`RowData`). The thread layer proves
`ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

/-- The machines of the threads. -/
abbrev codes (P : Params) (L : Launch) (g : Nat) : Flow.Code kernel Prod L g := code P L g

/-- The abstract state of thread `g` before its `k`-th event. -/
abbrev stateAt (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Option (Option D) :=
  Frame.stateAt (codes P L) X g k

/-! ### Positions within a row -/

/-- `1` for lane 0 of a warp. -/
def l0 (g : Nat) : Nat := if g % 256 % 32 = 0 then 1 else 0
/-- `1` for the threads 0..7 of a CTA. -/
def l8 (g : Nat) : Nat := if g % 256 < 8 then 1 else 0
/-- `1` for warp 0 of a CTA. -/
def w0 (g : Nat) : Nat := if g % 256 < 32 then 1 else 0
/-- `1` for thread 0 of a CTA. -/
def t0 (g : Nat) : Nat := if g % 256 = 0 then 1 else 0

/-- The offset of the second barrier in a row. -/
def p1 (g : Nat) : Nat := 30 + l0 g + 5 * w0 g + l8 g + t0 g

/-- The number of events of a row. -/
def rowLen (g : Nat) : Nat := p1 g + 35

/-- The offset of a state's event within its row. -/
def D.pos (g : Nat) (d : D) : Nat :=
  match d.site with
  | .shfl0 | .exit => 0
  | .ldxa => d.sub | .stxa0 => 4 + d.sub | .stxa1 => 8 + d.sub | .ldxb => 12 + d.sub
  | .stxb0 => 16 + d.sub | .stxb1 => 20 + d.sub | .bfa k => 24 + k | .stws => 29
  | .bar0 => 29 + l0 g | .ldws => 30 + l0 g | .bfb k => 30 + l0 g + l8 g + k
  | .stts => 35 + l0 g + l8 g | .bar1 => p1 g | .ldts => p1 g + 1
  | .ldwa => p1 g + 2 + d.sub | .ldsa0 => p1 g + 6 + d.sub | .ldsa1 => p1 g + 10 + d.sub
  | .stoa => p1 g + 14 + d.sub | .ldwb => p1 g + 18 + d.sub | .ldsb0 => p1 g + 22 + d.sub
  | .ldsb1 => p1 g + 26 + d.sub | .stob => p1 g + 30 + d.sub | .bar2 => p1 g + 34

/-- The offset of the first element of a vector access within its row. -/
def D.vbase (g : Nat) (d : D) : Nat :=
  match d.site with
  | .ldxa => 0 | .stxa0 => 4 | .stxa1 => 8 | .ldxb => 12 | .stxb0 => 16 | .stxb1 => 20
  | .ldwa => p1 g + 2 | .ldsa0 => p1 g + 6 | .ldsa1 => p1 g + 10 | .stoa => p1 g + 14
  | .ldwb => p1 g + 18 | .ldsb0 => p1 g + 22 | .ldsb1 => p1 g + 26 | .stob => p1 g + 30
  | _ => 0

/-- The position of the first event of row iteration `i` in the trace. -/
def rowBase (g i : Nat) : Nat := 1 + rowLen g * i

/-- The position of a state's event in its thread's trace: the shuffle first, then the rows, and
the exit after the last row. -/
def D.idx (g : Nat) (d : D) : Nat :=
  match d.site with
  | .shfl0 => 0
  | .exit => rowBase g d.i
  | _ => rowBase g d.i + d.pos g

/-- The arrivals on barrier `0` before a state's event: two per completed row, then the first
and second barrier of the current row. -/
def D.bc0 (d : D) : Nat :=
  match d.site with
  | .shfl0 => 0
  | .ldxa | .stxa0 | .stxa1 | .ldxb | .stxb0 | .stxb1 | .bfa _ | .stws | .bar0 | .exit => 2 * d.i
  | .ldws | .bfb _ | .stts | .bar1 => 2 * d.i + 1
  | _ => 2 * d.i + 2

/-- The arrivals on barrier `1` before a state's event: one per completed row. -/
def D.bc1 (d : D) : Nat :=
  match d.site with
  | .shfl0 => 0
  | _ => d.i

/-- The shuffles before a state's event: the warp-index shuffle, five per row (ten in warp 0),
and the rounds of the current row before it. -/
def D.sc (g : Nat) (d : D) : Nat :=
  match d.site with
  | .shfl0 => 0
  | .ldxa | .stxa0 | .stxa1 | .ldxb | .stxb0 | .stxb1 | .exit => 1 + 5 * (1 + w0 g) * d.i
  | .bfa k => 1 + 5 * (1 + w0 g) * d.i + k
  | .stws | .bar0 | .ldws => 1 + 5 * (1 + w0 g) * d.i + 5
  | .bfb k => 1 + 5 * (1 + w0 g) * d.i + 5 + k
  | _ => 1 + 5 * (1 + w0 g) * d.i + 5 + 5 * w0 g

/-! ### The data of a row -/

/-- The value the bytes of a read event rebuild to (`b32 0` for another event). -/
def rdv : Option Event → Value
  | some ⟨_, .rd _ bs⟩ => match rebuild 3 bs with
    | .ok v => v
    | .error _ => b32 0
  | _ => b32 0

/-- The values of the four reads at positions `p`, ..., `p + 3`. -/
def rv4 (es : List Event) (p : Nat) : List Value :=
  [rdv es[p]?, rdv es[p + 1]?, rdv es[p + 2]?, rdv es[p + 3]?]

/-- The value a shuffle event received (`b32 0` for another event). -/
def recvOf : Option Event → Value
  | some ⟨_, .shfl _ _ _ _ recv _⟩ => recv
  | _ => b32 0

/-- The data a state of a row holds, from the earlier events `es` of its row (base `b`,
offset `p`): the values a vector load has read so far, the words of the inputs, the values received
in the butterflies, warp 0's warp sum, the total, and the raw values of the weight loads and the
reloads of the inputs, each from the event that read it once the state is past it. -/
structure RowData (P : Params) (g : Nat) (d : D) (es : List Event) : Prop where
  acc : d.site.vload = true → d.acc = (rv4 es (rowBase g d.i + d.vbase g)).take d.sub
  xa : d.site.inRow = true → 4 ≤ d.pos g → d.xa = rv4 es (rowBase g d.i)
  xb : d.site.inRow = true → 16 ≤ d.pos g → d.xb = rv4 es (rowBase g d.i + 12)
  ra : d.site.inRow = true → ∀ k < 5, 24 + k < d.pos g →
    d.ra k = recvOf es[rowBase g d.i + 24 + k]?
  u : d.site.inRow = true → g % 256 < 32 → 30 + l0 g + l8 g ≤ d.pos g →
    d.u = if g % 256 < 8 then rdv es[rowBase g d.i + 30 + l0 g]? else b32 0
  rb : d.site.inRow = true → g % 256 < 32 → ∀ k < 5, 30 + l0 g + l8 g + k < d.pos g →
    d.rb k = recvOf es[rowBase g d.i + 30 + l0 g + l8 g + k]?
  tt : d.site.inRow = true → p1 g + 1 < d.pos g → d.tt = rdv es[rowBase g d.i + p1 g + 1]?
  rawa : d.site.inRow = true → p1 g + 6 ≤ d.pos g → d.pos g < p1 g + 18 →
    d.raw = rv4 es (rowBase g d.i + p1 g + 2)
  rawb : d.site.inRow = true → p1 g + 22 ≤ d.pos g → d.raw = rv4 es (rowBase g d.i + p1 g + 18)
  rs0a : d.site.inRow = true → p1 g + 10 ≤ d.pos g → d.pos g < p1 g + 26 →
    d.rs0 = rv4 es (rowBase g d.i + p1 g + 6)
  rs0b : d.site.inRow = true → p1 g + 26 ≤ d.pos g → d.rs0 = rv4 es (rowBase g d.i + p1 g + 22)
  rs1a : d.site.inRow = true → p1 g + 14 ≤ d.pos g → d.pos g < p1 g + 18 →
    d.rs1 = rv4 es (rowBase g d.i + p1 g + 10)
  rs1b : d.site.inRow = true → p1 g + 30 ≤ d.pos g → d.rs1 = rv4 es (rowBase g d.i + p1 g + 26)

/-- The event of a state's site. -/
def SiteEvent (P : Params) (g : Nat) (d : D) (e : Event) : Prop :=
  ∃ t o, Fires d.site.pc (siteTmpl P g d t) e o

/-- Per-thread facts of an execution. -/
structure ThreadFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- Every launched thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (codes P L) X
  /-- A followed state satisfies its invariant. -/
  inv : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt P L X g k = some (some d) → Inv P g d
  /-- An event of a followed thread is its state's site event. -/
  event : ∀ {g k : Nat} {e : Event} {d : D}, g < L.threads → X.get (g, k) = some e →
    stateAt P L X g k = some (some d) → SiteEvent P g d e
  /-- A followed state's event is at its position. -/
  index : ∀ {g k : Nat} {d : D}, g < L.threads → k ≤ (X.tr g).length →
    stateAt P L X g k = some (some d) → k = d.idx g
  /-- The barrier arrivals and shuffles before a followed state's event. -/
  counts : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt P L X g k = some (some d) →
    ((X.tr g).take k).countP (Execution.isBarId 0) = d.bc0 ∧
    ((X.tr g).take k).countP (Execution.isBarId 1) = d.bc1 ∧
    ((X.tr g).take k).countP Execution.isShfl = d.sc g
  /-- The data a followed state holds. -/
  data : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt P L X g k = some (some d) →
    RowData P g d ((X.tr g).take k)
  /-- The machine stops only after an event its transition rejects. -/
  dead : ∀ {g k : Nat}, g < L.threads → k ≤ (X.tr g).length → stateAt P L X g k = none →
    ∃ j d e, j < k ∧ stateAt P L X g j = some (some d) ∧ X.get (g, j) = some e ∧
      next P g d e = none
  /-- Undefined behaviour comes after the machine stopped. -/
  ub : ∀ {g k pc : Nat} {f : Fault}, g < L.threads → X.get (g, k) = some ⟨pc, .ub f⟩ →
    stateAt P L X g k = none
  /-- A thread whose run has not ended is about to perform its machine's last site's event, at
  the site's instruction. -/
  fire : ∀ {g : Nat} {t : TState} {d : D}, g < L.threads →
    Run kernel Prod L g {} (X.tr g) (some t) →
    stateAt P L X g (X.tr g).length = some (some d) →
    ∃ t1, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ t1.pc = d.site.pc ∧
      out kernel Prod L g t1 = .ev (siteTmpl P g d t1)

end
end PTX.Kernels.RmsNorm.Proof
