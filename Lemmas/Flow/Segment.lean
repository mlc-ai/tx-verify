-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # One step over a segment an assumption selects

A proof tool. At a site where an assumption of the list selects a segment (`segmentRule`,
THREAD-LOCAL), the local step is that assumption's outcome, provided no earlier assumption
selects one there (`run_select`; the list is written `A₁ ++ a :: A₂`, with `A₁` usually given
explicitly). For the two segment constructors:

* `run_segmentExact`: at a site of `segmentExact` where the template matches, the step is the
  template's step; `run_segmentExact_two` computes it for a two-lane template such as the
  software `exp2` (`Assumption.cuteExp2`): the output registers receive `.float .f32 (fn x)` of
  their inputs, the other registers it writes are cleared (`Assumption.segRegs_cleared`) and
  every other register is kept (`Assumption.segRegs_frame`), and execution continues after the
  instance.
* `run_pairEvenAt`: at a site of `pairEvenAt`, `and.b32 d, a, -16777217` of a `.shared::cta`
  window address below `2 ^ 24` gives the `.shared::cluster` address of the same byte in the
  even CTA of the pair. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {K : Kernel} {A₁ A₂ : List Assumption} {L : Launch} {g pc : Nat} {t t' : TState}
  {F : List (Nat × Value)}

/-- **One step at a selected site**: the outcome of the first assumption that selects a
segment. -/
theorem run_select {a : Assumption} {op : Op} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (h : At t pc F) (ha : a.segmentRule L g t = some (.ok t'))
    (h₁ : SegFreePc A₁ pc := by seg_free_pc) :
    run K (A₁ ++ a :: A₂) L g 1 t = some t' :=
  run_local hc hl h (execLocalA_select (h₁.at h.1) ha)

/-- **A local step that an assumption's segment takes, as a piece**: at a site where an
assumption takes a straight-line stretch of the code as one local step (`segmentRule`), the step
from `pc` reaches the state the segment names, at the program counter `b` the segment continues
at; the facts `G` hold in it. The premises are read off the segment's own rule: the instruction
is local, and on every state at `pc` whose registers satisfy `F` the step is an `ok` whose state
has the projections and the facts `G`. This is the piece a segment-assumption site needs in
`seg_sym`, where no instruction rule of the code describes the step. -/
theorem Seg.segStep {pc b : Nat} {op : Op} {F G : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hstep : ∀ R cf, Holds R F → ∃ t' : TState,
      execLocalA A L g ⟨pc, R, cf, 0, [], none⟩ op = .ok t' ∧ t'.pc = b ∧ t'.sub = 0 ∧
        t'.acc = [] ∧ t'.fault = none ∧ Holds t'.regs G) :
    ∃ n, Seg K A L g n pc F b G := by
  refine ⟨1, ?_⟩
  intro t h
  obtain ⟨tpc, R, cf, sub, acc, fault⟩ := t
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4
  obtain ⟨t', he, hpc, hsub, hacc, hfault, hG⟩ := hstep R cf h5
  exact ⟨t', run_local hc hl ⟨rfl, rfl, rfl, rfl, h5⟩ he,
    ⟨hpc, hsub, hacc, hfault, hG⟩⟩

/-- **A run step that an assumption's segment takes, as a piece**: at a site where an assumption
takes a straight-line stretch of the code as one local step, the engine run of one step from the
state at `pc` reaches the state the segment names, at the program counter `b`, where the facts `G`
hold. The kernel states the step's result and its proof (the lanes of a software `exp2` are the
values the segment computes); this lemma turns that statement into the piece `seg_sym` glues. -/
theorem Seg.segRunStep {pc b : Nat} {F G : List (Nat × Value)}
    (hstep : ∀ R cf, Holds R F → ∃ u : TState,
      run K A L g 1 ⟨pc, R, cf, 0, [], none⟩ = some u ∧ u.pc = b ∧ u.sub = 0 ∧
        u.acc = [] ∧ u.fault = none ∧ Holds u.regs G) :
    ∃ n, Seg K A L g n pc F b G := by
  refine ⟨1, ?_⟩
  intro t h
  obtain ⟨tpc, R, cf, sub, acc, fault⟩ := t
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4
  obtain ⟨u, hu, hpc, hsub, hacc, hfault, hG⟩ := hstep R cf h5
  exact ⟨u, hu, ⟨hpc, hsub, hacc, hfault, hG⟩⟩

/-- One step at a site of `segmentExact` where the template matches: the template's step. -/
theorem run_segmentExact {σ : Type} [DecidableEq σ] {name why : String} {T : SegTemplate σ}
    {sites : List Nat} {m : SegMatch σ} {op : Op} (hc : K.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (h : At t pc F) (hs : sites.contains pc = true)
    (hm : T.matchAt K pc = some m) (hex : execSegment T.fn m t = .ok t')
    (h₁ : SegFreePc A₁ pc := by seg_free_pc) :
    run K (A₁ ++ segmentExact K name T sites why :: A₂) L g 1 t = some t' := by
  refine run_select hc hl h ?_ h₁
  rw [segmentExact_select (h.1 ▸ hs) h.2.1 h.2.2.1 (h.1 ▸ hm), hex]

/-- **One step over a two-lane segment**: at a site of `segmentExact` where the template
matches with inputs `i₀`, `i₁` and outputs `o₀`, `o₁`, when the constants are defined or
present and the inputs hold `f32` numbers `x₀`, `x₁`, the outputs receive `fn x₀` and `fn x₁`
and execution continues after the instance. -/
theorem run_segmentExact_two {σ : Type} [DecidableEq σ] {name why : String}
    {T : SegTemplate σ} {sites : List Nat} {m : SegMatch σ} {op : Op} {i₀ o₀ i₁ o₁ : σ}
    {v₀ v₁ : Value} {x₀ x₁ : ℝ} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (h : At t pc F) (hs : sites.contains pc = true) (hm : T.matchAt K pc = some m)
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hcst : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2)
    (h₀ : (m.regOf i₀, v₀) ∈ F) (hx₀ : valFloat .f32 v₀ = .ok x₀)
    (h₁' : (m.regOf i₁, v₁) ∈ F) (hx₁ : valFloat .f32 v₁ = .ok x₁)
    (h₁ : SegFreePc A₁ pc := by seg_free_pc) :
    run K (A₁ ++ segmentExact K name T sites why :: A₂) L g 1 t = some { t with
      regs := segRegs m t [(m.regOf o₀, .float .f32 (T.fn x₀)),
        (m.regOf o₁, .float .f32 (T.fn x₁))],
      pc := m.stop, sub := 0, acc := [] } :=
  run_segmentExact hc hl h hs hm (execSegment_two hio hcst (holds_mem h.2.2.2.2 h₀) hx₀
    (holds_mem h.2.2.2.2 h₁') hx₁) h₁

/-- **One step over the peer-bit `and`**: at a site of `pairEvenAt`, a register holding a
`.shared::cta` window address below `2 ^ 24`, in a launch whose cluster of the executing CTA has
even size, gives the `.shared::cluster` address of the same byte in the even CTA of the pair. -/
theorem run_pairEvenAt {name why : String} {sites : List Nat} {d a w : Nat} {x : BitVec 64}
    {even : Nat} (hc : K.code[pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some d],
      [.reg a, .imm peerBitMask]⟩⟩)
    (h : At t pc F) (hs : sites.contains pc = true) (hr : (a, .bits w x) ∈ F)
    (hoff : (truncBits 32 x).toNat < 2 ^ 24)
    (hcl : L.clusterSizeOf (g / L.block) % 2 = 0)
    (hp : L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2) = some even)
    (h₁ : SegFreePc A₁ pc := by seg_free_pc) :
    run K (A₁ ++ pairEvenAt K name sites why :: A₂) L g 1 t =
      some (next (setReg t d (.ptr 32 false (.shared (g / L.block) even)
        (BitVec.ofNat 64 (truncBits 32 x).toNat)))) := by
  refine run_select hc rfl h ?_ h₁
  rw [pairEvenAt_select (h.1 ▸ hs) h.2.1 (h.1 ▸ hc),
    execPairEven_ok (holds_mem h.2.2.2.2 hr) hoff hcl hp]

end
end PTX.Flow
