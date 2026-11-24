-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.SegmentExact
public import Core.Assumption.PairEven

@[expose] public section

/-! # Where an assumption list takes a segment

A proof tool. `execLocalA` first asks the assumptions for a segment at the thread's state
(`segmentRule`, THREAD-LOCAL). A kernel whose assumptions read some straight-line code as one
step (`segmentExact`, `pairEvenAt`) still runs Core's local rule everywhere else:

* `SegFreeAt A L g t`: no assumption of `A` takes a segment at the state `t`; then the local step
  is the local rule (`SegFreeAt.exec`).
* `SegFreePc A pc`: the same at every state at `pc` (`SegFreePc.at`), the form a lemma about one
  instruction takes and a tactic proves for a literal `pc` (`seg_free_pc`): an assumption with
  no segment hook by `rfl`, a `segmentExact` or `pairEvenAt` whose sites do not contain `pc`
  by evaluating the site list (`segmentExact_segFreePc`, `pairEvenAt_segFreePc`).
* `SegSites A S`: every segment of `A` starts at a pc of `S`, for statements about every pc
  (`SegSites.pc`); with no site a branch, no branch takes a segment (`SegFreeBra.of_sites`).

At a selected site the step is the selecting assumption's outcome (`execLocalA_select`):
`segmentExact_select` and `pairEvenAt_select` give it from the constructors' definitions,
`execPairEven_ok` computes the peer-bit step, and `execSegment_two` the step of a two-lane
template such as the software `exp2`: each output register receives `.float .f32 (fn x)` of its
input (`segRegs_two_out`), the other written registers are cleared (`segRegs_cleared`) and
every other register is kept (`segRegs_frame`). -/

namespace PTX.Assumption

noncomputable section

/-- No assumption of `A` takes a segment at the state `t`. -/
def SegFreeAt (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : Prop :=
  ∀ a ∈ A, a.segmentRule L g t = none

/-- No assumption of `A` takes a segment at a state at `pc`. -/
def SegFreePc (A : List Assumption) (pc : Nat) : Prop :=
  ∀ a ∈ A, ∀ L g (t : TState), t.pc = pc → a.segmentRule L g t = none

/-- Every segment an assumption of `A` takes starts at a pc of `S`. -/
def SegSites (A : List Assumption) (S : List Nat) : Prop :=
  ∀ a ∈ A, ∀ L g (t : TState), t.pc ∉ S → a.segmentRule L g t = none

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- Without a segment at the state, the local step is the local rule. -/
theorem SegFreeAt.exec (h : SegFreeAt A L g t) {op : Op} :
    execLocalA A L g t op = execLocalRule A L g t op :=
  execLocalA_noSegment h

theorem SegFreePc.at {pc : Nat} (h : SegFreePc A pc) (hpc : t.pc = pc) : SegFreeAt A L g t :=
  fun a ha => h a ha L g t hpc

/-- Without a segment at `pc`, the local step of a state at `pc` is the local rule. -/
theorem SegFreePc.exec {pc : Nat} (h : SegFreePc A pc) {op : Op} (hpc : t.pc = pc) :
    execLocalA A L g t op = execLocalRule A L g t op :=
  (h.at hpc).exec

/-- `SegFreePc.at` with the position first, so that a tactic finds it before the list. -/
theorem SegFreeAt.of_pc {pc : Nat} (hpc : t.pc = pc) (h : SegFreePc A pc) : SegFreeAt A L g t :=
  h.at hpc

theorem SegFreePc.of_eq {pc pc' : Nat} (hpc : pc = pc') (h : SegFreePc A pc') :
    SegFreePc A pc :=
  hpc ▸ h

theorem SegFreePc.nil {pc : Nat} : SegFreePc [] pc := nofun

theorem SegFreePc.cons {a : Assumption} {pc : Nat}
    (ha : ∀ L g (t : TState), t.pc = pc → a.segmentRule L g t = none) (h : SegFreePc A pc) :
    SegFreePc (a :: A) pc := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact h b hb

theorem SegFreePc.tail {a : Assumption} {pc : Nat} (h : SegFreePc (a :: A) pc) :
    SegFreePc A pc := fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem SegFreeAt.tail {a : Assumption} (h : SegFreeAt (a :: A) L g t) : SegFreeAt A L g t :=
  fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem SegSites.nil {S : List Nat} : SegSites [] S := nofun

theorem SegSites.cons {a : Assumption} {S : List Nat}
    (ha : ∀ L g (t : TState), t.pc ∉ S → a.segmentRule L g t = none) (h : SegSites A S) :
    SegSites (a :: A) S := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact h b hb

/-- Off the sites, no segment. -/
theorem SegSites.pc {S : List Nat} {pc : Nat} (h : SegSites A S) (hpc : pc ∉ S) :
    SegFreePc A pc :=
  fun a ha L g t ht => h a ha L g t (ht ▸ hpc)

/-- The instruction of `K` at `pc` is a branch. -/
def braAt (K : Kernel) (pc : Nat) : Bool :=
  match K.code[pc]? with
  | some ⟨_, .bra ..⟩ => true
  | _ => false

/-- No assumption of `A` takes a segment at a branch of `K`. -/
def SegFreeBra (A : List Assumption) (K : Kernel) : Prop :=
  ∀ pc gd tgt uni, K.code[pc]? = some ⟨gd, .bra tgt uni⟩ → SegFreePc A pc

/-- Segments only at sites that are not branches leave the branches free. -/
theorem SegFreeBra.of_sites {K : Kernel} {S : List Nat} (h : SegSites A S)
    (hS : S.all (fun s => !braAt K s) = true) : SegFreeBra A K := by
  intro pc gd tgt uni hc
  refine h.pc fun hm => ?_
  have := List.all_eq_true.mp hS pc hm
  simp [braAt, hc] at this

/-! ## The constructors -/

/-- A `segmentExact` takes no segment at a `pc` outside its sites. -/
theorem segmentExact_segFreePc {σ : Type} [DecidableEq σ] {K : Kernel} {name : String}
    {T : SegTemplate σ} {sites : List Nat} {why : String} {pc : Nat}
    (h : sites.contains pc = false) :
    ∀ L g (t : TState), t.pc = pc → (segmentExact K name T sites why).segmentRule L g t = none := by
  intro L g t ht
  have h' : pc ∉ sites := by simpa using h
  simp [segmentExact, ht, h']

/-- A `pairEvenAt` takes no segment at a `pc` outside its sites. -/
theorem pairEvenAt_segFreePc {K : Kernel} {name : String} {sites : List Nat} {why : String}
    {pc : Nat} (h : sites.contains pc = false) :
    ∀ L g (t : TState), t.pc = pc → (pairEvenAt K name sites why).segmentRule L g t = none := by
  intro L g t ht
  have h' : pc ∉ sites := by simpa using h
  simp [pairEvenAt, ht, h']

/-- The segments of a `segmentExact` start at its sites. -/
theorem segmentExact_segSites {σ : Type} [DecidableEq σ] {K : Kernel} {name : String}
    {T : SegTemplate σ} {sites S : List Nat} {why : String} (h : ∀ s ∈ sites, s ∈ S) :
    ∀ L g (t : TState), t.pc ∉ S → (segmentExact K name T sites why).segmentRule L g t = none := by
  intro L g t ht
  have : t.pc ∉ sites := fun hm => ht (h _ hm)
  simp [segmentExact, this]

/-- The segments of a `pairEvenAt` start at its sites. -/
theorem pairEvenAt_segSites {K : Kernel} {name : String} {sites S : List Nat} {why : String}
    (h : ∀ s ∈ sites, s ∈ S) :
    ∀ L g (t : TState), t.pc ∉ S → (pairEvenAt K name sites why).segmentRule L g t = none := by
  intro L g t ht
  have : t.pc ∉ sites := fun hm => ht (h _ hm)
  simp [pairEvenAt, this]

/-! ## The step at a selected site -/

/-- The first assumption that selects a segment gives the local step. -/
theorem execLocalA_select {A₁ A₂ : List Assumption} {a : Assumption} {r : Exec TState}
    (h₁ : SegFreeAt A₁ L g t) (ha : a.segmentRule L g t = some r) {op : Op} :
    execLocalA (A₁ ++ a :: A₂) L g t op = r := by
  unfold execLocalA
  rw [List.findSome?_append, List.findSome?_eq_none_iff.mpr h₁, Option.none_or,
    List.findSome?_cons, ha]

/-- At one of its sites, between instructions, where the template matches, a `segmentExact`
takes the template's step. -/
theorem segmentExact_select {σ : Type} [DecidableEq σ] {K : Kernel} {name : String}
    {T : SegTemplate σ} {sites : List Nat} {why : String} {m : SegMatch σ}
    (hs : sites.contains t.pc = true) (hsub : t.sub = 0) (hacc : t.acc = [])
    (hm : T.matchAt K t.pc = some m) :
    (segmentExact K name T sites why).segmentRule L g t = some (execSegment T.fn m t) := by
  have hs' : t.pc ∈ sites := by simpa using hs
  simp [segmentExact, hs', hsub, hacc, hm]

/-- At one of its sites, between instructions, at `and.b32 d, a, -16777217`, a `pairEvenAt`
takes the peer-bit step. -/
theorem pairEvenAt_select {K : Kernel} {name : String} {sites : List Nat} {why : String}
    {d a : Nat} (hs : sites.contains t.pc = true) (hsub : t.sub = 0)
    (hc : K.code[t.pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some d],
      [.reg a, .imm peerBitMask]⟩⟩) :
    (pairEvenAt K name sites why).segmentRule L g t = some (execPairEven L g t d a) := by
  have hs' : t.pc ∈ sites := by simpa using hs
  simp [pairEvenAt, hs', hsub, hc]

/-- The peer-bit step of a register holding a `.shared::cta` window address below `2 ^ 24`, in
a launch whose cluster of the executing CTA has even size: the even CTA's byte. -/
theorem execPairEven_ok {d a w : Nat} {x : BitVec 64} {even : Nat}
    (hr : t.regs a = some (.bits w x)) (hoff : (truncBits 32 x).toNat < 2 ^ 24)
    (hcl : L.clusterSizeOf (g / L.block) % 2 = 0)
    (hp : L.peerCta (g / L.block) (L.rankOfCta (g / L.block) / 2 * 2) = some even) :
    execPairEven L g t d a = .ok (next (setReg t d
      (.ptr 32 false (.shared (g / L.block) even)
        (BitVec.ofNat 64 (truncBits 32 x).toNat)))) := by
  have hoff' : (truncBits 32 x).toNat < 16777216 := hoff
  simp [execPairEven, readReg, hr, hoff', hcl, hp, bind, Except.bind, pure, Except.pure]

/-- The registers after a segment: the cleared written registers, then the constants of a
defining shape, then the outputs. -/
def segRegs {σ : Type} [DecidableEq σ] (m : SegMatch σ) (t : TState)
    (outs : List (Nat × Value)) : Nat → Option Value :=
  let reg := fun s => (m.reg.lookup s).getD 0
  let cleared := m.shape.writes.foldl (fun rs s => Function.update rs (reg s) none) t.regs
  let consts := if m.shape.defines then
      m.shape.consts.foldl (fun rs p => Function.update rs (reg p.1) (some p.2)) cleared
    else cleared
  outs.foldl (fun rs p => Function.update rs p.1 (some p.2)) consts

/-- The register of a slot. -/
abbrev SegMatch.regOf {σ : Type} [DecidableEq σ] (m : SegMatch σ) (s : σ) : Nat :=
  (m.reg.lookup s).getD 0

/-- **The step of a two-lane template**: when the constants are defined or present and both
inputs hold `f32` numbers `x₀`, `x₁`, the outputs receive `fn x₀` and `fn x₁` and execution
continues after the instance. -/
theorem execSegment_two {σ : Type} [DecidableEq σ] {fn : ℝ → ℝ} {m : SegMatch σ}
    {i₀ o₀ i₁ o₁ : σ} {v₀ v₁ : Value} {x₀ x₁ : ℝ}
    (hio : m.shape.io = [(i₀, o₀), (i₁, o₁)])
    (hc : m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (m.regOf p.1) = some p.2)
    (h₀ : t.regs (m.regOf i₀) = some v₀) (hx₀ : valFloat .f32 v₀ = .ok x₀)
    (h₁ : t.regs (m.regOf i₁) = some v₁) (hx₁ : valFloat .f32 v₁ = .ok x₁) :
    execSegment fn m t = .ok { t with
      regs := segRegs m t [(m.regOf o₀, .float .f32 (fn x₀)), (m.regOf o₁, .float .f32 (fn x₁))],
      pc := m.stop, sub := 0, acc := [] } := by
  unfold execSegment
  simp only [hio, List.mapM_cons, List.mapM_nil, readReg, h₀, h₁, hx₀, hx₁, bind, Except.bind,
    pure, Except.pure]
  simp only [hc, ↓reduceIte]
  rfl

/-- Folding updates of other registers keeps a register. -/
theorem foldl_update_other {β : Type} {f : β → Nat} {v : β → Option Value}
    {rs : Nat → Option Value} {r : Nat} :
    ∀ l : List β, (∀ x ∈ l, f x ≠ r) →
      (l.foldl (fun rs x => Function.update rs (f x) (v x)) rs) r = rs r
  | [], _ => rfl
  | x :: l, h => by
    rw [List.foldl_cons, foldl_update_other l (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      Function.update_of_ne (h x (by simp)).symm]

/-- Folding updates that end with a fixed value at `r` gives that value. -/
theorem foldl_update_last {β : Type} {f : β → Nat} {v : β → Option Value}
    {rs : Nat → Option Value} {r : Nat} {x : β} (l : List β) (hx : f x = r)
    (hl : ∀ y ∈ l, f y ≠ r) :
    ((l.foldl (fun rs x => Function.update rs (f x) (v x)) (Function.update rs (f x) (v x)))) r =
      v x := by
  rw [foldl_update_other l hl, ← hx, Function.update_self]

/-- **The registers after a segment.** A register no slot writes and no output names keeps its
value; a written register that is neither an output nor a defined constant is cleared. -/
theorem segRegs_frame {σ : Type} [DecidableEq σ] {m : SegMatch σ}
    {outs : List (Nat × Value)} {r : Nat} (hw : ∀ s ∈ m.shape.writes, m.regOf s ≠ r)
    (ho : ∀ p ∈ outs, p.1 ≠ r) (hk : ∀ p ∈ m.shape.consts, m.regOf p.1 ≠ r) :
    segRegs m t outs r = t.regs r := by
  unfold segRegs
  simp only
  rw [foldl_update_other (f := Prod.fst) (v := fun p => some p.2) outs ho]
  split
  · refine (foldl_update_other (β := σ × Value) (f := fun p => m.regOf p.1)
      (v := fun p => some p.2) _ hk).trans ?_
    exact foldl_update_other (f := m.regOf) (v := fun _ => none) _ hw
  · exact foldl_update_other (f := m.regOf) (v := fun _ => none) _ hw

/-- Folding updates where every update of `r` writes `none`, and some does, clears `r`. -/
theorem foldl_update_hit {β : Type} {f : β → Nat} {v : β → Option Value} {r : Nat} :
    ∀ (l : List β) (rs : Nat → Option Value), (∀ x ∈ l, f x = r → v x = none) →
      (∃ x ∈ l, f x = r) → (l.foldl (fun rs x => Function.update rs (f x) (v x)) rs) r = none
  | [], _, _, ⟨_, hx, _⟩ => by cases hx
  | y :: l, rs, hv, hx => by
    rw [List.foldl_cons]
    by_cases hl : ∃ x ∈ l, f x = r
    · exact foldl_update_hit l _ (fun x hx => hv x (List.mem_cons_of_mem _ hx)) hl
    · push Not at hl
      obtain ⟨x, hx, hxr⟩ := hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [foldl_update_other l hl, ← hxr, Function.update_self]
        exact hv x (by simp) hxr
      · exact absurd hxr (hl x hx)

/-- A register cleared by the segment: written by a slot, neither an output nor a constant of a
defining shape. -/
theorem segRegs_cleared {σ : Type} [DecidableEq σ] {m : SegMatch σ}
    {outs : List (Nat × Value)} {r : Nat} {s : σ} (hs : s ∈ m.shape.writes) (hr : m.regOf s = r)
    (ho : ∀ p ∈ outs, p.1 ≠ r) (hk : m.shape.defines → ∀ p ∈ m.shape.consts, m.regOf p.1 ≠ r) :
    segRegs m t outs r = none := by
  unfold segRegs
  simp only
  rw [foldl_update_other (f := Prod.fst) (v := fun p => some p.2) outs ho]
  have hcl := foldl_update_hit (f := m.regOf) (v := fun _ => none) (r := r) m.shape.writes
    t.regs (fun _ _ _ => rfl) ⟨s, hs, hr⟩
  split
  · rename_i hd
    exact (foldl_update_other (β := σ × Value) (f := fun p => m.regOf p.1)
      (v := fun p => some p.2) _ (hk hd)).trans hcl
  · exact hcl

/-- The output register of a two-lane step. -/
theorem segRegs_two_out {σ : Type} [DecidableEq σ] {m : SegMatch σ} {r₀ r₁ : Nat}
    {w₀ w₁ : Value} :
    segRegs m t [(r₀, w₀), (r₁, w₁)] r₁ = some w₁ ∧
      (r₀ ≠ r₁ → segRegs m t [(r₀, w₀), (r₁, w₁)] r₀ = some w₀) := by
  refine ⟨?_, fun hne => ?_⟩
  · simp [segRegs]
  · simp [segRegs, Function.update_of_ne hne]

end

end PTX.Assumption
