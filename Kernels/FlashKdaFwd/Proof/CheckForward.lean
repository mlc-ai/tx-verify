-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.PublicEnclosure
import Mathlib.Tactic

/-! Independent full-sequence output and state checks, including IEEE decoding and
absolute plus relative tolerances. The same theorem applies to each head and value row. -/
@[expose] public section
namespace FlashKda.Enclosure
open Sequence

structure Result (d : Nat) where
  state : Balls d
  outputs : Array Ball

def run {d} (bits : Nat) (scale : ℚ) (p : Nat → Prepared d) (v : Nat → ℚ)
    (initial : Rationals d) : Nat → Result d
  | 0 => ⟨initial.map point,#[]⟩
  | t+1 =>
    let prev := run bits scale p v initial t
    let next := stateStep bits (p t) (v t) prev.state
    ⟨next,prev.outputs.push (read scale (p t) next)⟩

noncomputable def spec {d} (raw : Nat → Raw d) (v : Nat → ℚ) (floor param : ℚ)
    (bias : Rationals d) :=
  activate (fun t => realRow (raw t).query) (fun t => realRow (raw t).key)
    (fun t => realRow (raw t).gate) (fun t => (v t:ℝ)) (fun t => ((raw t).logit:ℝ))
    floor param (realRow bias)

theorem run_ok {d bits n} (raw : Nat → Raw d) (v : Nat → ℚ) (floor param scale : ℚ)
    (bias initial : Rationals d) (p : Nat → Prepared d)
    (good : ∀ t < n, Correct (p t) (raw t) floor param bias) :
    let r := run bits scale p v initial n
    let x := spec raw v floor param bias
    r.outputs.size = n ∧ (∀ i, Covers r.state[i] (tokenState x (realRow initial) n i)) ∧
      ∀ t < n, ∃ o, r.outputs[t]? = some o ∧
        Covers o ((scale:ℝ)*Chunk.dot (tokenState x (realRow initial) (t+1)) (x.query t)) := by
  induction n with
  | zero =>
    refine ⟨rfl,?_,by simp⟩
    intro i
    simpa [run,realRow,tokenState,Chunk.sequential] using point_ok initial[i]
  | succ n ih =>
    obtain ⟨size,states,outputs⟩ := ih (fun t ht => good t (by omega))
    let x := spec raw v floor param bias
    let prev := run bits scale p v initial n
    let next := stateStep bits (p n) (v n) prev.state
    have ok := good n (by omega)
    have sn (i : Fin d) : Covers next[i] (tokenState x (realRow initial) (n+1) i) :=
      step_ok ok states i
    refine ⟨by simpa [run] using size, sn, ?_⟩
    intro t ht
    by_cases last : t = n
    · subst t
      refine ⟨read scale (p n) next,?_,read_ok ok sn⟩
      change (prev.outputs.push (read scale (p n) next))[n]? = _
      rw [Array.getElem?_push,show prev.outputs.size = n from size,ite_eq_left rfl]
    · obtain ⟨o,mem,inside⟩ := outputs t (by omega)
      exact ⟨o,by simpa [run,Array.getElem?_push,size,last] using mem,inside⟩

/-- The left side is an upper bound for the error. The right uses a lower bound for
the magnitude of the unknown true result so a successful comparison is sufficient. -/
def accepts (a : Ball) (measured absolute relative : ℚ) : Bool :=
  decide (0 ≤ absolute ∧ 0 ≤ relative ∧
    |measured-a.center|+a.radius ≤ absolute+relative*max 0 (|a.center|-a.radius))

theorem accepts_ok {a : Ball} {x : ℝ} {y absolute relative : ℚ}
    (h : Covers a x) (ok : accepts a y absolute relative = true) :
    |(y:ℝ)-x| ≤ (absolute:ℝ)+(relative:ℝ)*|x| := by
  obtain ⟨_,pr,checked⟩ : 0 ≤ absolute ∧ 0 ≤ relative ∧
      |y-a.center|+a.radius ≤ absolute+relative*max 0 (|a.center|-a.radius) := of_decide_eq_true ok
  have hi := (abs_sub_le (y:ℝ) (a.center:ℝ) x).trans
    (add_le_add le_rfl (show |(a.center:ℝ)-x| ≤ a.radius by rwa [abs_sub_comm]))
  have c := abs_add_le ((a.center:ℝ)-x) x
  rw [sub_add_cancel,abs_sub_comm] at c
  have xl : max 0 (|(a.center:ℝ)|-a.radius) ≤ |x| :=
    max_le (abs_nonneg _) (by unfold Covers at h; linarith)
  have cert := (Rat.cast_le (K := ℝ)).2 checked
  push_cast at cert
  exact hi.trans (cert.trans (by gcongr))

/-- Outward integer millionths give a reproducible lower and upper bound on the
absolute error of each measured output. -/
def millionths (a : Ball) (y : ℚ) : ℤ × ℤ :=
  (⌊max 0 (|y-a.center|-a.radius)*1000000⌋,⌈(|y-a.center|+a.radius)*1000000⌉)

theorem millionths_ok {a : Ball} {x : ℝ} (y : ℚ) (hx : Covers a x) :
    ((millionths a y).1:ℝ)/1000000 ≤ |(y:ℝ)-x| ∧
      |(y:ℝ)-x| ≤ ((millionths a y).2:ℝ)/1000000 := by
  have center : |x-(a.center:ℝ)| ≤ a.radius := hx
  have high := abs_sub_le (y:ℝ) (a.center:ℝ) x
  rw [abs_sub_comm (a.center:ℝ) x] at high
  have low := abs_sub_le (y:ℝ) x (a.center:ℝ)
  have bottom : max 0 (|(y:ℝ)-a.center|-a.radius) ≤ |(y:ℝ)-x| :=
    max_le (abs_nonneg _) (by linarith)
  have bl := (Rat.cast_le (K := ℝ)).2 (Int.floor_le (max 0 (|y-a.center|-a.radius)*1000000))
  have bu := (Rat.cast_le (K := ℝ)).2 (Int.le_ceil ((|y-a.center|+a.radius)*1000000))
  unfold millionths
  push_cast at bl bu ⊢
  constructor <;> linarith

structure Maximum where
  lowerMillionths : Int := 0
  upperMillionths : Int := 0
  deriving Inhabited

def Maximum.include (m : Maximum) (a : Ball) (y : ℚ) : Maximum :=
  let (lo,hi) := millionths a y
  ⟨max m.lowerMillionths lo,max m.upperMillionths hi⟩

def Maximum.bounds (m : Maximum) (x : ℝ) :=
  (m.lowerMillionths:ℝ)/1000000 ≤ x ∧ x ≤ (m.upperMillionths:ℝ)/1000000

theorem max_step {m : Maximum} {prev x : ℝ} {a : Ball} (y : ℚ) (old : m.bounds prev)
    (covered : Covers a x) : (m.include a y).bounds (max prev |(y:ℝ)-x|) := by
  have entry := millionths_ok y covered
  unfold Maximum.bounds Maximum.include
  push_cast
  rw [← max_div_div_right (by norm_num : (0:ℝ) ≤ 1000000),
    ← max_div_div_right (by norm_num : (0:ℝ) ≤ 1000000)]
  exact ⟨max_le_max old.1 entry.1,max_le_max old.2 entry.2⟩

/-- Accumulate actual decoded output words, stopping on a nonfinite or out-of-format word. -/
def scan (fmt : PTX.FloatFmt) (bits : Nat) (m : Maximum) : List (Ball × Nat) → Option Maximum
  | [] => some m
  | (a,w)::rest => do
    guard (w < 2^bits)
    let y ← fmt.decode w
    scan fmt bits (m.include a y) rest

noncomputable def trueMaximum (fmt : PTX.FloatFmt) (acc : ℝ) : List (ℝ × Nat) → Option ℝ
  | [] => some acc
  | (x,w)::rest => do
    let y ← fmt.decode w
    trueMaximum fmt (max acc |(y:ℝ)-x|) rest

/-- The same word scanner used by the capture reader brackets the maximum absolute error
over all supplied observations. An unmeasurable word cannot yield a successful scan. -/
theorem scan_ok (fmt : PTX.FloatFmt) (bits : Nat) (xs : List (Ball × Nat × ℝ))
    (covers : ∀ r ∈ xs, Covers r.1 r.2.2) {m out : Maximum} {acc : ℝ} (hm : m.bounds acc)
    (ok : scan fmt bits m (xs.map fun (b,w,_) => (b,w)) = some out) :
    ∃ actual, trueMaximum fmt acc (xs.map fun (_,w,x) => (x,w)) = some actual ∧
      out.bounds actual := by
  induction xs generalizing m acc with
  | nil =>
    have eq : m = out := Option.some.inj ok
    exact ⟨acc,rfl,eq ▸ hm⟩
  | cons head rest ih =>
    obtain ⟨a,w,x⟩ := head
    have ha := covers (a,w,x) (by simp)
    have tail : ∀ r ∈ rest, Covers r.1 r.2.2 := fun r hr => covers r (List.mem_cons_of_mem _ hr)
    cases d : fmt.decode w with
    | none => simp [scan,d] at ok
    | some y =>
      by_cases fits : w < 2^bits
      · have next : scan fmt bits (m.include a y) (rest.map fun (b,w,_) => (b,w)) = some out := by
          simpa [scan,d,fits] using ok
        obtain ⟨actual,eq,bound⟩ := ih tail (max_step y hm ha) next
        exact ⟨actual,by simpa [trueMaximum,d] using eq,bound⟩
      · simp [scan,fits] at ok

def checkWord (fmt : PTX.FloatFmt) (word : Nat) (a : Ball) (absolute relative : ℚ) : Bool :=
  match fmt.decode word with
  | some x => accepts a x absolute relative
  | none => false

theorem word_ok {fmt word a absolute relative} {x : ℝ}
    (hw : checkWord fmt word a absolute relative = true) (hx : Covers a x) :
    ∃ y : ℚ, fmt.decode word = some y ∧ |(y:ℝ)-x| ≤ (absolute:ℝ)+(relative:ℝ)*|x| := by
  unfold checkWord at hw
  split at hw
  · rename_i y hy
    exact ⟨y,hy,accepts_ok hx hw⟩
  · contradiction

/-- The interval result covers all live outputs and the outgoing state of the real
16-token block specification for every sequence length, including an empty sequence. -/
theorem forward {d bits n} (raw : Nat → Raw d) (v : Nat → ℚ) (floor param scale : ℚ)
    (bias initial : Rationals d) (p : Nat → Prepared d)
    (good : ∀ t < n, Correct (p t) (raw t) floor param bias) :
    let r := run bits scale p v initial n
    let x := spec raw v floor param bias
    (∀ t < n, ∃ o, r.outputs[t]? = some o ∧ Covers o (output x (realRow initial) n scale t)) ∧
      ∀ i, Covers r.state[i] (carry x (realRow initial) n scale ((n+15)/16) i) := by
  let x := spec raw v floor param bias
  obtain ⟨_,states,outputs⟩ := run_ok (bits := bits) raw v floor param scale bias initial p good
  obtain ⟨readout,finalState⟩ := Sequence.forward x (realRow initial) n scale
  constructor
  · intro t ht; rw [readout t ht]; exact outputs t ht
  · rw [finalState]; exact states

/-- Successful raw activation checks suffice for certified errors of every returned word.
Both references here are the real block program, at a live output and at the final boundary. -/
theorem measured_forward {d bits splits n} (raw : Nat → Raw d) (v : Nat → ℚ)
    (floor param scale : ℚ) (bias initial : Rationals d) (p : Nat → Prepared d) {logExp : Ball}
    (exponential : expAt bits splits param = some logExp)
    (prepared : ∀ t < n, prepare bits splits floor logExp bias (raw t) = some (p t)) :
    let r := run bits scale p v initial n
    let x := spec raw v floor param bias
    (∀ t < n, ∃ o, r.outputs[t]? = some o ∧ ∀ y : ℚ,
      let b := millionths o y
      let err := |(y:ℝ)-output x (realRow initial) n scale t|
      (b.1:ℝ)/1000000 ≤ err ∧ err ≤ (b.2:ℝ)/1000000) ∧
    (∀ i (y : ℚ), let b := millionths r.state[i] y
      let err := |(y:ℝ)-carry x (realRow initial) n scale ((n+15)/16) i|
      (b.1:ℝ)/1000000 ≤ err ∧ err ≤ (b.2:ℝ)/1000000) := by
  obtain ⟨outs,state⟩ := forward (bits := bits) raw v floor param scale bias initial p
    (fun t ht => prepare_ok exponential (prepared t ht))
  constructor
  · intro t ht
    obtain ⟨o,loc,cover⟩ := outs t ht
    exact ⟨o,loc,fun y => millionths_ok y cover⟩
  · exact fun i y => millionths_ok y (state i)

end FlashKda.Enclosure
