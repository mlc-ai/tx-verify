-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.Prefix
public import Core.Assumption.NcReadOnly
public import Lemmas.Flow.ContinuingEvent

/-! Execute the production prefix entry with the thread semantics and an immutable offset array.
Every successful replay carries a proof of its actual PTX event trace through return. -/
@[expose] public section
namespace FlashKda.Prefix
open PTX
noncomputable section

/-- Select exactly the non-coherent loads in this entry. All read the immutable sequence offsets. -/
def readSites := Decoded.kernel.code.zipIdx.filterMap fun (ins, pc) =>
  match ins.op with
  | .mem a => if a.nc then some pc else none
  | _ => none

def readonly := Assumption.ncReadOnly "flashkda-sequence-offsets" readSites
  "Only the input sequence offsets are read through the non-coherent cache."

/-- A one-warp launch with the host's chunk size of sixteen and separate device buffers. -/
def launch (n input output : Nat) : Launch where
  grid := 1
  block := 32
  params name := do
    let args := [input, n, 16, output]
    let index ← (List.range 4).find? fun i =>
      name == "_Z28_flash_kda_build_tile_prefixPKliiPi_param_" ++ toString i
    return BitVec.ofNat 64 (← args[index]?)

/-- A known byte of an initialized array of 64-bit cumulative lengths. -/
def inputByte (base : Nat) (offsets : List Nat) (loc : Loc) : Option Byte := do
  guard (loc.space = .global ∧ loc.cta = 0 ∧ base ≤ loc.addr)
  let pos := loc.addr - base
  let x ← offsets[pos/8]?
  return (.bits 64 (BitVec.ofNat 64 x), pos % 8)

def readBytes (base : Nat) (offsets : List Nat) (a : Acc) : List (Option Byte) :=
  (List.range a.size).map fun k => inputByte base offsets (a.loc.at k)

/-- The continuation of every direct weak load reads the destination list from its instruction. -/
def destination (A : List Assumption) (L : Launch) (g : Nat) (t : TState) :
    Option { ds : List Nat // ∀ a k, out Decoded.kernel A L g t = .ev (.readNC a k) →
      k = afterLoad t ds } := do
  match hi : Decoded.kernel.code[t.pc]? with
  | some ⟨none, .mem m⟩ =>
    let .reg base bits := m.addr.base | none
    if h : m.rule = some .threadAccess ∧ m.locSpace? = some .global ∧
        m.addr.base = .reg base bits ∧ m.kind = .load ∧ m.sem = .weak ∧
        (Op.mem m).isLocal = false then
      return ⟨m.regs, by
        intro a k actual
        cases hf : t.fault with
        | some f => simp [out, hf] at actual
        | none =>
          simp only [out, hf, hi, guardHolds, h.2.2.2.2.2, Bool.false_eq_true,
            ↓reduceIte, eventTmpl] at actual
          rw [memTmpl_direct_weakLoad h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1] at actual
          replace actual := Out.ev.inj actual
          unfold loadTmpl at actual
          split at actual <;> try contradiction
          split at actual <;> try contradiction
          split at actual <;> try contradiction
          injection actual with _ hk
          exact hk.symm⟩
    else none
  | _ => none

theorem rebuild_word (x : BitVec 64) :
    rebuild 3 ((Value.bits 64 x).toBytes.map some) = .ok (.bits 64 x) := by
  unfold rebuild
  simp [Value.toBytes, Value.byteAt, Value.bytes, List.range_succ, pure, Except.pure]

def loadedWord (t : TState) (ds : List Nat) (x : BitVec 64) : TState :=
  let v := Value.bits 64 x
  if t.sub + 1 < ds.length then { t with sub := t.sub+1, acc := t.acc ++ [v] }
  else { setRegs t ds (t.acc ++ [v]) with pc := t.pc+1, sub := 0, acc := [] }

theorem loaded_eq (t : TState) (ds : List Nat) (x : BitVec 64) :
    afterLoad t ds ((Value.bits 64 x).toBytes.map some) = loadedWord t ds x := by
  unfold afterLoad
  rw [rebuild_word]
  rfl

theorem tau_run {K A L g t u es}
    (h : Tau K A L g t u) (r : Run K A L g u es none) : Run K A L g t es none := by
  cases r with
  | step path event rest => exact .step ((Relation.ReflTransGen.single h).trans path) event rest
  | last path event => exact .last ((Relation.ReflTransGen.single h).trans path) event

/-- Non-coherent reads observe bytes from the launch's immutable cumulative lengths. -/
def respects (base : Nat) (offsets : List Nat) (e : Event) : Prop :=
  match e.kind with
  | .nc a bs => readSites.contains e.pc = true → ∀ data : List Byte,
      data.map some = readBytes base offsets a → bs = data.map some
  | _ => True

/-- A completed trace exists, uses the stated input, and is the only completed trace on it. -/
structure Exact (A : List Assumption) (L : Launch) (g base : Nat) (offsets : List Nat)
    (t : TState) (es : List Event) : Prop where
  run : Run Decoded.kernel A L g t es none
  reads : ∀ e ∈ es, respects base offsets e
  unique : ∀ xs, Run Decoded.kernel A L g t xs none → (∀ e ∈ xs, respects base offsets e) → xs = es

theorem at_event {A L g t es m}
    (h : out Decoded.kernel A L g t = .ev m) (r : Run Decoded.kernel A L g t es none) :
    (∃ e, es = [e] ∧ Fires t.pc m e none) ∨
    ∃ e xs u, es = e :: xs ∧ Fires t.pc m e (some u) ∧ Run Decoded.kernel A L g u xs none := by
  have first {s : TState} {e : Event} {o : Option TState}
      (path : Relation.ReflTransGen (Tau Decoded.kernel A L g) t s)
      (step : EStep Decoded.kernel A L g s e o) : Fires t.pc m e o := by
    obtain rfl := stop_unique path .refl (stops_of_estep step) ⟨_, h⟩
    obtain ⟨m', hm, fire⟩ := step
    rw [h] at hm
    cases hm
    exact fire
  cases r with
  | last path step => exact Or.inl ⟨_, rfl, first path step⟩
  | step path step tail => exact Or.inr ⟨_, _, _, rfl, first path step, tail⟩

theorem continue_event {A L g base offsets t u es m e}
    (h : out Decoded.kernel A L g t = .ev m) (hr : Exact A L g base offsets u es)
    (hf : Fires t.pc m e (some u)) (input : respects base offsets e)
    (det : ∀ f o, Fires t.pc m f o → respects base offsets f → f = e ∧ o = some u) :
    Exact A L g base offsets t (e :: es) := by
  refine ⟨.step .refl ⟨_, h, hf⟩ hr.run, ?_, ?_⟩
  · simpa only [List.forall_mem_cons] using And.intro input hr.reads
  · intro xs run reads
    rcases at_event h run with ⟨f, rfl, hh⟩ | ⟨f, tail, s, rfl, hh, rest⟩
    · have := (det f none hh (reads f (by simp))).2
      contradiction
    · obtain ⟨rfl, hs⟩ := det f (some s) hh (reads f (by simp))
      obtain rfl := Option.some.inj hs
      rw [hr.unique tail rest (fun z hz => reads z (List.mem_cons_of_mem _ hz))]

theorem return_event {A L g base offsets t}
    (h : out Decoded.kernel A L g t = .ev .exit) :
    Exact A L g base offsets t [⟨t.pc, .exit⟩] := by
  refine ⟨.last .refl ⟨_, h, rfl, rfl⟩, ?_, ?_⟩
  · simp [respects]
  · intro xs run _
    rcases at_event h run with ⟨e, rfl, hfire⟩ | ⟨e, xs, u, rfl, hfire, _⟩
    · rw [hfire.1]
    · cases hfire.2

/-- This partial interpreter delegates every instruction to TxVerify. It accepts exactly local
steps, immutable loads, writes, and a clean return. The fuel only bounds evaluation. -/
def replay (A : List Assumption) (L : Launch) (g base : Nat) (offsets : List Nat) :
    (fuel : Nat) → (t : TState) → Option { es // Exact A L g base offsets t es }
  | 0, _ => none
  | n+1, t =>
    match h : out Decoded.kernel A L g t with
    | .tau u => do
      let ⟨es, hr⟩ ← replay A L g base offsets n u
      return ⟨es, tau_run h hr.run, hr.reads, fun xs run rd =>
        hr.unique xs (run.after_local (.single h)) rd⟩
    | .ev (.readNC a k) => do
      let ds ← destination A L g t
      let index := (a.loc.addr-base)/8
      let x ← offsets[index]?
      let word := BitVec.ofNat 64 x
      let bs := (Value.bits 64 word).toBytes.map some
      if ok : bs.length = a.size ∧ bs = readBytes base offsets a ∧
          readSites.contains t.pc = true then
        let ⟨es, hr⟩ ← replay A L g base offsets n (loadedWord t ds.1 word)
        let e : Event := ⟨t.pc, .nc a bs⟩
        have hk : k bs = loadedWord t ds.1 word := by rw [ds.2 a k h, loaded_eq]
        return ⟨e :: es, continue_event h hr ⟨bs, ok.1, rfl, congrArg some hk.symm⟩
          (fun _ data hd => ok.2.1.trans hd.symm)
          (by
            intro f o hh rd
            obtain ⟨other, _, rfl, rfl⟩ := hh
            have same : other = bs := rd ok.2.2 _ ok.2.1
            subst other
            exact ⟨rfl, congrArg some hk⟩)⟩
      else none
    | .ev (.write a bs u) => do
      let ⟨es, hr⟩ ← replay A L g base offsets n u
      let e : Event := ⟨t.pc, .wr a bs⟩
      return ⟨e :: es, continue_event h hr ⟨rfl, rfl⟩ trivial (fun _ _ hf _ => hf)⟩
    | .ev .exit => some ⟨_, return_event h⟩
    | _ => none

def stored (e : Event) : Option (Acc × List Byte) :=
  match e.kind with
  | .wr a data => some (a, data)
  | _ => none

def ordinary (e : Event) : Bool := match e.kind with
  | .nc .. | .wr .. | .exit => true
  | _ => false

def outputWord (base index x : Nat) : Acc × List Byte :=
  ({ loc := ⟨.global, 0, base + 4*index⟩, size := 4 }, (Value.bits 32 (BitVec.ofNat 64 x)).toBytes)

/-- Check all event kinds and the addresses and bytes of every global store. -/
def storesMatch (base : Nat) (expected : List Nat) (es : List Event) : Bool :=
  es.all ordinary &&
    decide (es.filterMap stored = expected.zipIdx.map fun (x,i) => outputWord base i x)

/-- A successful check specifies all global stores for every completed run from the
same input bytes. Existence is included to exclude vacuity. -/
theorem verified_stores {A L g base offsets t fuel output expected}
    (ok : ((replay A L g base offsets fuel t).map
      (fun r => storesMatch output expected r.1)) = some true) :
    (∃ es, Exact A L g base offsets t es ∧ storesMatch output expected es = true) ∧
    (∀ xs, Run Decoded.kernel A L g t xs none → (∀ e ∈ xs, respects base offsets e) →
      storesMatch output expected xs = true) := by
  cases run : replay A L g base offsets fuel t with
  | none => simp [run] at ok
  | some pair =>
    obtain ⟨es, proof⟩ := pair
    simp only [run, Option.map_some, Option.some.injEq] at ok
    exact ⟨⟨es, proof, ok⟩, fun xs hr reads => proof.unique xs hr reads ▸ ok⟩

end
end FlashKda.Prefix
