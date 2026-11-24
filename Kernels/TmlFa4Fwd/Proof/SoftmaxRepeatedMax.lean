-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMax
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasSequence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- Dependency sets of scalar maxima, or of the two lanes of an incoming packed score. -/
inductive MaxDatum where
  | scalar (cols : List Nat)
  | pair (low high : List Nat)

def scoreMax (score : Nat → Option ℝ) (cols : List Nat) : Option ℝ :=
  cols.foldr (fun j z => maxScore (score j) z) none

def MaxDatum.value (score : Nat → Option ℝ) : MaxDatum → Value
  | .scalar cols => scoreValue (scoreMax score cols)
  | .pair lo hi => .pair (scoreValue (scoreMax score lo)) (scoreValue (scoreMax score hi))

def scalarColumns (d : MaxDatum) : Option (List Nat) :=
  match d with
  | .scalar cols => some cols
  | .pair .. => none

def scalarValue (score : Nat → Option ℝ) (D : Nat → Option MaxDatum) (r : Nat) : Value :=
  ((D r).map (MaxDatum.value score)).getD (.pred false)

def updateColumns (D : Nat → Option MaxDatum) (dst : Nat) (x : MaxDatum) : Nat → Option MaxDatum :=
  fun r => if r == dst then some x else D r

def maxColumns (D : Nat → Option MaxDatum) : RItem → Option (Nat → Option MaxDatum)
  | .unpack lo hi src => do
    let .pair xs ys ← D src | none
    return updateColumns (updateColumns D lo (.scalar xs)) hi (.scalar ys)
  | .fmax dst lo hi third => do
    let xs ← (D lo).bind scalarColumns
    let ys ← (D hi).bind scalarColumns
    let zs ← match third with
      | none => some []
      | some r => (D r).bind scalarColumns
    return updateColumns D dst (.scalar ((xs ++ ys) ++ zs))
  | _ => none

def runMaxColumns : List RItem → (Nat → Option MaxDatum) → Option (Nat → Option MaxDatum)
  | [], D => some D
  | i :: is, D => (maxColumns D i).bind (runMaxColumns is)

private theorem updateColumns_value (D : Nat → Option MaxDatum) (dst : Nat) (x : MaxDatum)
    (score : Nat → Option ℝ) :
    scalarValue score (updateColumns D dst x) =
      Function.update (scalarValue score D) dst (x.value score) := by
  funext r
  by_cases h : r = dst
  · subst r
    simp [scalarValue, updateColumns]
  · simp [scalarValue, updateColumns, Function.update_of_ne h, beq_false_of_ne h]

private theorem maxColumns_value {i : RItem} {D D' : Nat → Option MaxDatum}
    (h : maxColumns D i = some D') (score : Nat → Option ℝ) :
    i.req (scalarValue score D) = true ∧ i.cond (scalarValue score D) ∧
      i.upd (scalarValue score D) = scalarValue score D' := by
  cases i with
  | unpack lo hi src =>
    cases hs : D src with
    | none => simp [maxColumns, hs] at h
    | some v =>
      cases v with
      | scalar xs => simp [maxColumns, hs] at h
      | pair xs ys =>
        simp [maxColumns, hs, pure] at h
        subst D'
        let a := scoreValue (scoreMax score xs)
        let b := scoreValue (scoreMax score ys)
        have hRead : scalarValue score D src = .pair a b := by
          simp [scalarValue, hs, MaxDatum.value, a, b]
        have hSplit : splitValue 64 (.pair a b) = (a, b) := by
          cases scoreMax score xs <;> cases scoreMax score ys <;> rfl
        refine ⟨rfl, ?_, ?_⟩
        · simp [RItem.cond, hRead, hSplit, a, b, scoreValue_bytes, Value.bytes]
        · rw [updateColumns_value, updateColumns_value]
          simp [RItem.upd, RItem.vals, hRead, hSplit, MaxDatum.value, a, b]
  | fmax dst lo hi third =>
    have hView (r : Nat) {xs : List Nat} (hr : (D r).bind scalarColumns = some xs) :
        scalarValue score D r = scoreValue (scoreMax score xs) := by
      cases hd : D r with
      | none => simp [hd] at hr
      | some d =>
        cases d with
        | pair _ _ => simp [hd, scalarColumns] at hr
        | scalar ys =>
          simp [hd, scalarColumns] at hr
          subst ys
          simp [scalarValue, hd, MaxDatum.value]
    cases hlo : (D lo).bind scalarColumns with
    | none => simp [maxColumns, hlo] at h
    | some xs =>
      cases hhi : (D hi).bind scalarColumns with
      | none => simp [maxColumns, hlo, hhi] at h
      | some ys =>
        cases third with
        | none =>
          simp [maxColumns, hlo, hhi, pure] at h
          subst D'
          have he : maxE (RItem.maxSrcs (scalarValue score D) lo hi none) =
              .ok (scoreValue (scoreMax score (xs ++ ys))) := by
            simpa [RItem.maxSrcs, hView lo hlo, hView hi hhi, scoreMax, maxScore_append,
              -List.foldr_append] using maxEEq (scoreMax score xs) (scoreMax score ys) none
          refine ⟨rfl, ⟨_, he⟩, ?_⟩
          rw [updateColumns_value]
          simp [RItem.upd, RItem.vals, he, okVal, MaxDatum.value]
        | some r =>
          cases hthird : (D r).bind scalarColumns with
          | none => simp [maxColumns, hlo, hhi, hthird] at h
          | some zs =>
            simp [maxColumns, hlo, hhi, hthird, pure] at h
            subst D'
            have he : maxE (RItem.maxSrcs (scalarValue score D) lo hi (some r)) =
                .ok (scoreValue (scoreMax score ((xs ++ ys) ++ zs))) := by
              simpa [RItem.maxSrcs, hView lo hlo, hView hi hhi, hView r hthird,
                scoreMax, maxScore_append, maxScore_assoc, -List.foldr_append] using
                maxEEq (scoreMax score xs) (scoreMax score ys) (some (scoreMax score zs))
            refine ⟨rfl, ⟨_, he⟩, ?_⟩
            rw [updateColumns_value]
            simp [RItem.upd, RItem.vals, he, okVal, MaxDatum.value]
  | andImm | setpImm | selp => simp [maxColumns] at h

private theorem runMaxColumns_values (score : Nat → Option ℝ) :
    ∀ (is : List RItem) (D D' : Nat → Option MaxDatum),
      runMaxColumns is D = some D' →
      rReq (scalarValue score D) is = true ∧ rCond (scalarValue score D) is ∧
        rFinal (scalarValue score D) is = scalarValue score D'
  | [], _, _, h => by cases h; exact ⟨rfl, trivial, rfl⟩
  | i :: is, D, D', h => by
    cases he : maxColumns D i with
    | none => simp [runMaxColumns, he] at h
    | some E =>
      have h' : runMaxColumns is E = some D' := by simpa [runMaxColumns, he] using h
      obtain ⟨hr, hc, hf⟩ := runMaxColumns_values score is E D' h'
      obtain ⟨hr₀, hc₀, hf₀⟩ := maxColumns_value he score
      simp [rReq, rCond, rFinal, hr₀, hc₀, hf₀, hr, hc, hf]

def repeatedMaxStart (biased : Bool) : Nat := if biased then 5536 else 6747

def repeatedMaxBase (biased : Bool) : Nat := if biased then 5536 else 6720

def repeatedMaxOld (biased : Bool) : Nat := if biased then 7251 else 7255

def repeatedMaxNew (biased : Bool) : Nat := if biased then 4560 else 5509

def repeatedMaxShift (biased : Bool) : Fin 3 := if biased then 1 else 2

def repeatedMaxPacks (biased : Bool) : List Nat :=
  (shiftItems (repeatedMaxShift biased)).map (·.a)

def repeatedMaxDom (biased : Bool) : List Nat := repeatedMaxOld biased :: repeatedMaxPacks biased

def repeatedMaxSlice (biased : Bool) : List Instr :=
  if biased then
    Decoded.code173 ++ Decoded.code174 ++ Decoded.code175 ++ Decoded.code176 ++ Decoded.code177
  else
    Decoded.code210 ++ Decoded.code211 ++ Decoded.code212 ++ Decoded.code213 ++ Decoded.code214

def repeatedMaxKernel (biased : Bool) : Kernel := { kernel with code := repeatedMaxSlice biased }

private theorem repeatedMaxSlice_eq (biased : Bool) :
    (Decoded.kernel.code.drop (repeatedMaxBase biased)).take 160 = repeatedMaxSlice biased := by
  cases biased <;> kernel_rfl

def unpackOrMax (K : Kernel) (pc : Nat) : Option RItem :=
  match K.code[pc]? with
  | some ⟨none, .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg src]⟩⟩ =>
    some (.unpack lo hi src)
  | _ => (maxInstr K pc).map MaxItem.item

def repeatedMaxItems (biased : Bool) : List RItem :=
  (List.range 130).filterMap fun i => unpackOrMax (repeatedMaxKernel biased)
    (repeatedMaxStart biased - repeatedMaxBase biased + i)

def repeatedMaxInputs (biased : Bool) (r : Nat) : Option MaxDatum :=
  if r == repeatedMaxOld biased then some (.scalar [0])
  else match (repeatedMaxPacks biased).idxOf? r with
    | none => none
    | some i => some (.pair [2 * i + 1] [2 * i + 2])

private theorem repeatedMaxLength (biased : Bool) : (repeatedMaxItems biased).length = 130 := by
  cases biased <;> decide +kernel

private theorem repeatedMaxReads (biased : Bool) :
    rReadsB (repeatedMaxDom biased) (repeatedMaxItems biased) = true := by
  cases biased <;> decide +kernel

private theorem repeatedMaxVarying (biased : Bool) :
    rVaryingB (repeatedMaxItems biased) = true := by
  cases biased <;> decide +kernel

private theorem repeatedMaxShape (biased : Bool) :
    ((repeatedMaxItems biased).all (fun i => match i with
      | .unpack .. | .fmax .. => true
      | _ => false)) = true := by
  cases biased <;> decide +kernel

private theorem maxReadCodeOfSlice (K K' : Kernel) :
    ∀ (items : List RItem) (pc pc' : Nat),
      (∀ n < items.length, K.code[pc + n]? = K'.code[pc' + n]?) →
      rCodeB K pc items = rCodeB K' pc' items
  | [], _, _, _ => rfl
  | i :: items, pc, pc', hc => by
    have h₀ : K.code[pc]? = K'.code[pc']? := by simpa using hc 0 (by simp)
    have hi : i.codeB K pc = i.codeB K' pc' := by
      cases i <;> simp [RItem.codeB, h₀]
    simp only [rCodeB, hi]
    rw [maxReadCodeOfSlice K K' items (pc + 1) (pc' + 1)]
    intro n hn
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 n]
    exact hc _ (by simp only [List.length_cons]; omega)

private theorem repeatedMaxCode (biased : Bool) :
    rCodeB kernel (repeatedMaxStart biased) (repeatedMaxItems biased) = true := by
  let start := repeatedMaxStart biased
  let base := repeatedMaxBase biased
  have hb : base ≤ start ∧ start - base ≤ 30 := by cases biased <;> decide
  rw [maxReadCodeOfSlice kernel (repeatedMaxKernel biased) (repeatedMaxItems biased)
    start (start - base)]
  · cases biased <;> kernel_rfl
  · intro n hn
    rw [repeatedMaxLength] at hn
    change Decoded.kernel.code[start + n]? = (repeatedMaxSlice biased)[start - base + n]?
    rw [← repeatedMaxSlice_eq, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    congr 1
    omega

private theorem repeatedMaxOff (biased : Bool) {n : Nat} (hn : n < 130) :
    repeatedMaxStart biased + n ∉ Assumptions.swExp2Sites := by
  cases biased <;> simp [repeatedMaxStart, Assumptions.swExp2Sites] <;> omega

private theorem repeatedMaxNoRule (biased : Bool) :
    NoItemRule Assumptions.all (repeatedMaxItems biased) := by
  intro i hi hn l g t a ha
  have hf := List.all_eq_true.mp (repeatedMaxShape biased) i hi
  cases i <;> try contradiction
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def repeatedMaxLeaves (biased : Bool) : Option (List Nat) :=
  (runMaxColumns (repeatedMaxItems biased) (repeatedMaxInputs biased)).bind
    (fun state => (state (repeatedMaxNew biased)).bind scalarColumns)

set_option maxRecDepth 100000 in
private theorem repeatedMaxLeavesChecked (biased : Bool) :
    (repeatedMaxLeaves biased).isSome = true ∧
      (repeatedMaxLeaves biased).any (·.isPerm (List.range 129)) = true := by
  cases biased <;> constructor <;> kernel_rfl

/-- Both repeated max runs consume the prior running maximum and all 128 scores of
their current block.  Each lane of a packed source is followed through the unpack. -/
theorem repeatedMaxLocal {l : Launch} {g : Nat} {t : TState}
    (biased : Bool) (score : Nat → Option ℝ) (ht : At t (repeatedMaxStart biased) [])
    (hRead : ∀ r ∈ repeatedMaxDom biased,
      t.regs r = some (scalarValue score (repeatedMaxInputs biased) r)) :
    ∃ (u : TState) (mx : Option ℝ), At u (repeatedMaxStart biased + 130)
      [(repeatedMaxNew biased, scoreValue mx)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ v : EReal, scoreReal mx ≤ v ↔ ∀ i < 129, scoreReal (score i) ≤ v) ∧
      ∀ r, r ∉ rWrites (repeatedMaxItems biased) → u.regs r = t.regs r := by
  let ops := repeatedMaxItems biased
  let old := repeatedMaxInputs biased
  let dst := repeatedMaxNew biased
  obtain ⟨hCheck, hPerm⟩ := repeatedMaxLeavesChecked biased
  cases hD : runMaxColumns ops old with
  | none =>
    change (runMaxColumns ops old |>.bind (fun D => (D dst).bind scalarColumns)).isSome = true
      at hCheck
    simp [hD] at hCheck
  | some D =>
    obtain ⟨hReq, hCond, hFinal⟩ := runMaxColumns_values score ops old D hD
    have hOk (n : Nat) (hn : n < ops.length) : t.pc + n ∉ Assumptions.swExp2Sites := by
      rw [ht.1]
      exact repeatedMaxOff biased (by rwa [repeatedMaxLength] at hn)
    obtain ⟨u, hRun, hPc, hSub, hAcc, hFault, hFrame, hRegs⟩ :=
      (rRun (K := kernel) (A := Assumptions.all) (L := l) (g := g) ops
        (scalarValue score old) (repeatedMaxDom biased) t (ht.1 ▸ repeatedMaxCode biased)
        ht.2.2.2.1 hRead (repeatedMaxReads biased) hReq (repeatedMaxVarying biased)
        (repeatedMaxNoRule biased) (fun n hn => maxSeg (hOk n hn))
        (fun n hn s hs => (maxModel (hs ▸ hOk n hn)).1)
        (fun n hn s hs => (maxModel (hs ▸ hOk n hn)).2)).1 hCond
    have hWritten : dst ∈ rWrites ops := by cases biased <;> decide +kernel
    have hReg := hRegs dst (List.mem_append_left _ hWritten)
    rw [hFinal] at hReg
    change (runMaxColumns ops old |>.bind (fun D => (D dst).bind scalarColumns)).any
      (·.isPerm (List.range 129)) = true at hPerm
    rw [hD] at hPerm
    cases hDst : D dst with
    | none => simp [hDst] at hPerm
    | some d =>
      cases d with
      | pair _ _ => simp [hDst, scalarColumns] at hPerm
      | scalar cols =>
        simp only [Option.bind_some, hDst, scalarColumns, Option.any_some] at hPerm
        have hs : cols.Perm (List.range 129) := List.isPerm_iff.mp hPerm
        refine ⟨u, scoreMax score cols, ⟨?_, hSub.trans ht.2.1, hAcc.trans ht.2.2.1,
          hFault.trans ht.2.2.2.1, ?_, trivial⟩, run_rtg hRun, ?_, hFrame⟩
        · rw [hPc, ht.1, repeatedMaxLength]
        · simpa [scalarValue, hDst, MaxDatum.value] using hReg
        · intro v
          rw [scoreMax, maxScore_mem]
          simp [hs.mem_iff]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
