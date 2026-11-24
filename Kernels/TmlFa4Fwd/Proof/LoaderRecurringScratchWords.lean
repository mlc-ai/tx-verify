-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSaveAddress
public import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout
public import Kernels.TmlFa4Fwd.Proof.LoaderProgress
public import Kernels.TmlFa4Fwd.Flow.Code.Part015
public import Kernels.TmlFa4Fwd.Flow.Code.Part018
public import Kernels.TmlFa4Fwd.Flow.Code.Part019
public import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Each recurring pointer spill reads a physical page and within-page row from
the two lane-private arrays refreshed immediately before the associated K/V pair. -/
def recurringScratchWord (site : Fin 4) (isRow : Bool) : ScratchReloadSite :=
  match site, isRow with
  | 0, false => ⟨968, 7655, 7656, 3, 949⟩
  | 0, true  => ⟨970, 7657, 7658, 2, 953⟩
  | 1, false => ⟨1214, 7709, 7710, 3, 949⟩
  | 1, true  => ⟨1216, 7711, 7712, 2, 953⟩
  | 2, false => ⟨1438, 7770, 7771, 3, 1419⟩
  | 2, true  => ⟨1440, 7772, 7773, 2, 1423⟩
  | 3, false => ⟨1619, 7814, 7815, 3, 1419⟩
  | 3, true  => ⟨1621, 7816, 7817, 2, 1423⟩

private theorem recurringScratchWordCode (site : Fin 4) (isRow : Bool) :
    ScratchReloadCode (recurringScratchWord site isRow) := by
  fin_cases site <;> cases isRow
  · exact Flow.code_968
  · exact Flow.code_970
  · exact Flow.code_1214
  · exact Flow.code_1216
  · exact Flow.code_1438
  · exact Flow.code_1440
  · exact Flow.code_1619
  · exact Flow.code_1621

/-- At a live recurring scratch reload the actual event reads the selected local word. -/
theorem recurringScratchWordAccess {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g i : Nat} (site : Fin 4) (isRow : Bool) (entry : Fin 2)
    {t : TState} {ending : Option TState} :
    let op := recurringScratchWord site isRow
    let acc := scratchReloadAccess l g op entry
    At t op.pc [(op.base, b64 acc.loc.addr)] →
    Run kernel Assumptions.all l g t ((X.tr g).drop i) ending →
    (X.tr g).drop i ≠ [] → ∃ bytes, X.get (g, i) = some ⟨op.pc, .rd acc bytes⟩ := by
  dsimp only
  intro ht hr hMore
  let op := recurringScratchWord site isRow
  let a := scratchReloadAccess l g op entry
  have hRange : 174 ≤ op.pc ∧ op.pc < 1906 := by fin_cases site <;> cases isRow <;> decide
  have hArray : ¬ op.array.val < 2 := by fin_cases site <;> cases isRow <;> decide
  have hNext : Next kernel Assumptions.all l g t t
      (.read a (afterAccessLoad t (.sign 64) 32 [op.destination])) :=
    ⟨.refl, scratchReloadTemplate hp op (recurringScratchWordCode site isRow)
      hRange hArray entry ht⟩
  obtain ⟨_, _, he, ⟨bytes, _, rfl, _⟩, _⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hr hMore
  exact ⟨bytes, by simpa only [ht.1] using he⟩

/-- The actual scalar reload sign-extends the latest word in the selected scratch
slot. The address and 4-byte extent are exact for both entries of both arrays. -/
theorem recurringScratchWordObservedInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g w i value : Nat} (hwi : w < i) (hValue : value < 2 ^ 31)
    (site : Fin 4) (isRow : Bool) (entry : Fin 2) {t : TState} {ending : Option TState} :
    let op := recurringScratchWord site isRow
    let acc := scratchReloadAccess l g op entry
    At t op.pc [(op.base, b64 acc.loc.addr)] →
    Run kernel Assumptions.all l g t ((X.tr g).drop i) ending →
    (X.tr g).drop i ≠ [] →
    X.get (g, w) = some ⟨op.store, .wr acc (b32 value).toBytes⟩ →
    (∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers (acc.loc.at k) → j ≤ w ∨ i < j) →
    X.get (g, i) = some ⟨op.pc, .rd acc ((b32 value).toBytes.map some)⟩ ∧
      At (next (setReg t op.destination (b64 value))) (op.pc + 1)
        [(op.destination, b64 value)] ∧
      Run kernel Assumptions.all l g (next (setReg t op.destination (b64 value)))
        ((X.tr g).drop (i + 1)) ending := by
  dsimp only
  intro ht hr hMore hStore hLast
  exact scratchWordReloadObservedAtInPrefix hp hX hwi hValue (recurringScratchWord site isRow)
    (recurringScratchWordCode site isRow)
    (by fin_cases site <;> cases isRow <;> decide)
    (by fin_cases site <;> cases isRow <;> decide)
    entry ht hr hMore hStore hLast

end
end PTX.Kernels.TmlFa4Fwd.Loader
