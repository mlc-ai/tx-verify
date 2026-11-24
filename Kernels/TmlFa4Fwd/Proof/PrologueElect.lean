-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Kernels.TmlFa4Fwd.Flow.Code.Part001
public import Kernels.TmlFa4Fwd.Flow.Code.Part002
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Lemmas.Flow.Regs
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

/-- One warp-0 election and the instructions that select its initialization writer. -/
structure ElectSite where
  pc : Nat
  laneReg : Nat
  chosenReg : Nat
  skipReg : Nat
  skipPc : Nat
  countReg : Nat
  count : Nat

def electSites : Vector ElectSite 16 := #v[
  ⟨46, 1674, 20, 21, 52, 1675, 1⟩,
  ⟨56, 1676, 23, 24, 62, 1677, 1⟩,
  ⟨62, 1678, 25, 26, 69, 1679, 64⟩,
  ⟨73, 1680, 28, 29, 80, 1681, 1⟩,
  ⟨80, 1682, 30, 31, 86, 1683, 1⟩,
  ⟨90, 1684, 33, 34, 96, 1685, 256⟩,
  ⟨96, 1686, 35, 36, 102, 1687, 4⟩,
  ⟨105, 1688, 38, 39, 111, 1689, 1⟩,
  ⟨111, 1690, 40, 41, 117, 1691, 1⟩,
  ⟨119, 1692, 43, 44, 125, 1693, 128⟩,
  ⟨125, 1694, 45, 46, 131, 1695, 128⟩,
  ⟨135, 1696, 48, 49, 141, 1697, 128⟩,
  ⟨141, 1698, 50, 51, 147, 1699, 128⟩,
  ⟨151, 1700, 53, 54, 157, 1701, 32⟩,
  ⟨157, 1702, 55, 56, 163, 1703, 1⟩,
  ⟨166, 1704, 58, 59, 172, 1705, 4⟩]

def electSite (i : Fin 16) : ElectSite := electSites[i]

def electOp (s : ElectSite) : Op :=
  .warp ⟨.elect, none, [some s.laneReg, some s.chosenReg], [], some (.imm (-1))⟩

private def notChosen (s : ElectSite) : IntInstr :=
  ⟨.not, .pred, false, [some s.skipReg], [.reg s.chosenReg]⟩

private def countMove (s : ElectSite) : MoveInstr :=
  ⟨.scalar, .int .b 32, [some s.countReg], [.imm s.count]⟩

theorem electCode (i : Fin 16) : kernel.code[(electSite i).pc]? =
    some ⟨none, electOp (electSite i)⟩ := by
  fin_cases i
  · exact Flow.code_46
  · exact Flow.code_56
  · exact Flow.code_62
  · exact Flow.code_73
  · exact Flow.code_80
  · exact Flow.code_90
  · exact Flow.code_96
  · exact Flow.code_105
  · exact Flow.code_111
  · exact Flow.code_119
  · exact Flow.code_125
  · exact Flow.code_135
  · exact Flow.code_141
  · exact Flow.code_151
  · exact Flow.code_157
  · exact Flow.code_166

private theorem electLocalCode (i : Fin 16) :
    let s := electSite i
    kernel.code[s.pc + 1]? = some ⟨none, .int (notChosen s)⟩ ∧
      kernel.code[s.pc + 2]? = some ⟨some (s.skipReg, false), .bra s.skipPc false⟩ ∧
      kernel.code[s.pc + 3]? = some ⟨none, .move (countMove s)⟩ := by
  fin_cases i
  · exact ⟨Flow.code_47, Flow.code_48, Flow.code_49⟩
  · exact ⟨Flow.code_57, Flow.code_58, Flow.code_59⟩
  · exact ⟨Flow.code_63, Flow.code_64, Flow.code_65⟩
  · exact ⟨Flow.code_74, Flow.code_75, Flow.code_76⟩
  · exact ⟨Flow.code_81, Flow.code_82, Flow.code_83⟩
  · exact ⟨Flow.code_91, Flow.code_92, Flow.code_93⟩
  · exact ⟨Flow.code_97, Flow.code_98, Flow.code_99⟩
  · exact ⟨Flow.code_106, Flow.code_107, Flow.code_108⟩
  · exact ⟨Flow.code_112, Flow.code_113, Flow.code_114⟩
  · exact ⟨Flow.code_120, Flow.code_121, Flow.code_122⟩
  · exact ⟨Flow.code_126, Flow.code_127, Flow.code_128⟩
  · exact ⟨Flow.code_136, Flow.code_137, Flow.code_138⟩
  · exact ⟨Flow.code_142, Flow.code_143, Flow.code_144⟩
  · exact ⟨Flow.code_152, Flow.code_153, Flow.code_154⟩
  · exact ⟨Flow.code_158, Flow.code_159, Flow.code_160⟩
  · exact ⟨Flow.code_167, Flow.code_168, Flow.code_169⟩

/-- The full member mask includes every thread's lane. -/
private theorem fullMember (l : Launch) (g : Nat) : electMember (2 ^ 32 - 1) (laneOf l g) := by
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have he (x : Fin 32) : electMember (2 ^ 32 - 1) x.val := by
    fin_cases x <;> decide
  exact he ⟨_, hl⟩

def electedState (l : Launch) (g : Nat) (t : TState) (s : ElectSite) (leader : Nat) : TState :=
  next (setReg (setReg t s.laneReg (b32 leader)) s.chosenReg (.pred (laneOf l g == leader)))

/-- The decoded election has the full mask and the specified register continuation. -/
theorem electOut {l : Launch} {g : Nat} {t : TState} (i : Fin 16)
    (hp : t.pc = (electSite i).pc) (hf : t.fault = none) :
    out kernel [] l g t = .ev (.elect (2 ^ 32 - 1) (electedState l g t (electSite i))) := by
  unfold out
  rw [hp, hf, electCode i]
  change Out.ev
    (electTmpl l g t (some (electSite i).laneReg) (electSite i).chosenReg (.imm (-1))) = _
  have hm : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 := by decide
  simp only [electTmpl, readBits, pure, Except.pure, hm, fullMember, ↓reduceIte]
  rfl

private theorem evalNotChosen {l : Launch} {g : Nat} {t : TState} {s : ElectSite} {ok : Bool}
    (hf : t.fault = none) (hpc : t.pc = s.pc + 1)
    (hr : t.regs s.chosenReg = some (.pred ok))
    (hc : kernel.code[s.pc + 1]? = some ⟨none, .int (notChosen s)⟩) :
    tauStep kernel [] l g t = some (next (setReg t s.skipReg (.pred (!ok)))) := by
  have he : execLocal l g t (.int (notChosen s)) = .ok
    (next (setReg t s.skipReg (.pred (!ok)))) := by
    rw [execLocal_int rfl]
    simp [notChosen, execInt, DType.width, readPred, readReg, hr, bind, Except.bind, pure,
      Except.pure]
  have he' : execLocalA [] l g t (.int (notChosen s)) = _ := he
  simp only [tauStep, out, hf, hpc, hc, guardHolds, pure, Except.pure, ↓reduceIte, he',
    show (Op.int (notChosen s)).isLocal = true by rfl]

private theorem countRun {l : Launch} {g : Nat} {t : TState} (i : Fin 16)
    (hf : t.fault = none) (hpc : t.pc = (electSite i).pc + 3) :
    tauStep kernel [] l g t = some
      (next (setReg t (electSite i).countReg (b32 (electSite i).count))) := by
  have hb : (electSite i).count < 2 ^ 32 := by fin_cases i <;> decide
  have he : execLocal l g t (.move (countMove (electSite i))) =
      .ok (next (setReg t (electSite i).countReg (b32 (electSite i).count))) := by
    rw [execLocal_move rfl]
    simp [countMove, execMove, readValue, readBits, DType.width, Value.bytes, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hb (by decide), b32]
  have he' : execLocalA [] l g t (.move (countMove (electSite i))) = _ := he
  simp only [tauStep, out, hf, hpc, (electLocalCode i).2.2, guardHolds, pure, Except.pure,
    ↓reduceIte, he', show (Op.move (countMove (electSite i))).isLocal = true by rfl]

/-- An elected lane reaches the first initializer with its count. The other lanes join at
`skipPc`, leaving the existing mbarrier state untouched. -/
theorem electRouteWith {A : List Assumption} [StartupAgreement A]
    {l : Launch} {g : Nat} {t : TState} (i : Fin 16) (ok : Bool)
    (hp : t.pc = (electSite i).pc + 1) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hc : t.regs (electSite i).chosenReg = some (.pred ok)) :
    let s := electSite i
    let u := next (setReg t s.skipReg (.pred (!ok)))
    run kernel A l g (if ok then 3 else 2) t = some
      (if ok then next (setReg (next u) s.countReg (b32 s.count)) else
        { u with pc := s.skipPc }) := by
  let s := electSite i
  let u := next (setReg t s.skipReg (.pred (!ok)))
  have hBound : s.pc + 3 < 179 := by fin_cases i <;> decide
  have lift {a b : TState} (ha : a.pc < 179) (h : tauStep kernel [] l g a = some b) :
      tauStep kernel A l g a = some b := startupTau (.inl ha) h
  have h1 : tauStep kernel [] l g t = some u :=
    evalNotChosen hf hp hc (electLocalCode i).1
  have hpc : u.pc = s.pc + 2 := by change t.pc + 1 = s.pc + 2; rw [hp]
  have hf' : u.fault = none := hf
  have hs' : u.sub = 0 := hs
  have ha' : u.acc = [] := ha
  have hr : u.regs s.skipReg = some (.pred (!ok)) := by simp [u, next, setReg]
  have hcode : kernel.code[s.pc + 2]? = some ⟨some (s.skipReg, false), .bra s.skipPc false⟩ :=
    (electLocalCode i).2.1
  have hPcA : t.pc < 179 := by rw [hp]; change s.pc + 1 < 179; omega
  have hPcB : u.pc < 179 := by rw [hpc]; omega
  cases hok : ok
  · have h2 : tauStep kernel [] l g u = some { u with pc := s.skipPc } := by
      simp [tauStep, out, hpc, hf', hcode, hr, hok, guardHolds, readReg, Op.isLocal,
        execLocalA, execLocalRule, execLocal, Op.rule, execBranch, bind, Except.bind, pure,
          Except.pure ]
    simp only [run, lift hPcA h1, lift hPcB h2, Bool.false_eq_true, ↓reduceIte,
      Option.bind_some]
    simp only [u, s, hok]
  · have h2 : tauStep kernel [] l g u = some (next u) := by
      simp [tauStep, out, hpc, hf', hcode, hr, hok, guardHolds, readReg, bind, Except.bind, pure,
        Except.pure, skip, next, hs', ha']
    have hp' : (next u).pc = s.pc + 3 := by change u.pc + 1 = s.pc + 3; rw [hpc]
    have h3 := countRun (l := l) (g := g) (t := next u) i hf' hp'
    have hPcC : (next u).pc < 179 := by rw [hp']; exact hBound
    simp only [run, lift hPcA h1, lift hPcB h2, lift hPcC h3, ↓reduceIte, Option.bind_some]
    simp only [u, s, hok]

end
end PTX.Kernels.TmlFa4Fwd.Prologue
