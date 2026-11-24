-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part034
public import Kernels.TmlFa4Fwd.Flow.Code.Part035
public import Kernels.TmlFa4Fwd.Flow.Code.Part037
public import Kernels.TmlFa4Fwd.Flow.Code.Part038
public import Kernels.TmlFa4Fwd.Flow.Code.Part039
public import Kernels.TmlFa4Fwd.Flow.Code.Part041
public import Lemmas.Flow.BitForms

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

structure CommitSite where
  pc : Nat
  base : Nat
  off : Nat

/-- The QK readiness commits, KV releases, Q releases, and final O readiness commits. -/
def commitSite : Fin 12 → CommitSite
  | 0 => ⟨2208, 1188, 0⟩
  | 1 => ⟨2270, 2535, 88⟩
  | 2 => ⟨2274, 2535, 56⟩
  | 3 => ⟨2418, 1188, 0⟩
  | 4 => ⟨2462, 1191, 56⟩
  | 5 => ⟨2519, 1190, 0⟩
  | 6 => ⟨2523, 1193, 56⟩
  | 7 => ⟨2537, 2535, 16⟩
  | 8 => ⟨2541, 2535, 24⟩
  | 9 => ⟨2638, 1194, 56⟩
  | 10 => ⟨2642, 6495, 0⟩
  | 11 => ⟨2646, 2535, 152⟩

/-- The selected commit site is unguarded and issues to its decoded barrier address. -/
theorem commitCode (i : Fin 12) :
    let s := commitSite i
    kernel.code[s.pc]? = some ⟨none, .tcCommit .one s.base (s.off : Int) none⟩ := by
  fin_cases i
  · exact Flow.code_2208
  · exact Flow.code_2270
  · exact Flow.code_2274
  · exact Flow.code_2418
  · exact Flow.code_2462
  · exact Flow.code_2519
  · exact Flow.code_2523
  · exact Flow.code_2537
  · exact Flow.code_2541
  · exact Flow.code_2638
  · exact Flow.code_2642
  · exact Flow.code_2646

private theorem commitRange (i : Fin 12) :
    1904 ≤ (commitSite i).pc ∧ (commitSite i).pc < 2768 := by
  fin_cases i <;> decide

/-- Single-CTA commit with one target, the issuing CTA's shared barrier. -/
def commitSpec (l : Launch) (g addr : Nat) : TcCommit.Spec :=
  ⟨.one, ⟨.shared, g / l.block, addr⟩, 1, g / l.block, 1⟩

private theorem commitResolved {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (addr : Nat) :
    TcCommit.resolve l .one (g / l.block) ⟨.shared, g / l.block, addr⟩
      (BitVec.ofNat 16 (2 ^ l.rankOfCta (g / l.block))) = some (commitSpec l g addr) := by
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show g < l.grid * l.block from hg)
  have hOne := hp.cluster.2.2
  simp [TcCommit.resolve, commitSpec, hp.launch.1, hCta, Launch.oneDim_rankOfCta hOne,
    Launch.oneDim_clusterOfCta hOne, Launch.oneDim_clusterStart hOne,
    Launch.oneDim_clusterSizeOf hOne, hp.cluster.1, Nat.mod_one]

/-- Every commit site resolves to its physical same-CTA barrier. -/
theorem commitTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g a : Nat} (hg : g < l.threads) (i : Fin 12)
    {t : TState} {F : List (Nat × Value)} (ht : At t (commitSite i).pc F)
    (hBase : ((commitSite i).base, b32 a) ∈ F)
    (hA : a + (commitSite i).off < 2 ^ 32) (hAl : (a + (commitSite i).off) % 8 = 0) :
    out kernel Assumptions.all l g t =
      .ev (.tc (.commit (commitSpec l g (a + (commitSite i).off))) (next t)) := by
  have hr := commitRange i
  rw [out_eq_core (by rw [ht.1]; exact hr.1) (by rw [ht.1]; exact hr.2),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact commitCode i) rfl rfl]
  change Out.ev (tcCommitTmpl l g t (.tcCommit .one (commitSite i).base
    ((commitSite i).off : Int) none)) = _
  have ha := mbarClusterLoc_off (L := l) (g := g) (holds_mem ht.2.2.2.2 hBase) hA hAl
  simp only [tcCommitTmpl, hg, ha, commitResolved hp hg, ↓reduceIte, bind, pure, Except.bind,
    Except.pure, ofExec]

end PTX.Kernels.TmlFa4Fwd.Mma
