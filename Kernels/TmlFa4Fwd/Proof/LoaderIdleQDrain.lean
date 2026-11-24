-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderIdleDrain
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def idleQArrive (l : Launch) (g : Nat) : Event :=
  ⟨1900, .arrive ⟨.shared, g / l.block, l.sharedBase + 8⟩ 32768⟩

/-- ABI facts retained across idle query-buffer return. -/
def idleQCarry (l : Launch) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 14)]

/-- The cache drain retains the physical warp and its query release phase. -/
def terminalLoaderFrame (l : Launch) (warp phase : Nat) : List (Nat × Value) :=
  [(2535,b32 l.sharedBase),(258,.pred (decide (warp ≠ 14))),(7192,b32 phase),(1062,b32 warp)]

/-- Warp fourteen prepares the second-query wait after releasing all cache slots. -/
theorem queryDrainReadyWithPhase {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g phase : Nat} {t : TState} (ht : At t 1891 (terminalLoaderFrame l 14 phase)) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 1893 ((2305, b32 (l.sharedBase + 24)) :: (7192, b32 phase) :: idleQCarry l) := by
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1891 false ht ht.2.2.2.2.2.1 (by simp)
  obtain ⟨hvA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hBound : l.sharedBase + 24 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hPrep : Seg kernel [] l g 1 1892 [(2535, b32 l.sharedBase)] 1893
      [(2305, b32 (l.sharedBase + 24))] := by
    intro s hs
    seg_fp hs using norm_bits
  obtain ⟨u, hu, hU⟩ := hPrep v (hV.mono ⟨hV.2.2.2.2.1, trivial⟩)
  obtain ⟨huA, hFrame⟩ := loaderLinear (regs := [7192, 2535, 1062]) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  exact ⟨u, run_comp hvA huA, hU.mono ⟨hU.2.2.2.2.1,
    (hFrame 7192 (by decide)).trans hV.2.2.2.2.2.2.1,
    (hFrame 2535 (by decide)).trans hV.2.2.2.2.1,
    (hFrame 1062 (by decide)).trans hV.2.2.2.2.2.2.2.1, trivial⟩⟩

/-- The initialization-era query wait looks for the first empty generation. -/
theorem qDrainReady {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 1891 (idleDrainCarry l 14)) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u 1893 ((2305,b32 (l.sharedBase+24))::(7192,b32 1)::idleQCarry l) :=
  queryDrainReadyWithPhase hp ht

/-- The elected idle loader lane publishes the terminal expected-byte arrival. -/
theorem idleNotifyNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 1899 (idleQCarry l)) :
    ∃ s u, s.pc = 1900 ∧ At u 1901 (idleQCarry l) ∧
      Next kernel Assumptions.all l g t s
        (.arrive ⟨.shared,g/l.block,l.sharedBase+8⟩ 32768 u 1 true .cta) := by
  have hMove : Seg kernel [] l g 1 1899 [] 1900 [(2307, b32 32768)] := by
    intro s hs
    seg_fp hs using rfl
  obtain ⟨s, hs, hS⟩ := hMove t (ht.mono trivial)
  obtain ⟨hsA, hsFrame⟩ := loaderLinear (regs := [2535, 1062]) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hs
  have hSFrame := holdsSchedulerFrame ht.2.2.2.2 hsFrame (fun _ hm => List.mem_map_of_mem hm)
  let loc : Loc := ⟨.shared, g / l.block, l.sharedBase + 8⟩
  have hLoc : mbarLoc l g s 2535 8 = .ok loc := by
    have hBound : l.sharedBase + 8 < 2 ^ 32 := by have := hp.shared.2.1; omega
    have hAl : (l.sharedBase + 8) % 8 = 0 := by have := hp.shared.1; omega
    have hEff : effAddr l g s .shared 2535 8 = .ok loc :=
      effAddr_b32_off hSFrame.1 hBound
    simp [mbarLoc, hEff, loc, hAl, bind, Except.bind, pure, Except.pure]
  let u := next (mbarStateDest s (some 7861))
  have hOut : out kernel Assumptions.all l g s = .ev (.arrive loc 32768 u 1 true .cta) := by
    rw [loaderOutCore (by rw [hS.1]; decide) (by rw [hS.1]; decide)]
    rw [out_event hS.2.2.2.1 (by rw [hS.1]; exact Flow.code_1900) rfl rfl]
    have hOne : readBits l g s 32 (.imm 1) = .ok 1#64 := rfl
    simp [eventTmpl, widenMbarScope, tmaTmpl, hLoc, readBits_b32 hS.2.2.2.2.1 (by decide),
      hOne, u, bind, Except.bind, pure, Except.pure, ofExec]
  have hn : Next kernel Assumptions.all l g t s (.arrive loc 32768 u 1 true .cta) :=
    ⟨run_rtg hsA, hOut⟩
  have hAt : At u 1901 (idleQCarry l) := by
    refine ⟨by change s.pc + 1 = 1901; rw [hS.1], hS.2.1, hS.2.2.1, hS.2.2.2.1, ?_⟩
    simp [Holds, u, mbarStateDest, next, idleQCarry, hSFrame.1, hSFrame.2.1]
  exact ⟨s,u,hS.1,hAt,hn⟩

/-- The two register updates returned by the idle loader's full-warp election. -/
def idleElectionReturn (l : Launch) (g : Nat) (t : TState) (leader : Nat) : TState :=
  next (setReg (setReg t 2306 (b32 leader)) 261 (.pred (laneOf l g == leader)))

/-- The query loader elects a notification lane after the four release waits. -/
theorem idleElectionOut {l : Launch} {g : Nat} {tE : TState}
    (hE : At tE 1896 (idleQCarry l)) :
    out kernel Assumptions.all l g tE = .ev (.elect (2 ^ 32 - 1) (idleElectionReturn l g tE)) := by
  have hEPc := hE.1
  rw [loaderOutCore (by rw [hEPc]; decide) (by rw [hEPc]; decide)]
  rw [out_event hE.2.2.2.1 (by rw [hEPc]; exact Flow.code_1896) rfl rfl]
  have hMask : readBits l g tE 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hMember : electMember 4294967295 (laneOf l g) := electMember_full (by
    exact Nat.mod_lt _ (by decide))
  change Out.ev (electTmpl l g tE (some 2306) 261 (.imm (-1))) = _
  simp only [electTmpl, hMask, show (4294967295#64).toNat = 4294967295 from rfl,
    hMember, ↓reduceIte]
  rfl

/-- The decoded election continuation selects either the notification or the exit route. -/
theorem idleAfterElection {l : Launch} {g leader : Nat} {tE : TState}
    (hE : At tE 1896 (idleQCarry l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g)
      (idleElectionReturn l g tE leader) u ∧
      At u (if laneOf l g = leader then 1899 else 1901) (idleQCarry l) := by
  have hEPc := hE.1
  let after := idleElectionReturn l g tE
  let elected := laneOf l g == leader
  have hAt : At (after leader) 1897 ((261, .pred elected) :: idleQCarry l) := by
    have hF := hE
    refine ⟨by simp [after,idleElectionReturn,next,setReg,hEPc],hF.2.1,hF.2.2.1,
      hF.2.2.2.1,?_⟩
    simp [Holds,after,idleElectionReturn,elected,next,setReg,idleQCarry,hF.2.2.2.2.1,
      hF.2.2.2.2.2.1]
  have hNot (b : Bool) : Seg kernel [] l g 1 1897 [(261, .pred b)] 1898
      [(262, .pred (!b))] := by
    intro z hz
    let u := next (setReg z 262 (.pred (!b)))
    have hc := Flow.code_1897
    rw [← hz.1] at hc
    have hExec : execLocalA [] l g z
        (.int ⟨.not, .pred, false, [some 262], [.reg 261]⟩) = .ok u := by
      have hRead : readPred l g z (.reg 261) = .ok b := by
        simp [readPred, readReg, hz.2.2.2.2.1, bind, Except.bind, pure, Except.pure]
      rw [execLocalA_nil]
      change execInt l g z ⟨.not, .pred, false, [some 262], [.reg 261]⟩ = .ok u
      simp [execInt, DType.width, hRead, bind, Except.bind, pure, Except.pure, u]
    have hStep := out_tau hz.2.2.2.1 hc rfl rfl hExec
    have hRun : run kernel [] l g 1 z = some u := by
      simp [run, tauStep, hStep]
    exact ⟨u, hRun, by simp [u, next, setReg, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, At, Holds]⟩
  obtain ⟨u, hu, hU⟩ := hNot elected _ (hAt.mono ⟨hAt.2.2.2.2.1, trivial⟩)
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := [2535, 1062]) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hKeep := holdsSchedulerFrame hAt.2.2.2.2.2 huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hBranch : At u 1898 ((262, .pred (!elected)) :: idleQCarry l) :=
    hU.mono ⟨hU.2.2.2.2.1, hKeep⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1898 (!elected) hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨hwA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  refine ⟨w,run_rtg (run_comp huA hwA),?_⟩
  by_cases hLead : laneOf l g = leader <;>
    simpa [elected,hLead] using hW.mono hW.2.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Loader
