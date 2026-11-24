-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkAssembly
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue

noncomputable section

def firstQKFrame (l : Launch) : List (Nat × Value) :=
  [(9632, b32 0x8200490), (2536, b32 0), (1188, b32 (l.sharedBase + 80)),
   (2562, b32 (l.sharedBase + 8)), (2535,b32 l.sharedBase)] ++ qDescriptorFacts l 1

/-- Registers live through the first QK's two lane-zero broadcasts. -/
def firstQKBroadcastFacts (l : Launch) : List (Nat × Value) :=
  (1178, b32 (l.sharedBase + 68608)) :: firstQKFrame l

/-- The first QK setup converts the actual cache base to its slot-zero key descriptor. -/
theorem firstKeyWordLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 3 2148 [(1178,b32 (l.sharedBase+68608))] 2151
      [(2560,b32 (firstKLow l))] := by
  have hBound := hp.shared.2.1
  have hAlign := hp.shared.1
  have hMask := descriptorStart_mask (start := l.sharedBase + 68608) (by omega) (by omega)
  have hOr : (l.sharedBase + 68608) / 16 ||| 65536 =
      (l.sharedBase + 68608) / 16 + 65536 := by
    have hl : (l.sharedBase + 68608) / 16 < 2 ^ 16 := by omega
    rw [Nat.or_comm, show (65536 : Nat) = 2 ^ 16 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt hl, Nat.mul_one, Nat.add_comm]
  have h1 : l.sharedBase + 68608 < 4294967296 := by omega
  have h2 : (l.sharedBase + 68608) / 16 < 4294967296 := by omega
  have hZero : kvSlot 0 = 0 := rfl
  intro t ht
  seg_fp ht using
    (simp only [firstKLow, kvStart, hZero, Nat.mul_zero, Nat.add_zero]
     nf_simp
     simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, hMask, hOr])

private theorem assemblyKWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 3 2148 (firstQKBroadcastFacts l) 2151
      ((2560, b32 (firstKLow l)) :: firstQKFrame l) := by
  have hCore := firstKeyWordLocal hp g
  intro t ht
  obtain ⟨u, hRun, hU⟩ := hCore t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  let regs := [9632, 2536, 1188, 2562, 2535] ++ (List.range 8).map (9624 + ·)
  have hWrites : ((kernel.code.drop 2148).take 3).all
      (fun i => regs.all fun r => !(writesRegs i.op).contains r) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hFall : ((kernel.code.drop 2148).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hFrame : Holds u.regs (firstQKFrame l) := by
    apply holdsSchedulerFrame (regs := regs) ht.2.2.2.2.2
    · intro r hr
      exact schedulerLocalFrame hWrites hFall hRun ht.1.ge (by rw [ht.1]) hr
    · intro pair hm
      simp only [firstQKFrame, List.cons_append, List.mem_cons] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | hQ
      all_goals try (simp [regs]; done)
      unfold qDescriptorFacts at hQ
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hQ
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr i.isLt))
  exact ⟨u, hRun, hU.mono ⟨hU.2.2.2.2.1, hFrame⟩⟩

/-- The decoded full-mask indexed shuffle uses lane zero as its source. -/
theorem laneZeroBroadcast {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g pc src dst value : Nat} {s : TState}
    (hb : 1904 ≤ pc ∧ pc < 2768) (hs : At s pc [(src, b32 value)])
    (hc : kernel.code[pc]? = some ⟨none, .warp ⟨.shfl .idx, some (.int .b 32), [some dst],
      [.reg src, .imm 0, .imm 31], some (.imm (-1))⟩⟩) :
    out kernel Assumptions.all l g s =
      .ev (.shfl .idx (b32 value) 0 31 (fun v _ => next (setReg s dst v))) := by
  have hPc := hs.1
  rw [out_eq_core (by omega) (by omega),
    out_event hs.2.2.2.1 (by rw [hs.1]; exact hc) rfl rfl]
  change Out.ev (shflTmpl l g s .idx dst none (.reg src) (.imm 0) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hs.2.2.2.2.1, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

private theorem firstQKFrameFresh {l : Launch} {dst : Nat}
    (hDst : dst = 2564 ∨ dst = 2574) :
    ∀ pair ∈ firstQKFrame l, pair.1 ≠ dst := by
  intro pair hm
  simp only [firstQKFrame, List.cons_append, List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | hQ
  all_goals rcases hDst with rfl | rfl
  all_goals try exact of_decide_eq_true rfl
  all_goals
    unfold qDescriptorFacts at hQ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hQ
    change 9624 + i.val ≠ _
    omega

/-- When the opening K acquires have returned, the maximal warp records both first QK
broadcasts and reaches the election with the resolved descriptors. -/
theorem firstQKAfterBroadcastOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2148 (fun _ => firstQKBroadcastFacts l)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2153 (fun _ => firstQKInputFacts l)
      (shuffles+2) votes ends) := by
  obtain ⟨locals⟩ := cur.advanceLocal (G := fun _ => (2560,b32 (firstKLow l)) :: firstQKFrame l)
    fun lane hl => by
      have hAt := cur.checkpoint lane hl
      obtain ⟨u,hu,hU⟩ := assemblyKWord hp (warpLane l g lane) (cur.state lane) hAt
      exact ⟨u,run_rtg (localRun (by decide) (by decide) hAt.1 (by
        set_option maxRecDepth 100000 in kernel_rfl) hu),hU⟩
  have hK : ∀ lane < 32, ∀ pair ∈ (2560,b32 (firstKLow l)) :: firstQKFrame l,
      pair.1 ≠ 2564 := by
    intro _ _ pair hm
    rcases List.mem_cons.mp hm with rfl | hf
    · exact of_decide_eq_true rfl
    · exact firstQKFrameFresh (.inl rfl) pair hf
  obtain ⟨keys⟩ := locals.consumeShuffle (dst := 2564) hp hMax hg .idx
    (fun _ => b32 (firstKLow l)) (fun _ => 0) (fun _ => 31) hK
    (fun lane hl => laneZeroBroadcast hp (by decide) ((locals.checkpoint lane hl).mono
      ⟨(locals.checkpoint lane hl).2.2.2.2.1,trivial⟩) Flow.code_2151)
  have hScore : ∀ lane < 32,
      ∀ pair ∈ (2564,b32 (firstKLow l)) :: (2560,b32 (firstKLow l)) :: firstQKFrame l,
      pair.1 ≠ 2574 := by
    intro _ _ pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact of_decide_eq_true rfl
    · rcases List.mem_cons.mp hm with rfl | hf
      · exact of_decide_eq_true rfl
      · exact firstQKFrameFresh (.inr rfl) pair hf
  obtain ⟨scores⟩ := keys.consumeShuffle (dst := 2574) hp hMax hg .idx
    (fun _ => b32 0) (fun _ => 0) (fun _ => 31) hScore
    (fun lane hl => laneZeroBroadcast hp (by decide) ((keys.checkpoint lane hl).mono
      ⟨(keys.checkpoint lane hl).2.2.2.2.2.2.2.1,trivial⟩) Flow.code_2152)
  apply scores.advanceLocal
  intro lane hl
  have hAt := scores.checkpoint lane hl
  have hf := hAt.2.2.2.2
  exact ⟨scores.state lane,.refl,hAt.mono ⟨hf.1,hf.2.1,hf.2.2.2⟩⟩

/-- A reachable election cannot have occurred earlier when subsequent instructions stay
above its return boundary. -/
theorem noEarlierMmaElection {l : Launch} {X : Execution}
    (i : Fin 20)
    (hCodeElect : kernel.code[(electSite i).pc]? = some
      ⟨none, .warp ⟨.elect, none, [(electSite i).result, some (electSite i).pred], [],
        some (.imm (-1))⟩⟩)
    (hTail : (kernel.code.drop ((electSite i).pc + 1)).all
      (fun ins => Thread.staysPastEvent ((electSite i).pc + 1) ins.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide ((electSite i).pc + 1 ≤ seg.stop)
      | none => false) = true)
    {g pos : Nat} {t u : TState} {F : List (Nat × Value)} (ht : At u (electSite i).pc F)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    {j mask inst leader : Nat} (hj : j < pos)
    (he : X.Elect (g,j) (electSite i).pc mask inst leader) : False := by
  let event : Event := ⟨(electSite i).pc,.elect 4294967295 0 0⟩
  let es := (X.tr g).take pos ++ [event]
  have hNow : EStep kernel Assumptions.all l g u event (some (electState l g u i 0)) :=
    ⟨_,electTemplate i ht,0,0,by rw [ht.1]; rfl,rfl⟩
  have hr : Run kernel Assumptions.all l g {} es (some (electState l g u i 0)) :=
    hPast.snoc hLocal hNow
  have hBefore : j < ((X.tr g).take pos).length := by
    have hjOld : j < (X.tr g).length := len_of_get he
    simp only [List.length_take]
    omega
  have hGet : es[j]? = some ⟨(electSite i).pc,.elect mask inst leader⟩ := by
    dsimp only [es]
    rw [List.getElem?_append_left hBefore,List.getElem?_take_of_lt hj]
    exact he
  obtain ⟨source,after,hStep,hRun⟩ := hr.after_event hGet (by
    simp only [es,List.length_append,List.length_singleton]
    omega)
  obtain ⟨ins,hCode,_,hFire⟩ := EventFrame.estep_event_source hStep
  have hSite : source.pc = (electSite i).pc := (EventFrame.estep_source_pc hStep).symm
  rw [hSite,hCodeElect] at hCode
  obtain rfl := Option.some.inj hCode.symm
  obtain ⟨_,_,_,_,hAfter⟩ := fires_elect hFire
  have hFloor : (electSite i).pc+1 ≤ after.pc := by
    rw [hAfter]
    cases (electSite i).result <;> simp [next, setReg, hSite]
  have hMem : event ∈ es.drop (j+1) := by
    apply List.mem_of_getElem? (i := ((X.tr g).take pos).length - (j+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : j+1 ≤ ((X.tr g).take pos).length)]
    dsimp only [es]
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  obtain ⟨_,hWalk⟩ := walkFromRun hRun
  have hLate := Thread.eventTailEvents hTail hSegments hWalk hFloor event hMem
  change (electSite i).pc + 1 ≤ (electSite i).pc at hLate
  omega

/-- The assembled QK inputs survive the real full-warp election that selects an issuer. -/
theorem firstQKElectedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2153 (fun _ => firstQKInputFacts l)
      shuffles votes ends) :
    ∃ leader : Fin 32, ∃ done : SchedulerWarpReached l X g 2154
      (fun lane => (9636,.pred (laneOf l (warpLane l g lane) == leader.val)) ::
        firstQKInputFacts l) shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+1 ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) 2153 4294967295 inst leader := by
  have hPred : ∀ pair ∈ firstQKInputFacts l, pair.1 ≠ (electSite 0).pred := by
    intro pair hm
    simp only [firstQKInputFacts,List.cons_append,List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hQ
    all_goals try exact of_decide_eq_true rfl
    unfold qDescriptorFacts at hQ
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hQ
    have := i.isLt
    change 9624 + i.val ≠ 9636
    omega
  exact cur.consumeElection hp hMax hg (fun lane => electState l (warpLane l g lane)
      (cur.state lane) 0)
    (fun lane leader => (9636,.pred (laneOf l (warpLane l g lane) == leader)) ::
      firstQKInputFacts l)
    (fun lane hl _ hj _ _ _ he =>
      noEarlierMmaElection 0 Flow.code_2153 (by decide +kernel) (by decide +kernel)
        (cur.checkpoint lane hl) (cur.recorded lane hl)
        (cur.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 0 (cur.checkpoint lane hl))
    (fun lane hl leader => electStateFrame 0 (cur.checkpoint lane hl) leader hPred
      (by simp [electSite]))

end
end PTX.Kernels.TmlFa4Fwd.Mma
