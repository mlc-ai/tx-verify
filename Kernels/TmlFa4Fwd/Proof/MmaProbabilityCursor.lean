-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyIntervals
public import Kernels.TmlFa4Fwd.Proof.MmaReadySegments
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.PrologueNonzero
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part039

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue

/-- The steady and terminal sites for a physical probability packet. -/
def probabilityWait (packet : Fin 4) (terminal : Bool) : Fin 14 :=
  if terminal then (#v[10, 11, 12, 13] : Vector (Fin 14) 4)[packet]
  else (#v[4, 5, 7, 8] : Vector (Fin 14) 4)[packet]

def probabilityPc (packet : Fin 4) (terminal : Bool) : Nat :=
  (waitSite (probabilityWait packet terminal)).pc

/-- Retain the parity of the successful waits for one packet. -/
def probabilityMark (packet : Fin 4) (e : Event) : Option Nat :=
  match e.kind with
  | .wait _ parity true _ _ =>
    if e.pc = probabilityPc packet false ∨ e.pc = probabilityPc packet true then some parity
    else none
  | _ => none

/-- A finite successful poll history alternates from its entry parity. -/
inductive ProbabilityAlternates : Nat → List Nat → Prop
  | nil (q : Nat) : ProbabilityAlternates q []
  | cons {q : Nat} {rest : List Nat} :
      ProbabilityAlternates (q ^^^ 1) rest → ProbabilityAlternates q (q :: rest)

private def probabilityRegs : List Nat := [2535, 2610, 2614, 2615, 2618]

private def packetAddress (l : Launch) (packet : Fin 4) : Nat :=
  l.sharedBase + (#v[96, 112, 104, 120] : Vector Nat 4)[packet]

private def probabilityFrame (l : Launch) : List (Nat × Value) :=
  [(2610, b32 (packetAddress l 0)), (2614, b32 (packetAddress l 1)),
    (2615, b32 (packetAddress l 2)), (2618, b32 (packetAddress l 3))] ++ readyFrame l

private def phaseFrame (l : Launch) (q : Nat) : List (Nat × Value) :=
  (7205, b32 q) :: probabilityFrame l

private def probabilityInterval (packet : Fin 4) (i : Fin 9) : ReadyInterval :=
  let steady := probabilityPc packet false
  let tail := probabilityPc packet true
  let live := 7205 :: probabilityRegs
  match i with
  | 0 => ⟨1908, 2275, [2275, 2763], [2535]⟩
  | 1 => ⟨2279, 2281, [2281], probabilityRegs⟩
  | 2 => ⟨2282, 2288, [2288, 2534], live⟩
  | 3 => ⟨2291, steady, [steady], live⟩
  | 4 => ⟨steady + 3, 2529, [2529], live⟩
  | 5 => ⟨2530, 2534, [2291, 2534], live⟩
  | 6 => ⟨2534, tail, [tail], live⟩
  | 7 => ⟨tail + 3, 2768, [3099], []⟩
  | 8 => ⟨2763, 2768, [3099], []⟩

private theorem intervalBounds (packet : Fin 4) (i : Fin 9) :
    let v := probabilityInterval packet i
    1907 ≤ v.lo ∧ v.hi ≤ 2768 := by
  fin_cases packet <;> fin_cases i <;> decide

private theorem intervalCode (packet : Fin 4) (i : Fin 9) {pc : Nat} {ins : Instr}
    (hInside : (probabilityInterval packet i).inside pc) (hc : kernel.code[pc]? = some ins) :
    (probabilityInterval packet i).code pc ins = true := by
  let interval := probabilityInterval packet i
  let code := ((kernel.code.drop interval.lo).take (interval.hi - interval.lo)).zipIdx interval.lo
  have hCode : code.all (fun pair => interval.code pair.2 pair.1) = true := by
    fin_cases packet <;> fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hCode (ins, pc)
  apply List.mem_of_getElem? (i := pc - interval.lo)
  change interval.lo ≤ pc ∧ pc < interval.hi at hInside
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hInside.1, hc]
  rfl

private theorem intervalErase (packet : Fin 4) (i : Fin 9) (e : Event)
    (hIn : (probabilityInterval packet i).inside e.pc) :
    probabilityMark packet e = none := by
  have out (b : Bool) : ¬ (probabilityInterval packet i).inside (probabilityPc packet b) := by
    fin_cases packet <;> fin_cases i <;> cases b <;> decide
  have hNo (b : Bool) : e.pc ≠ probabilityPc packet b :=
    fun he => out b (he ▸ hIn)
  simp [probabilityMark, hNo]
  split <;> rfl

private theorem atProbabilityExit (packet : Fin 4) (i : Fin 9) {s : TState}
    {F : List (Nat × Value)} (hp : s.pc ∈ (probabilityInterval packet i).exits)
    (hf : s.fault = none) (hs : RoleShape s) (hF : Holds s.regs F) : At s s.pc F := by
  have hNo : ∀ pc ∈ (probabilityInterval packet i).exits, pc ≠ 1909 := by
    fin_cases packet <;> fin_cases i <;> decide
  exact ⟨rfl, hs.2.2 (hNo _ hp), hs.2.1, hf, hF⟩

private theorem intervalSequence (packet : Fin 4) (i : Fin 9) {l : Launch} {g q : Nat}
    {s : TState} {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hPc : (probabilityInterval packet i).inside s.pc) (hs : At s s.pc F)
    (hWarp : (1062, b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (probabilityInterval packet i).keep)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, u.pc ∈ (probabilityInterval packet i).exits → At u u.pc F →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      ProbabilityAlternates q (tail.filterMap (probabilityMark packet))) :
    ProbabilityAlternates q (es.filterMap (probabilityMark packet)) := by
  have hShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩
  rcases certifiedIntervalCut (probabilityMark packet) (probabilityInterval packet i)
      (intervalBounds packet i) (intervalCode packet i)
      (fun e h => intervalErase packet i e h) hw hPc
      ⟨hShape, holds_mem hs.2.2.2.2 hWarp⟩ hs.2.2.2.2 hKeep with
    h | ⟨u, pre, tail, post, hE, hP, hL, hX, hF, hS, hH, hw'⟩
  · rw [h]; exact .nil _
  · rw [hE, List.filterMap_append, hP, List.nil_append]
    exact after hX (atProbabilityExit packet i hX hF hS.1 hH) hL hw'

private theorem probabilitySeed (l : Launch) (g : Nat) :
    Seg kernel Assumptions.all l g 1 2281 (probabilityFrame l) 2282 (phaseFrame l 0) := by
  intro t ht
  simp only [phaseFrame, probabilityFrame, readyFrame, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using decide

private theorem probabilityToggle (l : Launch) (g q : Nat) (hQ : q < 2) :
    Seg kernel Assumptions.all l g 1 2529 (phaseFrame l q) 2530 (phaseFrame l (q ^^^ 1)) := by
  interval_cases q <;> intro t ht <;>
    simp only [phaseFrame, probabilityFrame, readyFrame, List.cons_append, List.nil_append]
      at ht ⊢ <;> seg_fp ht using decide

private theorem probabilityReseed (l : Launch) (g : Nat) :
    Seg kernel Assumptions.all l g 3 2288 (probabilityFrame l) 2291 (phaseFrame l 0) := by
  intro t ht
  simp only [phaseFrame, probabilityFrame, readyFrame, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using decide

private theorem probabilityAdd {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g pc dst off : Nat) {F : List (Nat × Value)}
    (hc : kernel.code[pc]? =
      some ⟨none, .int ⟨.add, .int .s 32, false, [some dst], [.reg 2535, .imm off]⟩⟩)
    (hPc : 1907 ≤ pc ∧ pc < 2768) (hOff : off ≤ 120)
    (hBase : (2535, b32 l.sharedBase) ∈ F) (hFresh : ∀ f ∈ F, f.1 ≠ dst) :
    Seg kernel Assumptions.all l g 1 pc F (pc + 1) ((dst, b32 (l.sharedBase + off)) :: F) := by
  intro t ht
  let u := next (setReg t dst (b32 (l.sharedBase + off)))
  have hWidth : l.sharedBase + off < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hTau := evalSharedAdd (g := g) ht.1 ht.2.2.2.1 (holds_mem ht.2.2.2.2 hBase) hWidth hc
  refine ⟨u, localRun (by omega) hPc.2 ht.1 rfl (by simpa [u, run] using hTau), ?_⟩
  exact ht.set hFresh

private theorem probabilityAddresses {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) : Seg kernel Assumptions.all l g 4 2275 (readyFrame l) 2279
      (probabilityFrame l) := by
  have a := probabilityAdd hp g 2275 2610 96 (F := readyFrame l)
    Flow.code_2275 (by decide) (by decide) (by simp [readyFrame]) (by simp [readyFrame])
  have b := probabilityAdd hp g 2276 2614 112
    (F := (2610, b32 (l.sharedBase + 96)) :: readyFrame l)
    Flow.code_2276 (by decide) (by decide) (by simp [readyFrame]) (by simp [readyFrame])
  have c := probabilityAdd hp g 2277 2615 104
    (F := (2614, b32 (l.sharedBase + 112)) :: (2610, b32 (l.sharedBase + 96)) :: readyFrame l)
    Flow.code_2277 (by decide) (by decide) (by simp [readyFrame]) (by simp [readyFrame])
  have d := probabilityAdd hp g 2278 2618 120
    (F := (2615, b32 (l.sharedBase + 104)) :: (2614, b32 (l.sharedBase + 112)) ::
      (2610, b32 (l.sharedBase + 96)) :: readyFrame l)
    Flow.code_2278 (by decide) (by decide) (by simp [readyFrame]) (by simp [readyFrame])
  apply (((a.comp b).comp c).comp d).weaken_end
  intro R h
  simpa [probabilityFrame, packetAddress, Holds, and_assoc, and_comm, and_left_comm] using h

private theorem cutoffLocals {l : Launch} {g n pc nextPc q : Nat} {packet : Fin 4}
    {s : TState} {F G : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hSeg : Seg kernel Assumptions.all l g n pc F nextPc G) (ht : At s pc F)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u post}, At u nextPc G → post.length ≤ vs.length →
      Walk kernel Assumptions.all l g u es post →
      ProbabilityAlternates q (es.filterMap (probabilityMark packet))) :
    ProbabilityAlternates q (es.filterMap (probabilityMark packet)) := by
  obtain ⟨u, hr, hu⟩ := hSeg s ht
  rcases advanceWalkLocals hr hw with rfl | ⟨post, hLen, _, hWalk⟩
  · exact .nil _
  · exact after hu (by omega) hWalk

private theorem probabilityPoll {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (packet : Fin 4) (terminal : Bool) {g q : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hQ : q < 2) (hs : At s (probabilityPc packet terminal) (phaseFrame l q))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, At u (probabilityPc packet terminal + 3) (phaseFrame l q) →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      ProbabilityAlternates (q ^^^ 1) (tail.filterMap (probabilityMark packet))) :
    ProbabilityAlternates q (es.filterMap (probabilityMark packet)) := by
  let i := probabilityWait packet terminal
  have hAddr : packetAddress l packet < 2 ^ 32 := by
    have := hp.shared.2.1
    fin_cases packet <;> dsimp [packetAddress] <;> omega
  have hAlign : packetAddress l packet % 8 = 0 := by
    have := hp.shared.1
    fin_cases packet <;> dsimp [packetAddress] <;> omega
  have hFresh : ∀ pair ∈ phaseFrame l q, pair.1 ≠ (waitSite i).result := by
    fin_cases packet <;> cases terminal <;>
      simp [i, phaseFrame, probabilityFrame, probabilityWait, waitSite, readyFrame]
  have hBase : ((waitSite i).base, b32 (packetAddress l packet)) ∈ phaseFrame l q := by
    fin_cases packet <;> cases terminal <;>
      simp [i, phaseFrame, probabilityFrame, probabilityWait, waitSite]
  have hPar : ((waitSite i).phase, b32 q) ∈ phaseFrame l q := by
    fin_cases packet <;> cases terminal <;>
      simp [i, phaseFrame, probabilityWait, waitSite]
  let ev := fun ok => Event.mk ((waitSite i).pc)
    (.wait ⟨.shared, g / l.block, packetAddress l packet⟩ q ok true .cta)
  have erase (n : Nat) : (List.replicate n (ev false)).filterMap (probabilityMark packet) = [] := by
    simp [probabilityMark, ev]
  have hMark : probabilityMark packet (ev true) = some q := by
    cases terminal <;> simp [probabilityMark, ev, i, probabilityPc]
  rcases waitWalk i hAddr hAlign hQ hFresh hBase hPar hs hw with ⟨n, hEq⟩ |
      ⟨n, rest, hEq, hTail⟩
  · change es = List.replicate n (ev false) at hEq
    rw [hEq, erase]
    exact .nil _
  · change es = List.replicate n (ev false) ++ ev true :: rest at hEq
    rw [hEq, List.filterMap_append, erase, List.nil_append, List.filterMap_cons, hMark]
    apply ProbabilityAlternates.cons
    rcases hTail with rfl | ⟨u, post, hL, hu, hw'⟩
    · exact .nil _
    · exact after hu hL hw'

private theorem roleExitNoProbabilities {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (packet : Fin 4) (hPc : s.pc = 3099)
    (hAt : At s s.pc [(1062, b32 12)]) (hWalk : Walk kernel Assumptions.all l g s es vs) :
    es.filterMap (probabilityMark packet) = [] := by
  have hEvents := mmaEpilogueExitEvents hPc hAt.2.2.2.1 (.inl rfl) hAt.2.2.2.2.1 hWalk
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  have h := hEvents e he
  obtain ⟨pc, kind⟩ := e
  dsimp only at h
  subst pc
  cases kind <;> try rfl
  case wait _ _ ok _ _ => cases ok <;> fin_cases packet <;> rfl

private theorem tailProbabilitySequence {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (packet : Fin 4) {g q : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hQ : q < 2) (hs : At s 2534 (phaseFrame l q))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ProbabilityAlternates q (es.filterMap (probabilityMark packet)) := by
  apply intervalSequence packet 6 (by rw [hs.1]; fin_cases packet <;> decide) ⟨rfl, hs.2⟩
    (by simp [phaseFrame, probabilityFrame, readyFrame])
    (by simp [phaseFrame, probabilityFrame, readyFrame, probabilityInterval, probabilityRegs]) hw
  intro t rest post hExit ht _ hWalk
  have hPc : t.pc = probabilityPc packet true := by simpa [probabilityInterval] using hExit
  apply probabilityPoll hp packet true hQ ⟨hPc, ht.2⟩ hWalk
  intro u final visits hu _ hf
  have hInside : (probabilityInterval packet 7).inside u.pc := by
    rw [hu.1]
    fin_cases packet <;> decide
  have hu' : At u u.pc [(1062, b32 12)] := by
    refine ⟨rfl, (hu.mono ?_).2⟩
    exact ⟨holds_mem hu.2.2.2.2 (by simp [phaseFrame, probabilityFrame, readyFrame]), trivial⟩
  apply intervalSequence packet 7 hInside hu' (by simp) (by simp) hf
  intro last out suffix hEnd hLast _ hSuffix
  have hLastPc : last.pc = 3099 := by simpa [probabilityInterval] using hEnd
  rw [roleExitNoProbabilities packet hLastPc hLast hSuffix]
  exact .nil _

private theorem steadyProbabilitySequence {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (packet : Fin 4) {g q : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hQ : q < 2) (hs : At s 2291 (phaseFrame l q))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ProbabilityAlternates q (es.filterMap (probabilityMark packet)) := by
  generalize hFuel : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing q s es vs with
  | h fuel ih =>
    apply intervalSequence packet 3 (by rw [hs.1]; fin_cases packet <;> decide) ⟨rfl, hs.2⟩
      (by simp [phaseFrame, probabilityFrame, readyFrame])
      (by simp [phaseFrame, probabilityFrame, readyFrame, probabilityInterval, probabilityRegs]) hw
    intro atPoll esPoll visitsPoll hPoll hpoll hLen₁ hWalk
    have hPollPc : atPoll.pc = probabilityPc packet false := by
      simpa [probabilityInterval] using hPoll
    apply probabilityPoll hp packet false hQ ⟨hPollPc, hpoll.2⟩ hWalk
    intro t es' visits' ht hLen₂ hw'
    have hStart : (probabilityInterval packet 4).inside t.pc := by
      rw [ht.1]
      fin_cases packet <;> decide
    apply intervalSequence packet 4 hStart ⟨rfl, ht.2⟩
      (by simp [phaseFrame, probabilityFrame, readyFrame])
      (by simp [phaseFrame, probabilityFrame, readyFrame, probabilityInterval, probabilityRegs]) hw'
    intro atToggle esToggle visitsToggle hToggle htog hLen₃ hWalkToggle
    have hTogglePc : atToggle.pc = 2529 := by simpa [probabilityInterval] using hToggle
    apply cutoffLocals (probabilityToggle l g q hQ) ⟨hTogglePc, htog.2⟩ hWalkToggle
    intro u visitsNext hu hLen₄ hWalkNext
    apply intervalSequence packet 5 (by rw [hu.1]; fin_cases packet <;> decide) ⟨rfl, hu.2⟩
      (by simp [phaseFrame, probabilityFrame, readyFrame])
      (by simp [phaseFrame, probabilityFrame, readyFrame, probabilityInterval, probabilityRegs])
      hWalkNext
    intro next rest post hExit hn hLen₅ hTail
    have hNext : next.pc = 2291 ∨ next.pc = 2534 := by simpa [probabilityInterval] using hExit
    have hBit : q ^^^ 1 < 2 := by interval_cases q <;> decide
    rcases hNext with h | h
    · exact ih post.length (by omega) hBit ⟨h, hn.2⟩ hTail rfl
    · exact tailProbabilitySequence hp packet hBit ⟨h, hn.2⟩ hTail

/-- Every actual MMA role prefix, including the terminal pair, has alternating successful
probability waits beginning at parity zero. -/
theorem probabilityAlternatesFromEntry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (packet : Fin 4) {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g s es vs) :
    ProbabilityAlternates 0 (es.filterMap (probabilityMark packet)) := by
  apply intervalSequence packet 0 (by rw [hs.1]; fin_cases packet <;> decide) ⟨rfl, hs.2⟩
    (by simp [readyFrame]) (by simp [readyFrame, probabilityInterval]) hw
  intro t rest post hExit ht _ hWalk
  have hNext : t.pc = 2275 ∨ t.pc = 2763 := by simpa [probabilityInterval] using hExit
  rcases hNext with hAddress | hBypass
  · apply cutoffLocals (probabilityAddresses hp g) ⟨hAddress, ht.2⟩ hWalk
    intro u visitsAdd hu _ hwAdd
    apply intervalSequence packet 1 (by rw [hu.1]; fin_cases packet <;> decide) ⟨rfl, hu.2⟩
      (by simp [probabilityFrame, readyFrame])
      (by simp [probabilityFrame, readyFrame, probabilityInterval, probabilityRegs]) hwAdd
    intro seed afterSeed visitsSeed hSeed hAtSeed _ hWalkSeed
    have hSeedPc : seed.pc = 2281 := by simpa [probabilityInterval] using hSeed
    apply cutoffLocals (probabilitySeed l g) ⟨hSeedPc, hAtSeed.2⟩ hWalkSeed
    intro v visitsEntry hv _ hWalkEntry
    apply intervalSequence packet 2 (by rw [hv.1]; fin_cases packet <;> decide) ⟨rfl, hv.2⟩
      (by simp [phaseFrame, probabilityFrame, readyFrame])
      (by simp [phaseFrame, probabilityFrame, readyFrame, probabilityInterval, probabilityRegs])
      hWalkEntry
    intro first body visitsBody hFirst hf _ hWalkBody
    have hFirstPc : first.pc = 2288 ∨ first.pc = 2534 := by
      simpa [probabilityInterval] using hFirst
    rcases hFirstPc with hSteady | hTail
    · apply cutoffLocals (probabilityReseed l g) ⟨hSteady, (hf.mono hf.2.2.2.2.2).2⟩ hWalkBody
      intro steady visitsSteady hAtSteady _ hWalkSteady
      exact steadyProbabilitySequence hp packet (by decide) hAtSteady hWalkSteady
    · exact tailProbabilitySequence hp packet (by decide) ⟨hTail, hf.2⟩ hWalkBody
  · have ht' : At t t.pc [(1062, b32 12)] := ht.mono (by
      refine ⟨holds_mem ht.2.2.2.2 (by simp [readyFrame]), trivial⟩)
    apply intervalSequence packet 8 (by rw [hBypass]; fin_cases packet <;> decide) ht'
      (by simp) (by simp) hWalk
    intro last out suffix hEnd hLast _ hSuffix
    have hLastPc : last.pc = 3099 := by simpa [probabilityInterval] using hEnd
    rw [roleExitNoProbabilities packet hLastPc hLast hSuffix]
    exact .nil _

end PTX.Kernels.TmlFa4Fwd.Mma
