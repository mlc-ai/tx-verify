-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalBallot
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalBallot
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotCursor
import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

private theorem terminalBallotOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g n lane : Nat} {t : TState} (ht : At t 9194 [(769,.pred (decide (lane < n)))]) :
    out kernel Assumptions.all l g t = .ev (.vote (2^32-1) (decide (lane < n))
      (fun word => next (setReg t 7127 (b32 word.toNat)))) := by
  rw [RowDrainRole.correction.drainCore (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_9194) rfl rfl]
  change Out.ev (voteTmpl l g t 7127 769 false (.imm (-1))) = _
  have hb : l.block%32 = 0 := by rw [hp.block]
  simp [voteTmpl,readPred,readReg,ht.2.2.2.2.1,hb,b32,readBits,pure,Except.pure]
  rfl

private theorem terminalBallotCount (l : Launch) (g : Nat) {n : Nat} (hn : n < 31) :
    Seg kernel [] l g 2 9195 [(7127,b32 (2^n-1))] 9197
      [(770,.pred (decide (n = 0))),(1662,b32 n)] := by
  have hPow : 2^n < 2^32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hWord : 2^n-1 < 2^32 := by omega
  let word := BitVec.ofNat 32 (2^n-1)
  have hNat : word.toNat = 2^n-1 := by
    dsimp only [word]
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hWord]
  have hBits (i : Nat) (hi : i < 32) : word.getLsbD i = decide (i < n) := by
    dsimp only [word]
    rw [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]
    simp [hi]
  have hPop := ballot_popc_prefix (by omega : n ≤ 32) hBits
  rw [hNat] at hPop
  have hZero : 2^n-1 = 0 ↔ n = 0 := by
    constructor
    · intro h
      by_contra hn
      have hh : 2^0 < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
      change 1 < 2^n at hh
      omega
    · rintro rfl
      decide
  intro t ht
  seg_fp ht using
    (simp only [Value.pred.injEq,compare,b32,Option.getD_some,
       truncBits_ofNat hWord (by decide),toNat_ofNat_lt (show 2^n-1 < 2^64 by omega),
       show (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 from rfl,hPop,
       decide_eq_decide]
     all_goals omega)

private theorem terminalBeforeIndex {l : Launch} {g n prefixCount tiles : Nat}
    (hn : n < 31) {t : TState}
    (ht : At t 9195 ((7127,b32 (2^n-1))::
      terminalBallotCarry l prefixCount tiles)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if n = 0 then
        At u 9200 ((1662,b32 n)::terminalBallotCarry l prefixCount tiles)
      else At u 9199 [(7128,b32 (n-1)),(1662,b32 n),(7283,b32 prefixCount),(7282,b32 tiles),
        (7131,b32 (l.sharedBase+232)),(7287,b32 0)] := by
  let fixed := terminalBallotCarry l prefixCount tiles
  obtain ⟨v,hv,hV⟩ := (terminalBallotCount l g hn).apply (ht.mono
    ⟨ht.2.2.2.2.1,trivial⟩)
  have hSave : At t 9195 fixed := ht.mono ht.2.2.2.2.2
  obtain ⟨hLocal,hKeep⟩ := terminalLocalKeep hSave (by decide) (by decide)
    (by simp only [fixed,terminalBallotCarry,terminalFreeFrame,List.cons_append,
      List.nil_append,List.map]; decide +kernel) (by decide +kernel) hv
  have hBoth : At v 9197 ((770,.pred (decide (n=0)))::(1662,b32 n)::fixed) :=
    hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,hKeep⟩
  obtain ⟨s,hs,hS⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9197 (decide (n=0)) hBoth hBoth.2.2.2.2.1 (by simp)
  have hPath := hLocal.trans (RowDrainRole.correction.drainLocals (n := 1)
    (by decide) (by decide) hBoth.1 (by simp) hs)
  by_cases hz : n=0
  · have hPc : s.pc = 9200 := by simpa [hz] using hS.1
    exact ⟨s,hPath,by
      rw [ite_eq_left hz]
      exact ⟨hPc,hS.2.1,hS.2.2.1,hS.2.2.2.1,hS.2.2.2.2.2⟩⟩
  · have hPc : s.pc = 9198 := by simpa [hz] using hS.1
    have hS' : At s 9198 ((1662,b32 n)::fixed) :=
      ⟨hPc,hS.2.1,hS.2.2.1,hS.2.2.2.1,hS.2.2.2.2.2⟩
    have hPrev : Seg kernel [] l g 1 9198 [(1662,b32 n)] 9199 [(7128,b32 (n-1))] := by
      intro t ht
      seg_fp ht using norm_bits
    obtain ⟨u,hu,hU⟩ := hPrev.apply (hS'.mono ⟨hS'.2.2.2.2.1,trivial⟩)
    obtain ⟨hGo,hFixed⟩ := terminalLocalKeep hS' (by decide) (by decide)
      (by simp only [fixed,terminalBallotCarry,terminalFreeFrame,List.cons_append,
        List.nil_append,List.map]; decide +kernel) (by decide +kernel) hu
    exact ⟨u,hPath.trans hGo,by
      rw [ite_eq_right hz]
      exact hU.mono ⟨hU.2.2.2.2.1,hFixed⟩⟩

private theorem terminalIndexOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g sel value : Nat} (hSel : sel < 32) (previous : Bool) {t : TState}
    (ht : At t (if previous then 9199 else 9200)
      [((if previous then 7128 else 1662),b32 sel),
        ((if previous then 7283 else 7282),b32 value)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 value) sel 31
      (fun v _ => next (setReg t (if previous then 7129 else 7130) v))) := by
  have hSel32 : sel < 2^32 := by omega
  have hSel64 : sel < 2^64 := by omega
  have hCore := RowDrainRole.correction.drainCore (l := l) (g := g) (s := t)
    (by rw [ht.1]; cases previous <;> decide) (by rw [ht.1]; cases previous <;> decide)
  have hb : l.block%32 = 0 := by rw [hp.block]
  have hMask : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hBound : readBits l g t 32 (.imm 31) = .ok (BitVec.ofNat 64 31) := rfl
  rw [hCore]
  cases previous
  · have hPc : t.pc = 9200 := ht.1
    rw [out_event ht.2.2.2.1 (hPc.symm ▸ Flow.code_9200) rfl rfl]
    change Out.ev (shflTmpl l g t .idx 7130 none (.reg 7282)
      (.reg 1662) (.imm 31) (.imm (-1))) = _
    have hReg : t.regs 7282 = some (b32 value) := ht.2.2.2.2.2.1
    have hIdx : t.regs 1662 = some (b32 sel) := ht.2.2.2.2.1
    have hBits : readBits l g t 32 (.reg 1662) = .ok (BitVec.ofNat 64 sel) :=
      readBits_b32 hIdx hSel32
    simp only [shflTmpl,hReg,hb,hMask,hBound,hBits,readValue,readReg,
      toNat_ofNat_lt hSel64,pure,Except.pure]
    rfl
  · have hPc : t.pc = 9199 := ht.1
    rw [out_event ht.2.2.2.1 (hPc.symm ▸ Flow.code_9199) rfl rfl]
    change Out.ev (shflTmpl l g t .idx 7129 none (.reg 7283)
      (.reg 7128) (.imm 31) (.imm (-1))) = _
    have hReg : t.regs 7283 = some (b32 value) := ht.2.2.2.2.2.1
    have hIdx : t.regs 7128 = some (b32 sel) := ht.2.2.2.2.1
    have hBits : readBits l g t 32 (.reg 7128) = .ok (BitVec.ofNat 64 sel) :=
      readBits_b32 hIdx hSel32
    simp only [shflTmpl,hReg,hb,hMask,hBound,hBits,readValue,readReg,
      toNat_ofNat_lt hSel64,pure,Except.pure]
    rfl

/-- Execute the selected group's actual ballot, optional previous-prefix exchange, and final
request-size exchange, retaining the actual staging-free slot and parity. -/
theorem terminalIndexOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g n shuffles votes : Nat} (hg : g < l.threads) (hn : n < 31)
    (prefixCount tiles : Nat → Nat) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9194
      (fun lane => (769,.pred (decide (lane < n)))::
        terminalBallotCarry l (prefixCount lane) (tiles lane))
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 9201
      (fun _ => terminalFreeFrame l 0)
      (shuffles+(if n=0 then 1 else 2)) (votes+1) ends) := by
  let carry := fun lane => terminalBallotCarry l (prefixCount lane) (tiles lane)
  let selected := fun lane => (1662,b32 n)::carry lane
  obtain ⟨count⟩ := cur.consumePrefixBallot (dst := 7127) hp hMax hg (by omega : n ≤ 32) (by
      intro lane _ x hx
      simp only [terminalBallotCarry,terminalFreeFrame,List.cons_append,List.nil_append,
        List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    (fun lane hl => terminalBallotOut hp
      ((cur.checkpoint lane hl).mono ⟨(cur.checkpoint lane hl).2.2.2.2.1,trivial⟩))
  have consumeSelected {sh : Nat}
      (c : SchedulerWarpReached l X g 9200 selected sh (votes+1) ends) :
      Nonempty (SchedulerWarpReached l X g 9201
        (fun _ => terminalFreeFrame l 0) (sh+1) (votes+1) ends) := by
    obtain ⟨after⟩ := c.consumeShuffle (dst := 7130) hp hMax hg .idx
      (fun lane => b32 (tiles lane)) (fun _ => n) (fun _ => 31)
      (by
        intro lane _ x hx
        simp only [selected,carry,terminalBallotCarry,terminalFreeFrame,
          List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
      (fun lane hl => terminalIndexOut hp (by omega) false
        ((c.checkpoint lane hl).mono
          ⟨(c.checkpoint lane hl).2.2.2.2.1,(c.checkpoint lane hl).2.2.2.2.2.2.1,trivial⟩))
    apply after.advanceLocal
    intro lane hl
    have ht := after.checkpoint lane hl
    exact ⟨_,.refl,ht.mono ht.2.2.2.2.2.2.2.2⟩
  by_cases hz : n=0
  · obtain ⟨start⟩ := count.advanceLocal (pc' := 9200) (G := selected) (by
      intro lane hl
      obtain ⟨u,hu,hU⟩ := terminalBeforeIndex (g := warpLane l g lane) hn
        ((count.checkpoint lane hl).mono ⟨(count.checkpoint lane hl).2.2.2.2.1,
          (count.checkpoint lane hl).2.2.2.2.2.2⟩)
      rw [ite_eq_left hz] at hU
      exact ⟨u,hu,hU⟩)
    simpa only [hz,ite_true] using consumeSelected start
  · let previous := fun lane => (7128,b32 (n-1))::selected lane
    obtain ⟨start⟩ := count.advanceLocal (pc' := 9199) (G := previous) (by
      intro lane hl
      obtain ⟨u,hu,hU⟩ := terminalBeforeIndex (g := warpLane l g lane) hn
        ((count.checkpoint lane hl).mono ⟨(count.checkpoint lane hl).2.2.2.2.1,
          (count.checkpoint lane hl).2.2.2.2.2.2⟩)
      rw [ite_eq_right hz] at hU
      exact ⟨u,hu,hU⟩)
    obtain ⟨after⟩ := start.consumeShuffle (dst := 7129) hp hMax hg .idx
      (fun lane => b32 (prefixCount lane)) (fun _ => n-1) (fun _ => 31)
      (by
        intro lane _ x hx
        simp only [previous,selected,carry,terminalBallotCarry,terminalFreeFrame,
          List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
      (fun lane hl => terminalIndexOut hp (by omega) true
        ((start.checkpoint lane hl).mono
          ⟨(start.checkpoint lane hl).2.2.2.2.1,(start.checkpoint lane hl).2.2.2.2.2.2.1,trivial⟩))
    obtain ⟨middle⟩ := after.advanceLocal (pc' := 9200) (G := selected) (by
      intro lane hl
      have ht := after.checkpoint lane hl
      exact ⟨_,.refl,ht.mono ht.2.2.2.2.2.2⟩)
    simpa only [hz,ite_false] using consumeSelected middle

end PTX.Kernels.TmlFa4Fwd.Correction
