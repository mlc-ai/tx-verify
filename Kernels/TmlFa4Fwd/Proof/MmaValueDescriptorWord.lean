-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
public import Kernels.TmlFa4Fwd.Proof.MmaDescriptorStartup
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Lemmas.Flow.WarpScan
import Lemmas.Step.ExitLast
import Lemmas.Execution.ShapeExecution

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow

/-- The descriptor setup and broadcast are duplicated in the steady and tail control paths. -/
structure ValueDescriptorSite where
  prepare : Nat
  input : Nat
  output : Nat

def valueDescriptorSite : Bool → ValueDescriptorSite
  | true => ⟨2300, 2581, 2595⟩
  | false => ⟨2551, 2625, 2612⟩

/-- The probability setup uses a separate shuffle immediately before the value descriptor. -/
def valueProbabilityRegs : Bool → Nat × Nat
  | true => (2582,2569)
  | false => (2626,2611)

/-- Low bits of the V descriptor before the fragment stride is added. -/
def valueDescriptorLow (l : Launch) (use : Nat) : Nat := kvStart l use / 16 + 67108864

/-- The decoded local setup encodes the exact bank dictated by the actual ring slot register. -/
theorem valueDescriptorLocalWithProbabilityFrame {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (steady : Bool) (use : Nat) (warp : Option Value) :
    let site := valueDescriptorSite steady
    Seg kernel [] l g 7 site.prepare
      ([(7207, b32 (kvSlot use)), (2535, b32 l.sharedBase)] ++
        warp.toList.map (1062, ·))
      (site.prepare + 7) ([((valueProbabilityRegs steady).1,b32 64),
        (site.input, b32 (valueDescriptorLow l use))] ++ warp.toList.map (1062, ·)) := by
  dsimp only
  have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
  have hBound := hp.shared.2.1
  have hAlign := hp.shared.1
  have h0 : kvSlot use < 4294967296 := by omega
  have h1 : kvSlot use * 32768 < 4294967296 := by omega
  have h2 : l.sharedBase < 4294967296 := by omega
  have h3 : l.sharedBase + kvSlot use * 32768 < 4294967296 := by omega
  let start := l.sharedBase + kvSlot use * 32768 + 68608
  have h4 : l.sharedBase + kvSlot use * 32768 + 68608 < 4294967296 := by omega
  have h5 : (l.sharedBase + kvSlot use * 32768 + 68608) / 16 < 4294967296 := by omega
  have h6 : start / 16 < 2 ^ 26 := by dsimp [start]; omega
  have hMask := descriptorStart_mask (start := start) (by dsimp [start]; omega)
    (by dsimp [start]; omega)
  have hOr : start / 16 ||| 67108864 = start / 16 + 67108864 := by
    rw [Nat.or_comm, show (67108864 : Nat) = 2 ^ 26 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt h6, Nat.mul_one, Nat.add_comm]
  dsimp only [start] at hMask hOr
  have hStart : l.sharedBase + 68608 + 32768 * kvSlot use =
      l.sharedBase + kvSlot use * 32768 + 68608 := by omega
  cases steady <;> cases warp <;> intro t ht <;>
    simp only [valueDescriptorSite,valueProbabilityRegs,Option.toList,List.map,
      List.cons_append,List.nil_append]
      at ht ⊢ <;>
    seg_fp ht using
      (try unfold valueDescriptorLow kvStart
       nf_simp
       try simp only [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
         Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5, hMask, hOr, hStart])

/-- The decoded local setup encodes the exact bank dictated by the actual ring slot register. -/
theorem valueDescriptorLocalWithProbability {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (steady : Bool) (use : Nat) :
    let site := valueDescriptorSite steady
    Seg kernel [] l g 7 site.prepare
      [(7207, b32 (kvSlot use)), (2535, b32 l.sharedBase), (1062, b32 12)]
      (site.prepare + 7) [((valueProbabilityRegs steady).1,b32 64),
        (site.input, b32 (valueDescriptorLow l use)), (1062, b32 12)] :=
  valueDescriptorLocalWithProbabilityFrame hp g steady use (some (b32 12))

/-- The decoded setup preserves the physical V descriptor word. -/
theorem valueDescriptorLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (steady : Bool) (use : Nat) :
    let site := valueDescriptorSite steady
    Seg kernel [] l g 7 site.prepare
      [(7207, b32 (kvSlot use)), (2535, b32 l.sharedBase), (1062, b32 12)]
      (site.prepare + 7) [(site.input, b32 (valueDescriptorLow l use)), (1062, b32 12)] := by
  dsimp only
  intro t ht
  have hSeg := valueDescriptorLocalWithProbability hp g steady use
  dsimp only at hSeg
  obtain ⟨u,hRun,hu⟩ := hSeg t ht
  exact ⟨u,hRun,hu.mono hu.2.2.2.2.2⟩

/-- The preceding fixed probability-column shuffle does not change the V input register. -/
theorem valueProbabilityShuffle {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (steady : Bool) {g : Nat} {t : TState}
    (ht : At t ((valueDescriptorSite steady).prepare + 7)
      [((valueProbabilityRegs steady).1,b32 64)]) :
    out kernel Assumptions.all l g t =
      .ev (.shfl .idx (b32 64) 0 31
        (fun v _ => next (setReg t (valueProbabilityRegs steady).2 v))) := by
  let site := valueDescriptorSite steady
  let regs := valueProbabilityRegs steady
  have hCode : kernel.code[site.prepare + 7]? = some ⟨none,
      .warp ⟨.shfl .idx, some (.int .b 32), [some regs.2],
        [.reg regs.1, .imm 0, .imm 31], some (.imm (-1))⟩⟩ := by
    cases steady
    · exact Flow.code_2558
    · exact Flow.code_2307
  rw [out_eq_core (by rw [ht.1]; cases steady <;> decide)
      (by rw [ht.1]; cases steady <;> decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode) rfl rfl]
  change Out.ev (shflTmpl l g t .idx regs.2 none (.reg regs.1)
      (.imm 0) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRead : t.regs regs.1 = some (b32 64) := ht.2.2.2.2.1
  simp [shflTmpl, readValue, readReg, hRead, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

/-- The value descriptor broadcast is a full-mask lane-zero shuffle. -/
theorem valueDescriptorShuffle {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (steady : Bool) (use : Nat) {g : Nat} {t : TState}
    (ht : At t ((valueDescriptorSite steady).prepare + 8)
      [((valueDescriptorSite steady).input, b32 (valueDescriptorLow l use))]) :
    out kernel Assumptions.all l g t =
      .ev (.shfl .idx (b32 (valueDescriptorLow l use)) 0 31
        (fun v _ => next (setReg t (valueDescriptorSite steady).output v))) := by
  let site := valueDescriptorSite steady
  have hCode : kernel.code[site.prepare + 8]? = some ⟨none,
      .warp ⟨.shfl .idx, some (.int .b 32), [some site.output],
        [.reg site.input, .imm 0, .imm 31], some (.imm (-1))⟩⟩ := by
    cases steady
    · exact Flow.code_2559
    · exact Flow.code_2308
  rw [out_eq_core (by rw [ht.1]; cases steady <;> decide)
      (by rw [ht.1]; cases steady <;> decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode) rfl rfl]
  change Out.ev (shflTmpl l g t .idx site.output none (.reg site.input)
      (.imm 0) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hRead : t.regs site.input = some (b32 (valueDescriptorLow l use)) := ht.2.2.2.2.1
  simp [shflTmpl, readValue, readReg, hRead, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

/-- The actual indexed broadcast consumes its matched lane-zero descriptor word.
The matched send rules out the early-exit branch of the shuffle semantics. -/
theorem valueDescriptorReceivedFromPeer {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j ordinal pc sourcePc use : Nat} {sent received peerReceived : Value} {ok peerOk : Bool}
    (he : X.get (g,i) = some ⟨pc, .shfl .idx sent 0 31 received ok⟩)
    (hIndex : X.ShflK (g,i) ordinal)
    (hPeer : X.get (g-laneOf l g,j) =
      some ⟨sourcePc, .shfl .idx (b32 (valueDescriptorLow l use)) 0 31 peerReceived peerOk⟩)
    (hPeerIndex : X.ShflK (g-laneOf l g,j) ordinal) :
    received = b32 (valueDescriptorLow l use) := by
  let peer := g - laneOf l g
  have hPeerLt : peer < l.threads := event_thread_lt hX hPeer
  have hSource := shflSource_idx (laneOf l g) (show 0 < 32 by decide)
  have hequal : g - laneOf l g + (shflSource .idx (laneOf l g) 0 31).1 = peer := by
    simp [hSource, peer]
  have hLive : ¬ ShflExited X peer ordinal := by
    rintro ⟨k, exitPc, hx, hCount⟩
    have hLast := Execution.exit_last hX hPeerLt hx
    have hSize : j < (X.tr peer).length := (List.getElem?_eq_some_iff.mp hPeer).1
    have hj : j < k := by
      by_contra! hj
      have hEq : j = k := by omega
      subst k
      cases congrArg Event.kind (Option.some.inj (hPeer.symm.trans hx))
    let sentEvent := Event.mk sourcePc
      (.shfl .idx (b32 (valueDescriptorLow l use)) 0 31 peerReceived peerOk)
    have hTake : (X.tr peer).take (j+1) = (X.tr peer).take j ++ [sentEvent] := by
      change (X.tr peer)[j]? = some sentEvent at hPeer
      simp [List.take_add_one, hPeer]
    have hMono := countP_take_mono Execution.isShfl (X.tr peer) (show j+1 ≤ k by omega)
    rw [hTake, List.countP_append, hPeerIndex.2] at hMono
    simp [sentEvent, Execution.isShfl] at hMono
    omega
  exact (shfl_source_value hX he hIndex (by rwa [hequal]) (by rwa [hequal])
    (by rwa [hequal])).1

end PTX.Kernels.TmlFa4Fwd.Mma
