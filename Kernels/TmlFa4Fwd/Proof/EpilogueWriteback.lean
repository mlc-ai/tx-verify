-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWritebackControl
public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX Proof

noncomputable section

def writebackPc : Option WritebackSite → Nat
  | some (.ready stage) => pollPc stage
  | some (.store stage subbox) => storePc stage subbox
  | some (.commit stage) => commitPc stage
  | some (.readWait stage) => readWaitPc stage
  | some (.release stage) => freePc stage
  | none => 2986

/-- The ABI and selected tile operands preserved by the writeback. -/
def writebackEntry (p : Params) (l : Launch) (batch head tile : Nat) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1178, b32 (l.sharedBase + 68608)),
   (2390, b32 (l.sharedBase + 208)), (6497, b32 (l.sharedBase + 224)),
   (7229, b32 0), (7290, .ptr 64 false (.param (param 10)) 0),
   (2395, b32 (2 ^ 30 - p.qLength batch + 256 * tile)),
   (2393, b32 (p.qOffset (batch + 1))), (7227, b32 head)]

/-- Local register definitions, in program order. At any site exactly the indicated prefix
of these definitions has been executed. -/
def writebackDefinitions (p : Params) (l : Launch) (batch tile : Nat) : List (Nat × Value) :=
  [(7868, .ptr 64 true (.param (param 10)) 0), (7869, b64 0),
   (2396, b32 32), (2397, b32 64), (2398, b32 96),
   (2391, b32 (l.sharedBase + 216)),
   (2399, b32 (2 ^ 30 - p.qLength batch + stageRow tile 1)), (2400, b32 1)]

def writebackDefined : Option WritebackSite → Nat
  | some (.ready stage) => if stage = 0 then 0 else 6
  | some (.store stage subbox) => if stage = 0 then 2 + subbox.val else 7
  | some (.commit stage) => if stage = 0 then 5 else 7
  | some (.readWait stage) => if stage = 0 then 7 else 8
  | some (.release _) | none => 8

def writebackFacts (p : Params) (l : Launch) (batch head tile : Nat)
    (site : Option WritebackSite) : List (Nat × Value) :=
  writebackEntry p l batch head tile ++
    (writebackDefinitions p l batch tile).take (writebackDefined site)

def writebackWrites : List Nat :=
  [9748, 9749, 7868, 7869, 2396, 2397, 2398, 2391, 2399, 2400, 7870, 7871]

/-- Every active writeback site has a concrete Core event template. -/
def writebackTemplate (p : Params) (l : Launch) (g batch head tile : Nat)
    (site : WritebackSite) (t : TState) : Tmpl :=
  match site with
  | .ready stage => .wait (readyLoc l g stage) 0
      (fun ok => next (setReg t (readyReg stage) (.pred ok))) true .cta
  | .store stage subbox => .tensorStore p.oMapAddress
      (writebackStoreSpec p l g batch head tile stage subbox) (next t)
  | .commit _ => .bulkCommit (next t)
  | .readWait stage => .bulkWait .read (1 - stage.val) (next t)
  | .release stage => .arrive (writebackFreeLoc l g stage) 0
      (next (mbarStateDest t (some (7870 + stage.val)))) 1 true .cta

section
variable {p : Params} {l : Launch}

private theorem freeAddress {m : Mem0} (hpre : Pre p l m) (g : Nat) (t : TState) (stage : Fin 2)
    (hbase : t.regs 2535 = some (b32 l.sharedBase))
    (hfree : t.regs 6497 = some (b32 (l.sharedBase + 224))) :
    mbarLoc l g t (freeBase stage) (freeOffset stage) = .ok (writebackFreeLoc l g stage) := by
  have hLimit := hpre.shared.2.1
  have hAlign := hpre.shared.1
  have ha (n : Nat) (hn : n ≤ 232) : l.sharedBase + n < 2 ^ 32 := by omega
  have h8 (n : Nat) (hn : n % 8 = 0) : (l.sharedBase + n) % 8 = 0 := by omega
  have haddr (r base off : Nat) (hr : t.regs r = some (b32 base))
      (hb : base + off < 2 ^ 32) (hal : (base + off) % 8 = 0) :
      mbarLoc l g t r off = .ok ⟨.shared, g / l.block, base + off⟩ := by
    have h₁ : base < 2 ^ 32 := by omega
    have h₂ : base + off < 2 ^ 64 := by omega
    have hNat : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 base) + BitVec.ofNat 64 off)).toNat =
        base + off := by
      rw [truncBits_ofNat h₁ (by decide), ← BitVec.ofNat_add, truncBits_ofNat hb (by decide),
        toNat_ofNat_lt h₂]
    simp [mbarLoc, effAddr, sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind,
      pure, Except.pure, hNat, hal]
  fin_cases stage
  · exact haddr 6497 (l.sharedBase + 224) 0 hfree (by simpa using ha 224 (by decide))
      (by simpa using h8 224 (by decide))
  · exact haddr 2535 l.sharedBase 232 hbase (ha 232 (by decide)) (h8 232 (by decide))

/-- The register contract yields the actual output of the frozen instruction at every site. -/
theorem writebackOut {m : Mem0} (hpre : Pre p l m) (g : Nat) (site : WritebackSite) (t : TState)
    {batch head tile : Nat} (hb : batch < p.batch) (hh : head < p.heads)
    (htile : 256 * tile < p.qLength batch)
    (h : At t (writebackPc (some site)) (writebackFacts p l batch head tile (some site))) :
    out kernel [] l g t = .ev (writebackTemplate p l g batch head tile site t) := by
  have hEntry := (holds_append ..).1 h.2.2.2.2 |>.1
  have hbase : t.regs 2535 = some (b32 l.sharedBase) := holds_lookup hEntry rfl
  have hBuf : t.regs 1178 = some (b32 (l.sharedBase + 68608)) := holds_lookup hEntry rfl
  have hHead : t.regs 7227 = some (b32 head) := holds_lookup hEntry rfl
  have hEnd : t.regs 2393 = some (b32 (p.qOffset (batch + 1))) := holds_lookup hEntry rfl
  have hParity : t.regs 7229 = some (b32 0) := holds_lookup hEntry rfl
  have hf := h.2.2.2.1
  cases site with
  | ready stage =>
    have hReady : t.regs (readyBase stage) = some (b32 (readyLoc l g stage).addr) := by
      fin_cases stage <;> exact holds_lookup h.2.2.2.2 rfl
    exact readyPoll hpre g t stage h.1 hf hReady hParity
  | store stage subbox =>
    have hMap : t.regs 7868 = some (.ptr 64 true (.param (param 10)) 0) := by
      fin_cases stage <;> fin_cases subbox <;> exact holds_lookup h.2.2.2.2 rfl
    have hPolicy : t.regs 7869 = some (b64 0) := by
      fin_cases stage <;> fin_cases subbox <;> exact holds_lookup h.2.2.2.2 rfl
    have hRow : t.regs (rowReg stage) =
        some (b32 (2 ^ 30 - p.qLength batch + stageRow tile stage)) := by
      fin_cases stage <;> fin_cases subbox <;> exact holds_lookup h.2.2.2.2 rfl
    have hColumn : t.regs (columnReg subbox) = some (b32 (32 * subbox.val)) := by
      fin_cases stage <;> fin_cases subbox <;> exact holds_lookup h.2.2.2.2 rfl
    exact tileStore hpre g t stage subbox hb hh htile h.1 hf hMap hPolicy hbase hBuf hColumn hRow
      hHead hEnd
  | commit stage => exact commitTemplate stage l g t h.1 hf
  | readWait stage => exact readWaitTemplate stage l g t h.1 hf
  | release stage =>
    have hFree : t.regs 6497 = some (b32 (l.sharedBase + 224)) := holds_lookup hEntry rfl
    have hCount : t.regs 2400 = some (b32 1) := holds_lookup h.2.2.2.2 rfl
    apply freeTemplate stage l g t _ h.1 hf (freeAddress hpre g t stage hbase hFree)
    simp [readBits, readReg, hCount, b32, bind, Except.bind, pure, Except.pure]
    rfl

/-- The current tile's writeback does not change any register outside this write set. -/
def WritebackFrame (t u : TState) : Prop := ∀ r ∉ writebackWrites, u.regs r = t.regs r

private theorem frame_refl (t : TState) : WritebackFrame t t := fun _ _ => rfl

private theorem frame_trans {t u v : TState} (hu : WritebackFrame t u) (hv : WritebackFrame u v) :
    WritebackFrame t v := fun r hr => (hv r hr).trans (hu r hr)

private theorem frame_setReg (t : TState) (i : Nat) (v : Value) (hi : i ∈ writebackWrites) :
    WritebackFrame t (setReg t i v) := by
  intro r hr
  have hn : r ≠ i := fun he => hr (he ▸ hi)
  exact Function.update_of_ne hn _ _

private theorem holds_add_definition {t : TState} {F ds : List (Nat × Value)}
    {idx r : Nat} {v : Value} (h : Holds t.regs (F ++ ds.take idx))
    (hd : ds[idx]? = some (r, v)) (hf : ∀ x ∈ F ++ ds.take idx, x.1 ≠ r) :
    Holds (setReg t r v).regs (F ++ ds.take (idx + 1)) := by
  obtain ⟨hi, hGet⟩ := List.getElem?_eq_some_iff.mp hd
  rw [List.take_succ_eq_append_getElem hi, hGet, ← List.append_assoc, holds_append]
  exact ⟨holds_update h hf, Function.update_self .., trivial⟩

private def writebackKeys : List Nat :=
  [2535, 1178, 2390, 6497, 7229, 7290, 2395, 2393, 7227, 7868, 7869, 2396, 2397, 2398,
    2391, 2399, 2400]

private theorem keys_exact {b head tile : Nat} :
    (writebackEntry p l b head tile ++ writebackDefinitions p l b tile).map Prod.fst =
      writebackKeys := rfl

private theorem fresh_definition {b head tile idx r : Nat} {v : Value}
    (h : (writebackDefinitions p l b tile)[idx]? = some (r, v)) :
    ∀ x ∈ writebackEntry p l b head tile ++ (writebackDefinitions p l b tile).take idx,
      x.1 ≠ r := by
  intro x hx he
  have hn : List.Nodup ((writebackEntry p l b head tile ++ writebackDefinitions p l b tile).map
      Prod.fst) := by rw [keys_exact]; decide
  have hpart : (writebackEntry p l b head tile ++ writebackDefinitions p l b tile).map Prod.fst =
      (writebackEntry p l b head tile ++ (writebackDefinitions p l b tile).take idx).map Prod.fst ++
      ((writebackDefinitions p l b tile).drop idx).map Prod.fst := by
    simp only [← List.map_append, List.append_assoc, List.take_append_drop]
  rw [hpart] at hn
  have hm := List.mem_map_of_mem (f := Prod.fst) hx
  have hdrop : r ∈ ((writebackDefinitions p l b tile).drop idx).map Prod.fst := by
    apply List.mem_map_of_mem (f := Prod.fst) (a := (r, v))
    have hHead : ((writebackDefinitions p l b tile).drop idx)[0]? = some (r, v) := by
      simpa using h
    exact List.mem_of_getElem? hHead
  have hdrop' : x.1 ∈ ((writebackDefinitions p l b tile).drop idx).map Prod.fst := by
    rw [he]; exact hdrop
  exact (List.nodup_append.mp hn).2.2 x.1 hm x.1 hdrop' rfl

private theorem writebackFresh {b head tile r : Nat} {site : Option WritebackSite}
    (hn : r ∉ writebackKeys) :
    ∀ x ∈ writebackFacts p l b head tile site, x.1 ≠ r := by
  intro x hx he
  have hEnt : x ∈ writebackEntry p l b head tile ++ writebackDefinitions p l b tile := by
    rcases List.mem_append.mp hx with hE | hD
    · exact List.mem_append_left _ hE
    · exact List.mem_append_right _ (List.mem_of_mem_take hD)
  have hm := List.mem_map_of_mem (f := Prod.fst) hEnt
  rw [he, keys_exact] at hm
  exact hn hm

private theorem extendDefinition {batch head tile idx : Nat} {t : TState} {r : Nat} {v : Value}
    (h : Holds t.regs (writebackEntry p l batch head tile ++
      (writebackDefinitions p l batch tile).take idx))
    (hv : (writebackDefinitions p l batch tile)[idx]? = some (r, v)) :
    Holds (next (setReg t r v)).regs (writebackEntry p l batch head tile ++
      (writebackDefinitions p l batch tile).take (idx + 1)) :=
  holds_add_definition h hv (fresh_definition hv)

/-- Poll failure keeps the current site. All other events advance through the fixed writeback
sequence, interleaving both commits and both source-release waits. -/
def writebackSuccessor (site : WritebackSite) (ok : Bool) : Option WritebackSite :=
  match site with
  | .ready stage => if ok then some (.store stage 0) else some site
  | .store stage subbox => if hb : subbox.val < 3 then some
    (.store stage ⟨subbox.val + 1, by omega⟩)
      else some (.commit stage)
  | .commit stage => if stage = 0 then some (.ready 1) else some (.readWait 0)
  | .readWait stage => some (.release stage)
  | .release stage => if stage = 0 then some (.readWait 1) else none

private theorem pollStep {m : Mem0} (hpre : Pre p l m) (g : Nat) (t : TState) (stage : Fin 2)
    (ok : Bool) {batch head tile : Nat} (hb : batch < p.batch)
    (htile : 256 * tile < p.qLength batch)
    (h : At t (writebackPc (some (.ready stage)))
      (writebackFacts p l batch head tile (some (.ready stage)))) :
    ∃ v steps, run kernel [] l g steps (next (setReg t (readyReg stage) (.pred ok))) = some v ∧
      At v (writebackPc (writebackSuccessor (.ready stage) ok))
        (writebackFacts p l batch head tile (writebackSuccessor (.ready stage) ok)) ∧
      WritebackFrame t v := by
  let t₁ := next (setReg t (readyReg stage) (.pred ok))
  have hFresh : readyReg stage ∉ writebackKeys := by fin_cases stage <;> decide
  have hChange : readyReg stage ∈ writebackWrites := by fin_cases stage <;> decide
  have h₁ := h.set (r := readyReg stage) (v := .pred ok) (writebackFresh hFresh)
  have hHold : Holds t₁.regs (writebackFacts p l batch head tile (some (.ready stage))) :=
    h₁.2.2.2.2.2
  have hBranch := pollBranches stage ok l g t₁ h₁.1 h₁.2.2.2.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2.2.1
  have hFrame : WritebackFrame t t₁ := frame_setReg t _ _ hChange
  cases ok
  · let v := { t₁ with pc := pollPc stage }
    exact ⟨v, 2, hBranch, ⟨rfl, h.2.1, h.2.2.1, h.2.2.2.1, hHold⟩, hFrame⟩
  · let v := { t₁ with pc := pollPc stage + 3 }
    have hRun : run kernel [] l g 1 t₁ = some v := hBranch
    have hEntry : Holds v.regs (writebackEntry p l batch head tile) :=
      (holds_append ..).1 hHold |>.1
    fin_cases stage
    · let w := next (setReg v 7868 (.ptr 64 true (.param (param 10)) 0))
      let z := next (setReg w 7869 (b64 0))
      have hRaw : v.regs 7290 = some
        (.ptr 64 false (.param (param 10)) 0) := holds_lookup hEntry rfl
      have hPrep : run kernel [] l g 2 v = some z := prepareStore l g v rfl h.2.2.2.1 hRaw
      have hw : Holds w.regs (writebackEntry p l batch head tile ++
          (writebackDefinitions p l batch tile).take (0 + 1)) := extendDefinition hHold rfl
      have hz : Holds z.regs (writebackFacts p l batch head tile (some (.store 0 0))) :=
        extendDefinition hw rfl
      refine ⟨z, 3, run_comp hRun hPrep, ⟨rfl, h.2.1, h.2.2.1, h.2.2.2.1, hz⟩, ?_⟩
      exact frame_trans (frame_trans hFrame (frame_setReg v 7868 _ (by decide)))
        (frame_setReg w 7869 _ (by decide))
    · let z := next (setReg v 2399 (b32 (2 ^ 30 - p.qLength batch + stageRow tile 1)))
      have hRow : v.regs 2395 = some (b32 (2 ^ 30 - p.qLength batch + 256 * tile)) :=
        holds_lookup hEntry rfl
      have hTau : tauStep kernel [] l g v = some z :=
        prepareSecondRow hpre g v hb htile rfl h.2.2.2.1 hRow
      have hPrep : run kernel [] l g 1 v = some z := by simp only [run, hTau, Option.bind_some]
      have hz : Holds z.regs (writebackFacts p l batch head tile (some (.store 1 0))) :=
        extendDefinition hHold rfl
      refine ⟨z, 2, run_comp hRun hPrep, ⟨rfl, h.2.1, h.2.2.1, h.2.2.2.1, hz⟩, ?_⟩
      exact frame_trans hFrame (frame_setReg v 2399 _ (by decide))

private theorem nextColumnStep (g : Nat) (t : TState) (d : Fin 3) {batch head tile : Nat}
    (h : At t (writebackPc (some (.store 0 d.castSucc)))
      (writebackFacts p l batch head tile (some (.store 0 d.castSucc)))) :
    ∃ v, run kernel [] l g 1 (next t) = some v ∧
      At v (writebackPc (some (.store 0 d.succ)))
        (writebackFacts p l batch head tile (some (.store 0 d.succ))) ∧
      WritebackFrame t v := by
  let r := columnReg d.succ
  let v := next (setReg (next t) r (b32 (32 * d.succ.val)))
  have hp : (next t).pc = 2964 + 2 * d.val := by
    have hp := h.1
    change t.pc = (if (0 : Fin 2) = 0 then 2963 + 2 * d.val else 2976 + d.val) at hp
    simp only [↓reduceIte] at hp
    change t.pc + 1 = 2964 + 2 * d.val
    omega
  have ht : tauStep kernel [] l g (next t) = some v := prepareColumn d l g (next t) hp h.2.2.2.1
  have hidx : (writebackDefinitions p l batch tile)[2 + d.val]? =
      some (r, b32 (32 * d.succ.val)) := by fin_cases d <;> rfl
  have hNew : Holds v.regs (writebackFacts p l batch head tile (some (.store 0 d.succ))) :=
    extendDefinition (t := next t) h.2.2.2.2 hidx
  have hChange : r ∈ writebackWrites := by fin_cases d <;> decide
  have hpNew : v.pc = writebackPc (some (.store 0 d.succ)) := by
    change (next t).pc + 1 = storePc 0 d.succ
    fin_cases d <;> rw [hp] <;> rfl
  exact ⟨v, by simp only [run, ht, Option.bind_some],
    ⟨hpNew, h.2.1, h.2.2.1, h.2.2.2.1, hNew⟩, frame_setReg (next t) r _ hChange⟩

private theorem storeStep (g : Nat) (t : TState) (stage : Fin 2) (d : Fin 4) {batch head tile : Nat}
    (h : At t (writebackPc (some (.store stage d)))
      (writebackFacts p l batch head tile (some (.store stage d)))) :
    ∃ v steps, run kernel [] l g steps (next t) = some v ∧
      At v (writebackPc (writebackSuccessor (.store stage d) true))
        (writebackFacts p l batch head tile (writebackSuccessor (.store stage d) true)) ∧
      WritebackFrame t v := by
  fin_cases stage
  · by_cases hd : d.val < 3
    · let d' : Fin 3 := ⟨d.val, hd⟩
      have he : d'.castSucc = d := Fin.ext rfl
      have hNext : writebackSuccessor (.store 0 d) true = some (.store 0 d'.succ) := by
        simp [writebackSuccessor, hd, d', Fin.succ]
      change ∃ v steps, run kernel [] l g steps (next t) = some v ∧
        At v (writebackPc (writebackSuccessor (.store 0 d) true))
          (writebackFacts p l batch head tile (writebackSuccessor (.store 0 d) true)) ∧
        WritebackFrame t v
      rw [hNext]
      obtain ⟨v, hrun, hv, hframe⟩ := nextColumnStep (g := g) t d' (he.symm ▸ h)
      exact ⟨v, 1, hrun, hv, hframe⟩
    · have he : d = 3 := Fin.ext (by have := d.isLt; omega)
      subst d
      exact ⟨next t, 0, rfl, h.next, frame_refl t⟩
  · fin_cases d <;> exact ⟨next t, 0, rfl, h.next, frame_refl t⟩

private theorem commitStep {m : Mem0} (hpre : Pre p l m) (g : Nat) (t : TState) (stage : Fin 2)
    {batch head tile : Nat}
    (h : At t (writebackPc (some (.commit stage)))
      (writebackFacts p l batch head tile (some (.commit stage)))) :
    ∃ v steps, run kernel [] l g steps (next t) = some v ∧
      At v (writebackPc (writebackSuccessor (.commit stage) true))
        (writebackFacts p l batch head tile (writebackSuccessor (.commit stage) true)) ∧
      WritebackFrame t v := by
  fin_cases stage
  · let v := next (setReg (next t) 2391 (b32 (l.sharedBase + 216)))
    have hp : (next t).pc = 2971 := h.next.1
    have hBase : (next t).regs 2535 = some (b32 l.sharedBase) := holds_lookup h.2.2.2.2 rfl
    have ht : tauStep kernel [] l g (next t) = some v :=
      prepareSecondPoll hpre g (next t) hp h.2.2.2.1 hBase
    have hNew : Holds v.regs (writebackFacts p l batch head tile (some (.ready 1))) :=
      extendDefinition (t := next t) h.2.2.2.2 rfl
    have hp' : v.pc = 2972 := by change (next t).pc + 1 = 2972; rw [hp]
    exact ⟨v, 1, by simp only [run, ht, Option.bind_some],
      ⟨hp', h.2.1, h.2.2.1, h.2.2.2.1, hNew⟩, frame_setReg (next t) 2391 _ (by decide)⟩
  · exact ⟨next t, 0, rfl, h.next, frame_refl t⟩

private theorem readWaitStep (g : Nat) (t : TState) (stage : Fin 2) {batch head tile : Nat}
    (h : At t (writebackPc (some (.readWait stage)))
      (writebackFacts p l batch head tile (some (.readWait stage)))) :
    ∃ v steps, run kernel [] l g steps (next t) = some v ∧
      At v (writebackPc (writebackSuccessor (.readWait stage) true))
        (writebackFacts p l batch head tile (writebackSuccessor (.readWait stage) true)) ∧
      WritebackFrame t v := by
  fin_cases stage
  · let v := next (setReg (next t) 2400 (b32 1))
    have hp : (next t).pc = 2982 := h.next.1
    have ht : tauStep kernel [] l g (next t) = some v :=
      prepareReleaseCount l g (next t) hp h.2.2.2.1
    have hNew : Holds v.regs (writebackFacts p l batch head tile (some (.release 0))) :=
      extendDefinition (t := next t) h.2.2.2.2 rfl
    have hp' : v.pc = 2983 := by change (next t).pc + 1 = 2983; rw [hp]
    exact ⟨v, 1, by simp only [run, ht, Option.bind_some],
      ⟨hp', h.2.1, h.2.2.1, h.2.2.2.1, hNew⟩, frame_setReg (next t) 2400 _ (by decide)⟩
  · exact ⟨next t, 0, rfl, h.next, frame_refl t⟩

private theorem releaseStep (t : TState) (stage : Fin 2) {batch head tile : Nat}
    (h : At t (writebackPc (some (.release stage)))
      (writebackFacts p l batch head tile (some (.release stage)))) :
    let v := next (mbarStateDest t (some (7870 + stage.val)))
    At v (writebackPc (writebackSuccessor (.release stage) true))
      (writebackFacts p l batch head tile (writebackSuccessor (.release stage) true)) ∧
      WritebackFrame t v := by
  have hFresh : 7870 + stage.val ∉ writebackKeys := by fin_cases stage <;> decide
  have hChange : 7870 + stage.val ∈ writebackWrites := by fin_cases stage <;> decide
  have hNew : Holds (mbarStateDest t (some (7870 + stage.val))).regs
      (writebackFacts p l batch head tile (some (.release stage))) :=
    holds_update h.2.2.2.2 (writebackFresh hFresh)
  have hKeep : WritebackFrame t (mbarStateDest t (some (7870 + stage.val))) := by
    intro r hr
    have hn : r ≠ 7870 + stage.val := fun he => hr (he ▸ hChange)
    exact Function.update_of_ne hn _ _
  fin_cases stage <;> exact ⟨⟨h.next.1, h.2.1, h.2.2.1, h.2.2.2.1, hNew⟩, hKeep⟩

/-- Exact event kind at each writeback site. The only open result is the ready predicate. -/
def writebackKind (p : Params) (l : Launch) (g batch head tile : Nat)
    (site : WritebackSite) (ok : Bool) : Kind :=
  match site with
  | .ready stage => .wait (readyLoc l g stage) 0 ok true .cta
  | .store stage subbox => .tensorStore p.oMapAddress
      (writebackStoreSpec p l g batch head tile stage subbox)
  | .commit _ => .bulkCommit
  | .readWait stage => .bulkWait .read (1 - stage.val)
  | .release stage => .arrive (writebackFreeLoc l g stage) 0 1 true .cta

/-- After any actual firing, the output registers satisfy the next site contract. Failed polls
retry the same site and successful polls take the decoded branch. -/
theorem writebackStep {m : Mem0} (hpre : Pre p l m) (g : Nat) (site : WritebackSite) {t u : TState}
    {e : Event} {batch head tile : Nat} (hb : batch < p.batch)
    (htile : 256 * tile < p.qLength batch)
    (h : At t (writebackPc (some site)) (writebackFacts p l batch head tile (some site)))
    (hFire : Fires t.pc (writebackTemplate p l g batch head tile site t) e (some u)) :
    let ok := writebackSucceeded e.kind
    let result := writebackSuccessor site ok
    e = ⟨writebackPc (some site), writebackKind p l g batch head tile site ok⟩ ∧
      ∃ v steps, run kernel [] l g steps u = some v ∧
        At v (writebackPc result) (writebackFacts p l batch head tile result) ∧
        WritebackFrame t v ∧ (result = none → u = v) := by
  cases site with
  | ready stage =>
    obtain ⟨ok, rfl, hU⟩ := hFire
    obtain rfl := Option.some.inj hU
    obtain ⟨v, n, hr, hv, hf⟩ := pollStep hpre g t stage ok hb htile h
    exact ⟨by rw [h.1]; rfl, v, n, hr, hv, hf, by cases ok <;> simp [writebackSuccessor,
        writebackSucceeded]⟩
  | store stage box =>
    obtain ⟨rfl, hU⟩ := hFire
    obtain rfl := Option.some.inj hU
    obtain ⟨v, n, hr, hv, hf⟩ := storeStep g t stage box h
    refine ⟨by rw [h.1]; rfl, v, n, hr, hv, hf, ?_⟩
    simp only [writebackSuccessor]
    split <;> simp
  | commit stage =>
    obtain ⟨rfl, hU⟩ := hFire
    obtain rfl := Option.some.inj hU
    obtain ⟨v, n, hr, hv, hf⟩ := commitStep hpre g t stage h
    refine ⟨by rw [h.1]; rfl, v, n, hr, hv, hf, ?_⟩
    simp only [writebackSuccessor]
    split <;> simp
  | readWait stage =>
    obtain ⟨rfl, hU⟩ := hFire
    obtain rfl := Option.some.inj hU
    obtain ⟨v, n, hr, hv, hf⟩ := readWaitStep g t stage h
    exact ⟨by rw [h.1]; rfl, v, n, hr, hv, hf, by simp [writebackSuccessor]⟩
  | release stage =>
    obtain ⟨rfl, hU⟩ := hFire
    obtain rfl := Option.some.inj hU
    obtain ⟨hNext, hFrame⟩ := releaseStep t stage h
    exact ⟨by rw [h.1]; rfl, _, 0, rfl, hNext, hFrame, fun _ => rfl⟩

private theorem writebackContinues {g batch head tile : Nat} (site : WritebackSite) (t : TState)
    (e : Event) :
    ¬ Fires t.pc (writebackTemplate p l g batch head tile site t) e none := by
  cases site with
  | ready _ => rintro ⟨_, _, h⟩; cases h
  | store _ _ | commit _ | readWait _ | release _ => rintro ⟨_, h⟩; cases h

private theorem active_writeback_pc (s : WritebackSite) : WritebackPc (writebackPc (some s)) := by
  cases s with
  | store stage box => fin_cases stage <;> fin_cases box <;> decide
  | ready stage | commit stage | readWait stage | release stage => fin_cases stage <;> decide

private theorem continue_writeback_pc (s : WritebackSite) (ok : Bool)
    (h : writebackSuccessor s ok ≠ none) : WritebackPc (writebackPc (some s) + 1) := by
  cases s with
  | store stage box => fin_cases stage <;> fin_cases box <;> decide
  | ready stage | commit stage | readWait stage => fin_cases stage <;> decide
  | release stage =>
    fin_cases stage
    · decide
    · exact (h rfl).elim

private theorem writebackFiringPc {g batch head tile : Nat} (site : WritebackSite) {t u : TState}
    {e : Event} (hf : Fires t.pc (writebackTemplate p l g batch head tile site t) e (some u)) :
    u.pc = t.pc + 1 := by
  cases site with
  | ready stage =>
    obtain ⟨_, _, h⟩ := hf
    obtain rfl := Option.some.inj h
    rfl
  | store stage box => obtain ⟨_, h⟩ := hf; obtain rfl := Option.some.inj h; rfl
  | commit stage => obtain ⟨_, h⟩ := hf; obtain rfl := Option.some.inj h; rfl
  | readWait stage => obtain ⟨_, h⟩ := hf; obtain rfl := Option.some.inj h; rfl
  | release stage => obtain ⟨_, h⟩ := hf; obtain rfl := Option.some.inj h; rfl
end

/-- An event sequence of the output writeback, admitting repeated failed ready polls. -/
inductive WritebackTrace (p : Params) (l : Launch) (g batch head tile : Nat) :
    Option WritebackSite → List Event → Option WritebackSite → Prop where
  | nil (atSite : Option WritebackSite) : WritebackTrace p l g batch head tile atSite [] atSite
  | step {site : WritebackSite} {e : Event} {es : List Event} {last : Option WritebackSite}
      (he : e = ⟨writebackPc (some site),
        writebackKind p l g batch head tile site (writebackSucceeded e.kind)⟩)
      (hr : WritebackTrace p l g batch head tile
        (writebackSuccessor site (writebackSucceeded e.kind)) es last) :
      WritebackTrace p l g batch head tile (some site) (e :: es) last

variable {p : Params} {l : Launch}

/-- Invert the actual Core trace from any writeback checkpoint. On completion the remaining
Core trace starts at PC 2986 with every register outside the write set preserved. -/
theorem writebackRunOfOutEq {m : Mem0} {A : List Assumption} (hpre : Pre p l m) (g : Nat)
    (hModel : ∀ {s : TState}, WritebackPc s.pc → out kernel A l g s = out kernel [] l g s)
    {batch head tile : Nat} (hb : batch < p.batch) (hh : head < p.heads)
    (htile : 256 * tile < p.qLength batch) :
    ∀ (events : List Event) {a t : TState} {o : Option TState} (site : Option WritebackSite),
      Relation.ReflTransGen (Tau kernel A l g) a t → (site = none → a = t) →
      At t (writebackPc site) (writebackFacts p l batch head tile site) →
      Run kernel A l g a events o →
      ∃ written suffix last u, events = written ++ suffix ∧
        WritebackTrace p l g batch head tile site written last ∧
        At u (writebackPc last) (writebackFacts p l batch head tile last) ∧ WritebackFrame t u ∧
        (match last with
         | none => Run kernel A l g u suffix o
         | some _ => suffix = [] ∧ o.isSome) := by
  intro events
  induction events with
  | nil =>
    intro a t o site hl hsame ht hr
    cases site with
    | none =>
      have hr' : Run kernel A l g t [] o := hsame rfl ▸ hr
      exact ⟨[], [], none, t, rfl, .nil _, ht, frame_refl t, hr'⟩
    | some s =>
      cases hr
      exact ⟨[], [], some s, t, rfl, .nil _, ht, frame_refl t, rfl, rfl⟩
  | cons e rest ih =>
    intro a t o site hl hsame ht hr
    cases site with
    | none =>
      have hr' : Run kernel A l g t (e :: rest) o := hsame rfl ▸ hr
      exact ⟨[], e :: rest, none, t, rfl, .nil _, ht, frame_refl t, hr'⟩
    | some site =>
      have hn : Next kernel A l g a t (writebackTemplate p l g batch head tile site t) :=
        ⟨hl, (hModel (ht.1.symm ▸ active_writeback_pc site)).trans
          (writebackOut hpre g site t hb hh htile ht)⟩
      obtain ⟨v, hf, hs⟩ := hn.continuing_event (writebackContinues site t e) hr
      obtain ⟨he, w, n, hlocal, hw, hFrame, hEq⟩ := writebackStep hpre g site hb htile ht hf
      let nextSite := writebackSuccessor site (writebackSucceeded e.kind)
      have hLift : Relation.ReflTransGen (Tau kernel A l g) v w := by
        by_cases h : nextSite = none
        · rw [hEq h]
        · have hv : WritebackPc v.pc := by
            rw [writebackFiringPc site hf, ht.1]
            exact continue_writeback_pc site _ h
          exact writebackLiftLocal hModel hv (run_rtg hlocal)
      obtain ⟨pref, suf, last, u, hpref, ht', hu, hFrame', hd⟩ := ih nextSite hLift hEq hw hs
      exact ⟨e :: pref, suf, last, u, by rw [hpref]; rfl,
        .step he ht', hu, frame_trans hFrame hFrame', hd⟩

/-- The first wait starts the writeback trace. A complete writeback leaves the remaining run
at the exact exit contract, while an incomplete prefix stays at an active writeback site. -/
theorem writebackFromFirstPollOfOutEq {m : Mem0} {A : List Assumption} (hpre : Pre p l m) (g : Nat)
    (hModel : ∀ {s : TState}, WritebackPc s.pc → out kernel A l g s = out kernel [] l g s)
    {batch head tile : Nat} {t : TState} {events : List Event} {o : Option TState}
    (hb : batch < p.batch) (hh : head < p.heads) (htile : 256 * tile < p.qLength batch)
    (h : At t 2958 (writebackEntry p l batch head tile)) (hr : Run kernel A l g t events o) :
    ∃ written suffix last u, events = written ++ suffix ∧
      WritebackTrace p l g batch head tile (some (.ready 0)) written last ∧
      At u (writebackPc last) (writebackFacts p l batch head tile last) ∧ WritebackFrame t u ∧
      (match last with
         | none => Run kernel A l g u suffix o
         | some _ => suffix = [] ∧ o.isSome) := by
  have ht : At t (writebackPc (some (.ready 0)))
      (writebackFacts p l batch head tile (some (.ready 0))) := by
    simpa [writebackPc, pollPc, writebackFacts, writebackDefined] using h
  exact writebackRunOfOutEq hpre g hModel hb hh htile events (some (.ready 0)) .refl
    (fun _ => rfl) ht hr

/-- The writeback event sites, in issue order when unsuccessful ready polls are removed. -/
def writebackSites : List WritebackSite :=
  [.ready 0, .store 0 0, .store 0 1, .store 0 2, .store 0 3, .commit 0,
   .ready 1, .store 1 0, .store 1 1, .store 1 2, .store 1 3, .commit 1,
   .readWait 0, .release 0, .readWait 1, .release 1]

def writebackOrder : WritebackSite → Nat
  | .ready stage => 6 * stage.val
  | .store stage box => 6 * stage.val + 1 + box.val
  | .commit stage => 6 * stage.val + 5
  | .readWait stage => 12 + 2 * stage.val
  | .release stage => 13 + 2 * stage.val

/-- The successful writeback events remaining at a checkpoint. -/
def writebackRemaining (p : Params) (l : Launch) (g batch head tile : Nat) :
    Option WritebackSite → List Event
  | none => []
  | some site => (writebackSites.drop (writebackOrder site)).map fun s =>
      ⟨writebackPc (some s), writebackKind p l g batch head tile s true⟩

private theorem writebackRemaining_step (p : Params) (l : Launch) (g batch head tile : Nat)
    (site : WritebackSite) :
    writebackRemaining p l g batch head tile (some site) =
      ⟨writebackPc (some site), writebackKind p l g batch head tile site true⟩ ::
        writebackRemaining p l g batch head tile (writebackSuccessor site true) := by
  cases site with
  | store stage box => fin_cases stage <;> fin_cases box <;> rfl
  | ready stage | commit stage | readWait stage | release stage => fin_cases stage <;> rfl

/-- The successful prefix and remaining decoded events partition the writeback sequence. -/
theorem WritebackTrace.successfulPrefix {g batch head tile : Nat} {site last : Option WritebackSite}
    {events : List Event} (h : WritebackTrace p l g batch head tile site events last) :
    events.filter (fun e => writebackSucceeded e.kind) ++
      writebackRemaining p l g batch head tile last =
        writebackRemaining p l g batch head tile site := by
  induction h with
  | nil atSite => rfl
  | @step s e es last he next ih =>
    have hTail := ih
    cases hOk : writebackSucceeded e.kind with
    | true =>
      rw [hOk] at he hTail
      simp only [List.filter_cons, hOk, ↓reduceIte, List.cons_append, hTail]
      rw [writebackRemaining_step, he]
    | false =>
      have hReady : ∃ stage, s = .ready stage := by
        have he' := congrArg (fun ev : Event => writebackSucceeded ev.kind) he
        rw [hOk] at he'
        cases s with
        | ready stage => exact ⟨stage, rfl⟩
        | store stage box => exact False.elim (Bool.noConfusion he')
        | commit stage => exact False.elim (Bool.noConfusion he')
        | readWait stage => exact False.elim (Bool.noConfusion he')
        | release stage => exact False.elim (Bool.noConfusion he')
      obtain ⟨stage, rfl⟩ := hReady
      rw [hOk] at hTail
      simpa only [List.filter_cons, hOk, Bool.false_eq_true, ↓reduceIte, writebackSuccessor]
        using hTail

/-- Successful events of a completed writeback are exactly the two ready waits, the eight O
stores, the two commits, the two bulk read waits, and the two stage releases in issue order. -/
theorem WritebackTrace.successful {g batch head tile : Nat} {site last : Option WritebackSite}
    {events : List Event} (h : WritebackTrace p l g batch head tile site events last)
    (hLast : last = none) :
    events.filter (fun e => writebackSucceeded e.kind) =
      writebackRemaining p l g batch head tile site := by
  simpa only [hLast, writebackRemaining, List.append_nil] using h.successfulPrefix

/-- Each counted event consumes one slot of the finite writeback sequence. Failed polls
can appear in the trace without changing this budget. -/
theorem WritebackTrace.counted {g batch head tile : Nat} {site last : Option WritebackSite}
    {events : List Event} (h : WritebackTrace p l g batch head tile site events last) :
    events.countP Event.counts + (writebackRemaining p l g batch head tile last).length =
      (writebackRemaining p l g batch head tile site).length := by
  have he : Event.counts = fun e => writebackSucceeded e.kind := by
    funext ev
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> try rfl
    case wait m parity ok acquire scope => cases ok <;> rfl
  rw [he, List.countP_eq_length_filter]
  simpa only [List.length_append] using congrArg List.length h.successfulPrefix

/-- A terminated thread run from the first ready poll must have finished the writeback,
with all eight stores issued and all entry registers outside the write set retained. -/
theorem writebackTerminatedOfOutEq {m : Mem0} {A : List Assumption} (hpre : Pre p l m) (g : Nat)
    (hModel : ∀ {s : TState}, WritebackPc s.pc → out kernel A l g s = out kernel [] l g s)
    {batch head tile : Nat} {t : TState} {events : List Event} (hb : batch < p.batch)
    (hh : head < p.heads) (htile : 256 * tile < p.qLength batch)
    (h : At t 2958 (writebackEntry p l batch head tile)) (hr : Run kernel A l g t events none) :
    ∃ written suffix u, events = written ++ suffix ∧
      written.filter (fun e => writebackSucceeded e.kind) =
        writebackRemaining p l g batch head tile (some (.ready 0)) ∧
      At u 2986 (writebackFacts p l batch head tile none) ∧
      WritebackFrame t u ∧ Run kernel A l g u suffix none := by
  obtain ⟨written, suffix, last, u, hsplit, hTrace, hu, hFrame, hRest⟩ :=
    writebackFromFirstPollOfOutEq hpre g hModel hb hh htile h hr
  cases last with
  | some s => exact (Bool.noConfusion hRest.2)
  | none => exact ⟨written, suffix, u, hsplit, hTrace.successful rfl, hu, hFrame, hRest⟩

/-- The first-poll trace decomposition for the base instruction rules. -/
theorem writebackFromFirstPoll {m : Mem0} (hpre : Pre p l m) (g : Nat) {batch head tile : Nat}
    {t : TState} {events : List Event} {o : Option TState} (hb : batch < p.batch)
    (hh : head < p.heads) (htile : 256 * tile < p.qLength batch)
    (h : At t 2958 (writebackEntry p l batch head tile)) (hr : Run kernel [] l g t events o) :
    ∃ written suffix last u, events = written ++ suffix ∧
      WritebackTrace p l g batch head tile (some (.ready 0)) written last ∧
      At u (writebackPc last) (writebackFacts p l batch head tile last) ∧ WritebackFrame t u ∧
      (match last with
       | none => Run kernel [] l g u suffix o
       | some _ => suffix = [] ∧ o.isSome) :=
  writebackFromFirstPollOfOutEq hpre g (fun _ => rfl) hb hh htile h hr

/-- A terminated base-rule trace has issued all eight output stores. -/
theorem writebackTerminated {m : Mem0} (hpre : Pre p l m) (g : Nat) {batch head tile : Nat}
    {t : TState} {events : List Event} (hb : batch < p.batch) (hh : head < p.heads)
    (htile : 256 * tile < p.qLength batch) (h : At t 2958 (writebackEntry p l batch head tile))
    (hr : Run kernel [] l g t events none) :
    ∃ written suffix u, events = written ++ suffix ∧
      written.filter (fun e => writebackSucceeded e.kind) =
        writebackRemaining p l g batch head tile (some (.ready 0)) ∧
      At u 2986 (writebackFacts p l batch head tile none) ∧
      WritebackFrame t u ∧ Run kernel [] l g u suffix none :=
  writebackTerminatedOfOutEq hpre g (fun _ => rfl) hb hh htile h hr

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
