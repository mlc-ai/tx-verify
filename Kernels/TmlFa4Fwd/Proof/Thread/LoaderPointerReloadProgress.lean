-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderScratchReadProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerReload
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

section
variable {l : Launch} {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g pos base addr store : Nat} (hg : g < l.threads) (site : SavedPointerReload)
include hMax hg site

private theorem pointerHalfReadOfMaximal (word : Fin 2)
    (hCell : PrimingCellValue X g pos store (site.cell g addr) (b64 base).toBytes) {s u : TState}
    {ending : Option TState} {ret : List (Option Byte) → TState}
    (hn : Next kernel Assumptions.all l g s u (.read (site.word g addr word) ret))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some ⟨u.pc,.rd (site.word g addr word) (pointerReadBytes base word)⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1))
        (some (ret (pointerReadBytes base word))) ∧
      Run kernel Assumptions.all l g (ret (pointerReadBytes base word))
        ((X.tr g).drop (pos+1)) ending := by
  obtain ⟨write,hBefore,hStore,hLatest⟩ := hCell
  have hWord := word.isLt
  have addrAt (k : Nat) : (site.word g addr word).loc.at k =
      (site.cell g addr).loc.at (4*word.val+k) := by
    simp [SavedPointerReload.word,Loc.at,Nat.add_assoc]
  refine Step.local_read_of_maximal hMax hg rfl ⟨store,hStore⟩ hBefore
    (by simp [pointerReadBytes,SavedPointerReload.word]) ?_ ?_ ?_
    hn hPrefix hTail hBound hRelease (Assumptions.wf_snoc_nonGlobal hMax.1 (by
      simp [SavedPointerReload.word, SavedPointerReload.cell, Loc.at]))
  · intro k hk
    have hk₄ : k < 4 := hk
    have hb : 4*word.val+k < 8 := by omega
    have hLength : 4*word.val+k < (b64 base).toBytes.length := by
      simpa [b64,Value.toBytes,Value.bytes] using hb
    rw [addrAt]
    refine ⟨Acc.covers_at hb,?_⟩
    rw [wbyte,Loc.at,Nat.add_sub_cancel_left,List.getElem?_eq_getElem hLength]
    simp [pointerReadBytes,Value.toBytes,b64,hk₄]
  · intro k _ w d data hWrite hCover
    exact localWriteOwner hMax.1 hWrite rfl hCover
  · intro k hk j hj a hAccess hCover
    have hk₄ : k < 4 := hk
    exact hLatest (4*word.val+k) (by change 4*word.val+k < 8; omega) j hj a hAccess
      (addrAt k ▸ hCover)

/-- A maximal loader trace reloads both halves of its own last saved pointer. -/
theorem SavedPointerReload.readOfMaximal (hRange : 174 ≤ site.pc ∧ site.pc < 1906)
    (hCode : kernel.code[site.pc]? = some ⟨none,.mem site.mem⟩) (hAddr : addr+site.offset < 2^64)
    (hAlign : (addr+site.offset)%8 = 0) (hDistinct : site.lowReg ≠ site.highReg)
    (hBase : base < 2^64) {s t : TState} {F : List (Nat × Value)} {ending : Option TState}
    (hs : At s site.pc ((site.baseReg,b64 addr) :: F))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg)
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t s)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g)
    (hCell : PrimingCellValue X g pos store (site.cell g addr) (b64 base).toBytes) :
    ∃ u, At u (site.pc+1)
        ((site.lowReg,b32 (base%2^32)) :: (site.highReg,b32 (base/2^32)) :: F) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+2)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+2)) ending ∧
      X.get (g,pos) = some ⟨site.pc,.rd (site.word g addr 0) (pointerReadBytes base 0)⟩ ∧
      X.get (g,pos+1) = some ⟨site.pc,.rd (site.word g addr 1) (pointerReadBytes base 1)⟩ := by
  let rs := [site.lowReg,site.highReg]
  let lo := b32 (base%2^32)
  let hi := b32 (base/2^32)
  have hn₀ : Next kernel Assumptions.all l g t s
      (.read (site.word g addr 0) (afterLoad s rs)) :=
    ⟨hSteps,pointerReloadTemplate site hRange hCode hAddr hAlign 0 hs.1 hs.2.2.2.1
      hs.2.1 hs.2.2.2.2.1⟩
  obtain ⟨he₀,hPast₀,hTail₀⟩ := pointerHalfReadOfMaximal hMax hg site 0 hCell hn₀
    hPrefix hTail hBound hRelease
  have hLo : rebuild 3 (pointerReadBytes base 0) = .ok lo := by
    simpa [pointerReadBytes,lo,b64,b32,toNat_ofNat_lt hBase] using
      rebuild_b64_half (BitVec.ofNat 64 base) false
  let mid := {s with sub := 1, acc := [lo]}
  have hMid : afterLoad s rs (pointerReadBytes base 0) = mid := by
    rw [afterLoad_mid hLo (by simp [hs.2.1,rs])]
    simp [mid,hs.2.1,hs.2.2.1]
  rw [hMid] at hPast₀ hTail₀
  have hn₁ : Next kernel Assumptions.all l g mid mid
      (.read (site.word g addr 1) (afterLoad mid rs)) :=
    ⟨.refl,pointerReloadTemplate site hRange hCode hAddr hAlign 1 hs.1 hs.2.2.2.1
      rfl hs.2.2.2.2.1⟩
  have hCell' := hCell.step hMax.1 he₀ (by intro _ _ h; cases h)
  obtain ⟨he₁,hPast₁,hTail₁⟩ := pointerHalfReadOfMaximal hMax hg site 1 hCell' hn₁
    hPast₀ hTail₀ (len_of_get he₀) (releasedIfLast he₀ (by intro h; cases h))
  have hHi : rebuild 3 (pointerReadBytes base 1) = .ok hi := by
    have hH : base / 4294967296 < 4294967296 := by omega
    simpa [pointerReadBytes,hi,b64,b32,toNat_ofNat_lt hBase,Nat.mod_eq_of_lt hH] using
      rebuild_b64_half (BitVec.ofNat 64 base) true
  let u := next (setReg (setReg s site.lowReg lo) site.highReg hi)
  have hEnd : afterLoad mid rs (pointerReadBytes base 1) = u := by
    rw [afterLoad_last hHi (by simp [mid,rs])]
    simp [u,mid,next,setRegs,setReg,rs,hs.2.1,hs.2.2.1]
  rw [hEnd] at hPast₁ hTail₁
  have hFields : Holds u.regs F := by
    apply holdsSchedulerFrame (regs := F.map Prod.fst) hs.2.2.2.2.2
    · intro r hR
      obtain ⟨pair,hm,rfl⟩ := List.mem_map.mp hR
      have hN := hFresh pair hm
      simp [u,next,setReg,hN.1,hN.2]
    · intro pair hp
      exact List.mem_map_of_mem hp
  refine ⟨u,?_,hPast₁,hTail₁,hs.1 ▸ he₀,hs.1 ▸ he₁⟩
  simp [u,At,next,setReg,hs.1,hDistinct,hs.2.1,hs.2.2.1,hs.2.2.2.1,lo,hi]
  exact hFields
end

private theorem pointerReloadDrop {X : Execution} {g n : Nat} {e : Event}
    (he : X.get (g,n) = some e) : (X.tr g).drop n = e :: (X.tr g).drop (n+1) := by
  have h := List.getElem?_eq_some_iff.mp he
  rw [List.drop_eq_getElem_cons h.1,h.2]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes addr store : Nat}
    (hg : g < l.threads) (site : SavedPointerReload) (hRange : 174 ≤ site.pc ∧ site.pc < 1906)
    (hCode : kernel.code[site.pc]? = some ⟨none,.mem site.mem⟩) (hAddr : addr+site.offset < 2^64)
    (hAlign : (addr+site.offset)%8 = 0) (hDistinct : site.lowReg ≠ site.highReg) (bases : Nat → Nat)
    (hBase : ∀ lane < 32, bases lane < 2^64) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g site.pc F shuffles votes ends)
    (hLocal : ∀ lane < 32, (site.baseReg,b64 addr) ∈ F lane)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg)
    (hSaved : ∀ lane < 32,
      PrimingCellValue X (warpLane l g lane) (cur.pos lane) store
        (site.cell (warpLane l g lane) addr) (b64 (bases lane)).toBytes)
include hp hMax hg site hRange hCode hAddr hAlign hDistinct bases hBase cur hLocal hFresh hSaved

/-- Each lane's two exact pointer reads preserve the reached warp and its collective counts. -/
theorem SavedPointerReload.warpReadPreservingOfMaximal :
    let G := fun lane => (site.lowReg,b32 (bases lane%2^32)) ::
      (site.highReg,b32 (bases lane/2^32)) :: F lane
    ∃ done : SchedulerWarpReached l X g (site.pc+1) G shuffles votes ends,
      done.pos = (fun lane => cur.pos lane+2) ∧
      ∀ lane < 32,
        X.get (warpLane l g lane,cur.pos lane) = some
          ⟨site.pc,.rd (site.word (warpLane l g lane) addr 0) (pointerReadBytes (bases lane) 0)⟩ ∧
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
          PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data :=
  by
  dsimp only
  classical
  let thread := warpLane l g
  let stop := fun lane => cur.pos lane+2
  let G := fun lane => (site.lowReg,b32 (bases lane%2^32)) ::
    (site.highReg,b32 (bases lane/2^32)) :: F lane
  let es : Nat → List Event := fun lane =>
    [⟨site.pc,.rd (site.word (thread lane) addr 0) (pointerReadBytes (bases lane) 0)⟩,
     ⟨site.pc,.rd (site.word (thread lane) addr 1) (pointerReadBytes (bases lane) 1)⟩]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (thread lane)).drop (cur.pos lane) = es lane ++ (X.tr (thread lane)).drop (stop lane) ∧
      At u (site.pc+1) (G lane) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (stop lane)) (some u) ∧
      Run kernel Assumptions.all l (thread lane) u ((X.tr (thread lane)).drop (stop lane))
        (ends lane) ∧
      stop lane ≤ (X.tr (thread lane)).length ∧
      (stop lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (thread lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (thread lane) (stop lane) pc cell data := by
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := cur.checkpoint lane hl
    obtain ⟨u,hu,hPast,hTail,he₀,he₁⟩ := site.readOfMaximal hMax
      (g := thread lane) hActor hRange hCode hAddr hAlign hDistinct (hBase lane hl)
      (hs.mono ⟨holds_mem hs.2.2.2.2 (hLocal lane hl),hs.2.2.2.2⟩) (hFresh lane hl)
      (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.bounded lane hl) (cur.released lane hl) (hSaved lane hl)
    have hStop : stop lane = cur.pos lane+1+1 := by simp [stop,Nat.add_assoc]
    refine ⟨u,?_,hu,hPast,hTail,?_,?_,?_⟩
    · rw [pointerReloadDrop he₀,pointerReloadDrop he₁,hStop]
      rfl
    · rw [hStop]; exact len_of_get he₁
    · rw [hStop]; exact releasedIfLast he₁ (by intro h; cases h)
    · intro pc cell data he
      exact (he.step hMax.1 he₀ (by intro _ _ h; cases h)).step hMax.1 he₁
        (by intro _ _ h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hPreserve using hLane
  have hOrd := cur.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,rfl,?_⟩
  intro lane hl
  refine ⟨?_,hPreserve lane hl⟩
  change (X.tr (thread lane))[cur.pos lane]? = _
  rw [← Nat.add_zero (cur.pos lane),← List.getElem?_drop,hTrace lane hl]
  rfl

/-- Each lane reads the exact saved pointer while preserving the collective counts. -/
theorem SavedPointerReload.warpReadOfMaximal :
    let G := fun lane => (site.lowReg,b32 (bases lane%2^32)) ::
      (site.highReg,b32 (bases lane/2^32)) :: F lane
    ∃ _done : SchedulerWarpReached l X g (site.pc+1) G shuffles votes ends,
      ∀ lane < 32, X.get (warpLane l g lane,cur.pos lane) =
        some ⟨site.pc,.rd (site.word (warpLane l g lane) addr 0)
          (pointerReadBytes (bases lane) 0)⟩ := by
  dsimp only
  obtain ⟨done,_,hDone⟩ :=
    site.warpReadPreservingOfMaximal hp hMax hg hRange hCode hAddr hAlign hDistinct bases hBase
      cur hLocal hFresh hSaved
  exact ⟨done,fun lane hl => (hDone lane hl).1⟩

end PTX.Kernels.TmlFa4Fwd.Loader
