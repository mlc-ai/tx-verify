-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Loader.CopyShape
import Kernels.InklingRelDecode.Proof.Lib.IterRange

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k pc : Nat} {e : Event}

private def packet (s : Site) : Prop := s = .arrive ∨ ∃ p half, s = .copy p half

private theorem packet_pc (s : Site) :
    s.pc ∈ [2378,2389,2391,2394,2396,2404,2406,2410,2412] → packet s := by
  cases s with
  | arrive => exact fun _ => .inl rfl
  | copy p half => exact fun _ => .inr ⟨p,half,rfl⟩
  | page b => cases b <;> exact fun h => absurd h (by decide)
  | warpBar p | elect p => fin_cases p <;> exact fun h => absurd h (by decide)
  | _ => exact fun h => absurd h (by decide)

/-- The arrival and every issued packet use the slot of the last successful poll.
The transfer size counts bytes of the full descriptor box. -/
public theorem packet_credit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hw : g % L.block / 32 = 6) (he : X.get (g,k) = some e)
    (hpc : e.pc ∈ [2378,2389,2391,2394,2396,2404,2406,2410,2412])
    (hkind : (∃ obj tx n rel sc, e.kind = .arrive obj tx n rel sc) ∨
      (∃ addr sp, e.kind = .tensorIssue addr sp)) :
    let n := pollRound 2374 ((X.tr g).take k)
    let j := Iface.preloadCount Q L (g / L.block) + n - 1
    let obj := Iface.kvReadyLoc L (g / L.block) ⟨j % 3, by omega⟩
    0 < n ∧ ((e.pc = 2378 ∧ e.kind = .arrive obj 65536 1 true .cta) ∨
      ∃ sp, e.kind = .tensorIssue Q.kvMap sp ∧ sp.mbar = obj ∧
        TensorTransfer.bytes sp.descriptor = 8192) := by
  have hnu : ∀ f, e.kind ≠ .ub f := by
    rcases hkind with ⟨_,_,_,_,_,he⟩ | ⟨_,_,he⟩ <;> simp [he]
  have hb : ∀ r ∈ [2378,2389,2391,2394,2396,2404,2406,2410,2412], 2344 < r ∧ r < 2422 := by
    decide
  obtain ⟨w,x,⟨s,i,n,a,b⟩,t,ins,o,hat,hp',hc,fire,hr,hcount,_⟩ :=
    loader_event hp hX hf hw he hnu (hb _ hpc).1 (hb _ hpc).2
  change e.pc = s.pc at hp'
  have hpack := packet_pc s (hp' ▸ hpc)
  have hin : s.inLoop := by rcases hpack with rfl | ⟨p,u,rfl⟩ <;> rfl
  obtain ⟨j,hlo,hhi,rfl,_⟩ := ref_loop hr hin
  have hn := Lib.iter_range hp (Frame.lt_of_get hX he)
  change iterCount Q L (g / L.block) < 2^31 at hn
  have hj : (bits (b32 j)).toNat = j := by
    rw [bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hround : pollRound 2374 ((X.tr g).take k) =
      j - Iface.preloadCount Q L (g / L.block) + 1 := by
    rcases hpack with rfl | ⟨p,u,rfl⟩ <;> simpa only [polls, hj] using hcount
  dsimp only
  have hj' : Iface.preloadCount Q L (g / L.block) + pollRound 2374 ((X.tr g).take k) - 1 = j := by
    omega
  refine ⟨by omega, ?_⟩
  simp only [Iface.kvReadyLoc, Iface.kvReady, hj']
  rcases hpack with rfl | ⟨p,u,rfl⟩
  · left
    refine ⟨hp', ?_⟩
    simpa only [Iface.kvReadyLoc, Iface.kvReady, hj] using
      arrive_slot hp (by rw [hj]; omega) hat hc fire
  · rcases hkind with ⟨l,tx,c,rel,sc,h⟩ | ⟨addr,sp,h⟩
    · exfalso
      have hcode := copy_instr p u
      obtain ⟨guard,dst,coords,hins⟩ := hcode
      obtain rfl := Option.some.inj (hc.symm.trans hins)
      have hz : arrivesOn l e = false := arrivesOn_of_arriveOp (by rfl) fire
      simp [arrivesOn, sourceArrive, h] at hz
    · obtain ⟨rfl, hobj, hbytes⟩ :=
        copy_slot hp (by rw [hj]; omega) (by rfl) hat hc fire h
      exact .inr ⟨sp,h,by simpa only [Iface.kvReadyLoc, Iface.kvReady, hj] using hobj,hbytes⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
