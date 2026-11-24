-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.KvSlot
public import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Mem
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The loader warps' memory events

An event of a loader lane that accesses memory is a read of a scheduler word or of a page-table
entry, an access of the lane's local memory, a row copy, or a tensor copy (`ld_mem`). A row copy
(`LdCp`), with `N` earlier ones of its lane, is copy `(i, j)` of packet `N / 32`: it writes its
lane's column of block `(i, j)` of slot `N / 32 mod 3`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The packet of a lane's next row copy. -/
def pkt (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP cpCopy / 32

/-- A `cp.async` group commit. -/
def isAsyncCommit (e : Event) : Bool := match e.kind with | .asyncCommit => true | _ => false

/-- **A row copy**: its place in the packet, its bytes, and the polls and arrivals of the packet's
slot before it. -/
structure LdCp (L : Launch) (X : Execution) (g k : Nat) (sp : AsyncCopy.Spec) : Prop where
  dst : ∃ (i : Fin 16) (j : Fin 2), ((X.tr g).take k).countP cpCopy % 32 = 2 * i.val + j.val ∧
    sp.dst = { loc := ⟨.shared, g / L.block, Loader.cpAddr L g (pkt X g k % 3) i j⟩, size := 16 }
  src : sp.src.loc.space = .global
  grp : sp.completion = .asyncGroup
  gen : sp.generic = true
  whole : sp.writes = .whole
  /-- The `cp.async` commits before it: one per earlier packet. -/
  commits : ((X.tr g).take k).countP isAsyncCommit = pkt X g k
  polls : okPolls (obj L g (56 + 8 * (pkt X g k % 3))) ((X.tr g).take k) = pkt X g k / 3 + 1
  arrs : ((X.tr g).take k).countP
    (MbarRing.arriveOnTo (obj L g (32 + 8 * (pkt X g k % 3)))) = pkt X g k / 3

/-- **A footprint of the lane's local memory**, inside its 128 bytes. -/
def LocalAt (L : Launch) (g : Nat) (a : Acc) : Prop :=
  ∃ o, a.loc = ⟨.local, g, L.localBase + o⟩ ∧ o + a.size ≤ 128

private theorem ringCnt_div (c : Nat) : Loader.ringCnt c (c % 3) = c / 3 := by
  have h : ∀ n s, s < 3 → Loader.ringCnt n s = (n + 2 - s) / 3 := by
    intro n s hs
    induction n with
    | zero => simp [Loader.ringCnt]; omega
    | succ n ih => rw [Loader.ringCnt_succ, ih]; split <;> omega
  rw [h _ _ (Nat.mod_lt _ (by decide))]
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A row copy of a loader lane.** -/
theorem ld_cp (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {pc : Nat}
    {sp : AsyncCopy.Spec} (he : X.get (g, k) = some ⟨pc, .copy sp⟩) : LdCp L X g k sp := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  have hpoll := ld_copy_poll hp hX hFw hw he (c := pkt X g k) rfl
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_mem hev' hi.2 trivial).elim
  obtain ⟨a1, -, -, -⟩ := Loader.copy_site hev hub
  have hcpsite : d.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨per, v, i, j, hs⟩ : ∃ per v i j, d.site = .cp per v i j := by
    revert hcpsite
    cases d.site <;> simp [Loader.Site.isCp]
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, hC⟩ := hJl.refE
  have e1 := Loader.cp_count hp hX hg hw hσ h0
  obtain ⟨site, v', k2⟩ := d
  simp only at hs
  subst hs
  simp only [Loader.CpCount, Loader.inPkt] at e1
  have hi := i.isLt
  have hj := j.isLt
  have hN : ((X.tr g).take k).countP cpCopy = 32 * n (.load .commit) + (2 * i.val + j.val) := e1
  have hcc : n (.load .commit) = pkt X g k := by unfold pkt; omega
  have hcm : n (.load .commit) = Loader.pkOf per v kk := by
    have h1 := hC.commit
    simp only [Loader.arrAt, Loader.inPkt] at h1
    exact h1
  have hslot := Loader.cp_slot hp hRing
  simp only [Loader.Ev] at hev
  rcases hev with ⟨n', hk⟩ | ⟨f, hk⟩
  swap
  · cases hk
  simp only [Kind.copy.injEq] at hk
  subst hk
  refine ⟨⟨i, j, by omega, ?_⟩, rfl, rfl, rfl, rfl, ?_, hpoll, ?_⟩
  · simp only [Acc.mk.injEq, and_true]
    rw [← hcc, hcm, ← hslot]
    rfl
  · rw [← hcc]
    exact count hσ (.load .commit)
  · rw [arr_count hp hX hFw hw]
    have h1 := Loader.arr_ring hp hX hg hw hσ h0 ⟨pkt X g k % 3, Nat.mod_lt _ (by decide)⟩
    refine Eq.trans (count hσ (.load (.asyncArrive (obj L g (32 + 8 * (pkt X g k % 3)))))) ?_
    refine Eq.trans h1 ?_
    simp only [Loader.inPkt, Nat.sub_zero]
    change Loader.ringCnt (n (.load .commit) - 0) (pkt X g k % 3) = _
    rw [hcc]
    exact ringCnt_div _

set_option maxHeartbeats 4000000 in
/-- **The loader warps' memory events.** -/
theorem ld_mem (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {e : Event}
    (he : X.get (g, k) = some e) (hm : MemKind e.kind) :
    (∃ a bs, e.kind = .rd a bs ∧ (InWord p a ∨ LocalAt L g a)) ∨
      (∃ a bs, e.kind = .wr a bs ∧ LocalAt L g a) ∨
      (∃ sp, e.kind = .copy sp ∧ LdCp L X g k sp) ∨ ∃ a s, e.kind = .tensorIssue a s := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [h] at hm; exact hm
  have hno : ∀ kd, e.kind = kd → ¬ MemKind kd → False := fun kd h h' => h' (h ▸ hm)
  have hcp : ∀ sp, e.kind = .copy sp → LdCp L X g k sp := by
    intro sp hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    exact ld_cp hp hX hFw hw he
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_mem hev' hi.2 hm).elim
  have hF : Loader.LFits p L g d (n .shfl) (n .vote) (n (.load .commit)) := (hR.2 h0).2
  have hwr := (LdWarp.wr_ev hp hev).1
  have hloc : ∀ a bs, e.kind = .wr a bs → LocalAt L g a := by
    intro a bs hk
    obtain ⟨-, -, o, hl, h⟩ := hwr a bs hk
    exact ⟨o, hl, by omega⟩
  have hsched : ∀ {a bs}, Epilogue.Ev p L g (Loader.toE d) e → d.site.sched = true →
      e.kind = .rd a bs → InWord p a := fun h1 h2 h3 =>
    Epilogue.sched_rd hp (Loader.sched_fits h2 hF).2.1 h1 h3
  cases hs : d.site
  case word =>
    have hE := LdWarp.ev_toE (by rw [hs]; rfl) hev
    simp only [Loader.Ev, hs, Loader.Site.toE, Epilogue.Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, h⟩
    · exact .inl ⟨_, bs, hk, .inl (hsched hE (by rw [hs]; rfl) hk)⟩
    · exact (hub f h).elim
  case q0 | q1 =>
    have hE := LdWarp.ev_q (by simp [hs]) hev
    simp only [Loader.Ev, hs] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, h⟩
    · exact .inl ⟨_, bs, hk, .inl (hsched hE (by rw [hs]; rfl) hk)⟩
    · exact (hub f h).elim
  case uk =>
    unfold LFits at hF
    rw [show lc d.site = .req by rw [hs]; rfl] at hF
    obtain ⟨-, hFE, -⟩ := hF
    simp only [Epilogue.Fits, toE, hs, Site.epi] at hFE
    obtain ⟨R, bal, hC, -, -⟩ := hFE
    obtain ⟨site, v, k2⟩ := d
    simp only at hs
    subst hs
    simp only [Loader.Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, h⟩
    · have hx : Loader.rv p L g (Loader.wOf b) ⟨.uk, v, k2⟩ (reqRegs .uk).1 +
          BitVec.ofInt 64 (reqRegs .uk).2 = truncBits 64 (Epilogue.vbits
            (Epilogue.addrS p.usedKBase (Epilogue.chosen v.sc))) + BitVec.ofInt 64 0 := by
        simp [rv, reqRegs, valueOf, values, valuesReq, lookupLit, truncBits64]
      rw [hx] at hk
      exact .inl ⟨_, bs, hk, .inl (Epilogue.usedK_rd rfl (rfl : _ = Kind.rd _ bs)
        (Epilogue.usedK_addr hp hC))⟩
    · exact (hub f h).elim
  case pgLd per it =>
    obtain ⟨i, q, hi, hq, ha, -⟩ := LdWarp.pg_addr hp hF hs (wOf b)
    simp only [Loader.Ev, hs] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, h⟩
    · rw [ha] at hk
      exact .inl ⟨_, bs, hk, .inl ⟨rfl, .inr (.inr ⟨i, hi, q, hq, rfl⟩)⟩⟩
    · exact (hub f h).elim
  case ptP | ptR | lw =>
    obtain ⟨a, bs, o, q, hk, hz, hl, h, -⟩ := LdWarp.loc_read hp hev (by rw [hs]; rfl)
    exact .inl ⟨a, bs, hk, .inr ⟨o + q, by rw [hl, Nat.add_assoc], by omega⟩⟩
  all_goals simp only [Loader.Ev, hs] at hev
  case pgSt | rwSt | ptS =>
    rcases hev with ⟨v', -, hk⟩ | ⟨f, h⟩
    · exact .inr (.inl ⟨_, _, hk, hloc _ _ hk⟩)
    · exact (hub f h).elim
  case cp =>
    rcases hev with ⟨n', hk⟩ | ⟨f, h⟩
    · exact .inr (.inr (.inl ⟨_, hk, hcp _ hk⟩))
    · exact (hub f h).elim
  case tc =>
    rcases hev with ⟨a, s, hk, -⟩ | ⟨f, h⟩
    · exact .inr (.inr (.inr ⟨a, s, hk⟩))
    · exact (hub f h).elim
  case down | up | total | pre | tiles | xl | xh =>
    try simp only [Epilogue.Ev, Site.toE] at hev
    obtain ⟨_, _, h⟩ := hev
    exact (hno _ h id).elim
  case vote =>
    simp only [Epilogue.Ev, Site.toE] at hev
    obtain ⟨_, h⟩ := hev
    exact (hno _ h id).elim
  case setmax => obtain ⟨_, _, _, h⟩ := hev; exact (hno _ h id).elim
  case slot | tw | dw | dq => obtain ⟨_, h⟩ := hev; exact (hno _ h id).elim
  case te | de =>
    rcases hev with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  all_goals exact (hno _ hev id).elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
