-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.Objects
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Mma.Commit
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Lemmas.Flow.NotCommit
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow

private abbrev pcs := [2499,2546,2548,2553]

private theorem commit_pcs : OpPcsFast kernel.code commitOp pcs = true := by decide +kernel

private theorem commits (s : Site) : s.pc ∈ pcs → ∃ a : CommitSite, s = a.site := by
  cases s with
  | qkCommit => exact fun _ => ⟨.qk,rfl⟩
  | pvCommit1 => exact fun _ => ⟨.empty,rfl⟩
  | pvCommit2 => exact fun _ => ⟨.done,rfl⟩
  | finCommit => exact fun _ => ⟨.final,rfl⟩
  | qk j | pv j => fin_cases j <;> exact fun h => absurd h (by decide)
  | _ => exact fun h => absurd h (by decide)

private theorem commit_site {L m X g k pc sp} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩) : pc ∈ pcs := by
  obtain ⟨_,bad⟩ | ⟨t,ins,o,_,hc,fire⟩ := get_source hX he
  · contradiction
  apply OpPcsFast.mem commit_pcs hc
  cases h : commitOp ins.op
  · exact absurd rfl (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) fire sp)
  · rfl

private theorem region : ∀ r ∈ pcs, 2422 < r ∧ r < 2557 := by decide

/-- Every observed commit is issued by warp seven, even before a CTA exits. -/
public theorem commit_warp {Q L m X g k pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.commit sp)⟩) : g%L.block/32=7 := by
  have ⟨lo,hi⟩ := region _ (commit_site hX he)
  obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp) (by dsimp; omega) hi
    (by dsimp; omega)
  cases r with
  | mma => exact inv.1
  | loader =>
    have eq := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    change pc=d.site.pc at eq
    have bound (s : Loader.Site) : s.pc<2422 := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    have := bound d.site
    omega

/-- Each commit targets rank zero of the issuing CTA. The ready/empty slot counts use
the successful polls that the warp has already made on that half of the loop. -/
public theorem commit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) {g k pc : Nat} {sp : TcCommit.Spec} (hw : g % L.block / 32 = 7)
    (he : X.get (g,k) = some ⟨pc, .tc (.commit sp)⟩) :
    let es := (X.tr g).take k
    let c := g / L.block
    ∃ off, sp = ⟨.one, ⟨.shared,c,L.sharedBase + off⟩, 1, c, 1⟩ ∧
      ((pc = 2499 ∧ off = Iface.sReady ⟨(pollRound 2462 es - 1) % 2, by omega⟩) ∨
       (pc = 2546 ∧ off = Iface.kvEmpty ⟨(pollRound 2510 es - 1) % 3, by omega⟩) ∨
       (pc = 2548 ∧ off = Iface.oDone) ∨ (pc = 2553 ∧ off = Iface.oFinal)) := by
  have hpcs := commit_site hX he
  obtain ⟨w,x,⟨s,i,v⟩,t,ins,o,hat,_,hpc,hc,fire,hq,hp'⟩ :=
    mma_event hp hX hF hw he (fun _ => nofun) (region _ hpcs).1 (region _ hpcs).2
  change pc = s.pc at hpc
  obtain ⟨a,rfl⟩ := commits s (hpc ▸ hpcs)
  have hs := commit_shape hp (Frame.lt_of_get hX he) a hat hc fire
  have hspec := TcKind.commit.inj (Kind.tc.inj hs)
  refine ⟨a.offset i,hspec,?_⟩
  cases a with
  | qk =>
    change pollRound 2462 _ = i+1 at hq
    exact .inl ⟨hpc, by simp [CommitSite.offset, Iface.sReady, hq]⟩
  | empty =>
    change pollRound 2510 _ = i at hp'
    exact .inr (.inl ⟨hpc, by simp [CommitSite.offset, Iface.kvEmpty, hp']⟩)
  | done => exact .inr (.inr (.inl ⟨hpc,rfl⟩))
  | final => exact .inr (.inr (.inr ⟨hpc,rfl⟩))

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
