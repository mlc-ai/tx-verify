-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base
public import Lemmas.Kernel.Progress.NextEv
import Kernels.InklingRelDecode.Proof.Common.NextState
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Softmax.Shape
import Kernels.InklingRelDecode.Proof.Epilogue.Shape
import Kernels.InklingRelDecode.Proof.Epilogue.Ledger
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll
import Lemmas.Flow.NotBulk

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Sched

private theorem next_pc {L m X g p l q ok a sc}
    (hn : NextEv L kernel Assumptions.all m X g ⟨p,.wait l q ok a sc⟩) : p ∈ Lib.pollSites := by
  obtain ⟨_,hy,_,he⟩ := hn
  exact (Lib.poll_site hy he).1

public theorem prologue_next {L m X g ev} (hn : NextEv L kernel Assumptions.all m X g ev)
    (lo : 27≤ev.pc) (hi : ev.pc<574) : ∀ l q ok a sc, ev.kind ≠ .wait l q ok a sc := by
  obtain ⟨p,k⟩ := ev
  rintro l q ok a sc rfl
  have hs := next_pc hn
  simp only [Lib.pollSites,List.mem_cons,List.not_mem_nil,or_false] at hs
  change 27≤p at lo; change p<574 at hi; omega

public theorem softmax_next {Q L m X g pc l q ok a sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨pc,.wait l q ok a sc⟩)
    (reg : (574≤pc ∧ pc<2331) ∨ (2560≤pc ∧ pc<2565)) :
    a=true ∧ sc=.cta ∧
    ((pc=1257 ∧ l=MbarRow.loc L g (Iface.sReady ⟨pollRound 1257 (X.tr g)%2,by omega⟩) ∧
      q=pollRound 1257 (X.tr g)/2%2) ∨
     (pc=2239 ∧ l=MbarRow.loc L g Iface.oDone ∧ q=pollRound 2239 (X.tr g)%2)) := by
  have sites := next_pc hn
  simp only [Lib.pollSites,List.mem_cons,List.not_mem_nil,or_false] at sites
  have pcs : pc=1257 ∨ pc=2239 := by omega
  obtain ⟨s,hs,inv,eq,t,ins,o,ht,hc,fire⟩ := next_state hp hf hn (fun _ => nofun)
  change pc=_ at eq
  obtain ⟨w,e,d,n,rfl⟩ := (eq ▸ state_role s).softmax (by omega) (by omega)
  change pc=d.site.pc at eq
  have ref : Softmax.Ref _ d (softCounts n) := inv.2
  have cnt (p) : n (.poll p) = pollRound p (X.tr g) := by
    simpa only [List.take_length,cls,pollRound] using fcount hs (.poll p)
  obtain ⟨s,i,v⟩ := d
  have shape := Softmax.object_shape hp ht (eq ▸ hc) (eq ▸ fire)
  change pc=s.pc at eq
  have only (s : Softmax.Site) : (s.pc=1257 → s=.waitS) ∧ (s.pc=2239 → s=.waitO) := by
    cases s <;> first | decide | (rename_i j; revert j; decide +kernel)
  rcases pcs with rfl|rfl
  · obtain rfl := (only s).1 eq.symm
    have ord := (cnt 1257).symm.trans (congrArg Softmax.Cnt.s ref.ledger)
    change pollRound 1257 (X.tr g)=i at ord
    obtain ⟨_,kind⟩ := shape
    obtain ⟨rfl,rfl,_,rfl,rfl⟩ := Kind.wait.inj kind
    exact ⟨rfl,rfl,.inl ⟨rfl,ord ▸ rfl,ord ▸ rfl⟩⟩
  · obtain rfl := (only s).2 eq.symm
    have ord := (cnt 2239).symm.trans (congrArg Softmax.Cnt.o ref.ledger)
    change pollRound 2239 (X.tr g)=i-1 at ord
    have pos : 0 < i := ref.oWait rfl
    obtain ⟨_,kind⟩ := shape
    obtain ⟨rfl,rfl,_,rfl,rfl⟩ := Kind.wait.inj kind
    exact ⟨rfl,rfl,.inr ⟨rfl,rfl,by omega⟩⟩

public theorem epilogue_next {Q L m X g pc l q ok a sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨pc,.wait l q ok a sc⟩) (lo : 2565≤pc) :
    pc=2565 ∧ l=MbarRow.loc L g Iface.oFinal ∧ q=0 ∧ a=true ∧ sc=.cta := by
  have sites := next_pc hn
  simp only [Lib.pollSites,List.mem_cons,List.not_mem_nil,or_false] at sites
  have pc0 : pc=2565 := by omega
  obtain ⟨s,_,inv,eq,t,ins,o,ht,hc,fire⟩ := next_state hp hf hn (fun _ => nofun)
  change pc=_ at eq
  obtain ⟨w,e,d,n,rfl⟩ := (eq ▸ state_role s).epilogue lo (by omega) inv.1
  obtain ⟨s,v⟩ := d
  change pc=s.pc at eq
  have wait : s=.wait := by
    by_contra ne
    exact Epilogue.final_only s ne (eq.symm.trans pc0)
  obtain ⟨_,kind⟩ := Epilogue.object_shape hp ht (eq ▸ hc) (eq ▸ fire) wait
  obtain ⟨rfl,rfl,_,rfl,rfl⟩ := Kind.wait.inj kind
  exact ⟨pc0,rfl,rfl,rfl,rfl⟩

/-- Complete classification of a data role's witnessed next event. The ordinary
branch covers arithmetic segments' next observable instruction; the final ret
is exposed separately for progress assembly. -/
public theorem data_next {Q L m X g e} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g e)
    (region : (27≤e.pc ∧ e.pc<2331) ∨ (2560≤e.pc ∧ e.pc<2856)) :
    ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit) ∨
    (e.pc=2855 ∧ e.kind=.exit) ∨
    (∃ ok, e.pc=1257 ∧ e.kind=.wait
      (MbarRow.loc L g (Iface.sReady ⟨pollRound 1257 (X.tr g)%2,by omega⟩))
      (pollRound 1257 (X.tr g)/2%2) ok true .cta) ∨
    (∃ ok, e.pc=2239 ∧ e.kind=.wait (MbarRow.loc L g Iface.oDone)
      (pollRound 2239 (X.tr g)%2) ok true .cta) ∨
    (∃ ok, e.pc=2565 ∧ e.kind=.wait (MbarRow.loc L g Iface.oFinal) 0 ok true .cta) := by
  obtain ⟨p,k⟩ := e
  change (27≤p ∧ p<2331) ∨ (2560≤p ∧ p<2856) at region
  cases k with
  | exit =>
    obtain ⟨_,hY,_,he⟩ := hn
    obtain ⟨_,bad⟩ | ⟨_,_,_,_,hc,fire⟩ := get_source hY he
    · cases bad
    exact .inr (.inl ⟨by simpa [Lib.retPcs] using Lib.ret_pc' hc fire rfl,rfl⟩)
  | wait l q ok a sc =>
    by_cases ep : 2565≤p
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := epilogue_next hp hf hn ep
      exact .inr (.inr (.inr (.inr ⟨_,rfl,rfl⟩)))
    by_cases pro : p<574
    · exact (prologue_next hn (by change 27≤p; omega) pro l q ok a sc rfl).elim
    obtain ⟨rfl,rfl,h⟩ := softmax_next hp hf hn (by omega)
    rcases h with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · exact .inr (.inr (.inl ⟨_,rfl,rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨_,rfl,rfl⟩)))
  | _ => exact .inl ⟨fun _ _ _ _ _ => nofun,nofun⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
