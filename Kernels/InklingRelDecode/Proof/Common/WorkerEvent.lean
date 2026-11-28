-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Common.StartupEvents
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

theorem reached_table (hf : Follow Q L X) (hg : g<L.threads) {s}
    (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some s)) : tableInv Q L g s :=
  (hf g hg k).2 _ hs (prefix_ub_zero hs nu)

/-- The state supplying any observed event strictly inside either worker routine. The
disjoint PCs remove startup and dispatch; the warp reference selects the called role. -/
theorem worker_occ (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (he : Occurs L X g k e) (hu : ∀ f, e.kind ≠ .ub f)
    (hlo : 2344 < e.pc) (hhi : e.pc < 2557) (hentry : e.pc ≠ 2422) :
    ∃ w x r d n, Frame.stateAt (thread Q L) X g k = some (some (workerState w x r d n)) ∧
      workerInv Q L g w x (.inr ⟨r,d⟩) n := by
  have hg := he.lt hX
  obtain ⟨s,hs,hpc,-⟩ := he.site hp hX hF hu
  have hi := (hF g hg k).2 s hs (prefix_ub_zero hs (he.noUb hX))
  obtain ⟨w,x,r,d,n,rfl⟩ := (hpc ▸ state_role s).worker hlo hhi hentry
  exact ⟨w,x,r,d,n,hs,hi.2⟩

theorem worker_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hlo : 2344 < e.pc) (hhi : e.pc < 2557) (hentry : e.pc ≠ 2422) :
    ∃ w x r d n, Frame.stateAt (thread Q L) X g k = some (some (workerState w x r d n)) ∧
      workerInv Q L g w x (.inr ⟨r,d⟩) n :=
  worker_occ hp hX hF (.inl he) hu hlo hhi hentry

theorem mma_occ (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (hg : g % L.block / 32 = 7) (he : Occurs L X g k e)
    (hu : ∀ f, e.kind ≠ .ub f) (hl : 2422 < e.pc) (hh : e.pc < 2557) :
    ∃ w x d t ins o, (Mma.code L g (dispatchRegs Q L g w x) w).AtD d t ∧
      Mma.Inv d ∧ e.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o ∧
      pollRound 2462 ((X.tr g).take k) = (Mma.polls d).1 ∧
      pollRound 2510 ((X.tr g).take k) = (Mma.polls d).2 := by
  obtain ⟨w,x,r,d,n,hs,hj⟩ := worker_occ hp hX hF he hu (by omega) hh (by omega)
  cases r with
  | loader =>
    have hw : g % L.block / 32 = 6 := hj.1
    omega
  | mma =>
    obtain ⟨_,_,hq,hp',-⟩ := hj
    obtain ⟨s',hs',-,t,ins,o,hat,hi,hc,hf⟩ := he.site hp hX hF hu
    obtain rfl : s' = workerState w x (.mma _) d n := Option.some.inj (Option.some.inj
      (hs'.symm.trans hs))
    exact ⟨w,x,d,t,ins,o,hat,hi.1,EventFrame.fires_source_pc hf,hc,hf,
      (fcount hs (.poll 2462)).symm.trans hq, (fcount hs (.poll 2510)).symm.trans hp'⟩

theorem mma_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (hg : g % L.block / 32 = 7) (he : X.get (g,k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (hl : 2422 < e.pc) (hh : e.pc < 2557) :
    ∃ w x d t ins o, (Mma.code L g (dispatchRegs Q L g w x) w).AtD d t ∧
      Mma.Inv d ∧ e.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o ∧
      pollRound 2462 ((X.tr g).take k) = (Mma.polls d).1 ∧
      pollRound 2510 ((X.tr g).take k) = (Mma.polls d).2 :=
  mma_occ hp hX hF hg (.inl he) hu hl hh

theorem loader_occ (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (hg : g % L.block / 32 = 6) (he : Occurs L X g k e)
    (hu : ∀ f, e.kind ≠ .ub f) (hl : 2344 < e.pc) (hh : e.pc < 2422) :
    ∃ w x d t ins o, (Loader.code L g w (Loader.inputs Q L g (dispatchRegs Q L g w x))).AtD d t ∧
      e.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o ∧
      Loader.Ref (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)) d ∧
      pollRound 2374 ((X.tr g).take k) =
        Loader.polls (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)) d ∧
      Loader.PageRef (Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x)) d := by
  obtain ⟨w,x,r,d,n,hs,hj⟩ := worker_occ hp hX hF he hu hl (by omega) (by omega)
  cases r with
  | mma =>
    have hw : g % L.block / 32 = 7 := hj.1
    omega
  | loader =>
    obtain ⟨_,hr,hq,pg,-⟩ := hj
    obtain ⟨s',hs',-,t,ins,o,ht,-,hc,hf⟩ := he.site hp hX hF hu
    obtain rfl : s' = workerState w x (.loader _) d n := Option.some.inj (Option.some.inj
      (hs'.symm.trans hs))
    exact ⟨w,x,d,t,ins,o,ht,EventFrame.fires_source_pc hf,hc,hf,hr,
      (fcount hs (.poll 2374)).symm.trans hq,pg⟩

theorem loader_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (hg : g % L.block / 32 = 6) (he : X.get (g,k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) (hl : 2344 < e.pc) (hh : e.pc < 2422) :
    ∃ w x d t ins o, (Loader.code L g w (Loader.inputs Q L g (dispatchRegs Q L g w x))).AtD d t ∧
      e.pc = d.site.pc ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o ∧
      Loader.Ref (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)) d ∧
      pollRound 2374 ((X.tr g).take k) =
        Loader.polls (Iface.preloadCount Q L (g / L.block)) (iterCount Q L (g / L.block)) d ∧
      Loader.PageRef (Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x)) d :=
  loader_occ hp hX hF hg (.inl he) hu hl hh

end PTX.Kernels.InklingRelDecode.Proof
