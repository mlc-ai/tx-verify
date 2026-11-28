-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Iface.CommitAfterPV
public import Kernels.InklingRelDecode.Proof.Mma.Export.Election
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC
import Kernels.InklingRelDecode.Proof.Common.Successor
import Kernels.InklingRelDecode.Proof.Mma.Facts.Final
import Kernels.InklingRelDecode.Proof.Mma.Commit
import Kernels.InklingRelDecode.Proof.Lib.Elect
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.NotBulk

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private theorem pv_site (s : Site) (pc : s.pc = 2546 ∨ s.pc = 2548) :
    s = .pvCommit1 ∨ s = .pvCommit2 := by
  cases s <;> first | exact .inl rfl | exact .inr rfl | exact absurd pc (by decide) |
    (rename_i i; fin_cases i <;> exact absurd pc (by decide))

private theorem exit_site {L m X g k pc} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k) = some ⟨pc,.exit⟩) : pc = 2855 := by
  obtain ⟨_,bad⟩ | ⟨_,_,_,_,hc,fire⟩ := get_source hX he
  · cases bad
  simpa [Lib.retPcs] using Lib.ret_pc' hc fire rfl

private theorem late_site (s : Site) (h : s.beforeFinal = true) :
    s.pc ≠ 2855 ∧ Lib.finalSync s.pc = false := by
  cases s <;> first | (exact absurd h (by decide)) | (constructor <;> decide) |
    (rename_i i; fin_cases i <;> (constructor <;> decide))

private theorem issue_site (s : Site) (h : s.pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
      2530,2533,2535,2537,2539,2541,2543,2545]) : s.beforeFinal = true := by
  cases s <;> first | rfl | exact absurd h (by decide)

/-- A lane of the MMA warp that wins its election and later reaches a final position (its
return, or its final rendezvous) has issued its final notification after every event of a
beforeFinal site. -/
private theorem later_core {Q L m X g k pc kd z pz kz} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,kd⟩) (nuk : ∀ f, kd ≠ .ub f) (rlo : 2422 < pc) (rhi : pc < 2557)
    (ne : pc ≠ 2553) (live : ∀ s : Site, s.pc = pc → s.beforeFinal = true)
    (won : Elected ((X.tr g).take k) (laneOf L g))
    (lastGet : X.get (g,z) = some ⟨pz,kz⟩) (nuz : ∀ f, kz ≠ .ub f) (hk : k ≤ z)
    (late : pz = 2855 ∨ Lib.finalSync pz = true) :
    ∃ j > k, ∃ sp', X.get (g,j) = some ⟨2553,.tc (.commit sp')⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨w,x,r,d,n,hs,hpc⟩ := mma_state hp hX hf he nuk rlo rhi
  change pc = d.site.pc at hpc
  have hv := live d.site hpc.symm
  have wins := Lib.electLead_of_elected hX (show Elected (X.tr g) (laneOf L g) from
    let ⟨ev,hev,ew⟩ := won
    ⟨ev,(List.take_sublist k _).subset hev,ew⟩)
  have hz : z < (X.tr g).length := (List.getElem?_eq_some_iff.mp lastGet).1
  have ordinary {j ev} (hj : j ≤ z) (get : X.get (g,j) = some ev) : ∀ f, ev.kind ≠ .ub f := by
    rcases hj.lt_or_eq with h | rfl
    · exact Frame.noUbBefore_of_get hX lastGet _ h _ get
    · obtain rfl := Option.some.inj (get.symm.trans lastGet)
      exact nuz
  by_contra! missing
  have alive (j : Nat) (lo : k ≤ j) (hi : j ≤ z) : ∃ s nm,
      stateAt (thread Q L) X g j = some (some (workerState w x (.mma r) s nm)) ∧
      s.site.beforeFinal = true := by
    induction j,lo using Nat.le_induction with
    | base => exact ⟨_,_,hs,hv⟩
    | succ j lo ih =>
      obtain ⟨s,nm,hst,live⟩ := ih (by omega)
      obtain ⟨ee,get⟩ : ∃ ev, X.get (g,j) = some ev :=
        ⟨_,List.getElem?_eq_getElem (by omega : j < (X.tr g).length)⟩
      have get' : ∃ ev, X.get (g,j+1) = some ev :=
        ⟨_,List.getElem?_eq_getElem (by omega : j+1 < (X.tr g).length)⟩
      obtain ⟨ev',nxt⟩ := get'
      have nf : s.site ≠ .finCommit := by
        rintro final
        obtain ⟨site,i,v⟩ := s
        change site = .finCommit at final
        subst site
        have pc' := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hst
          (ordinary (by omega) get)
        change ee.pc = 2553 at pc'
        have jl : k < j := by
          rcases lo.lt_or_eq with lt | rfl
          · exact lt
          · obtain rfl := Option.some.inj (get.symm.trans he)
            change pc = 2553 at pc'
            exact absurd pc' ne
        obtain ⟨t,ins,o,hat,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg)
          hX get hst (ordinary (by omega) get)
        have kind := commit_shape (regs := dispatchRegs Q L g w x) (w := w) (i := i) (v := v)
          hp hg .final hat hc fire
        have eq : ee = ⟨2553,.tc (.commit (CommitSite.final.spec L g i))⟩ := by
          cases ee
          congr 1
        exact missing j jl _ (eq ▸ get)
      obtain ⟨s',hn,keep⟩ := mma_successor hp hX hf hst get nxt (ordinary hi nxt)
      have live' := stays_before hn live nf (wins ee (List.mem_of_getElem? get))
      exact ⟨s',_,keep (fun h => by rw [h] at live'; cases live'),live'⟩
  obtain ⟨s,nm,hst,hbf⟩ := alive z hk le_rfl
  have pc' := Frame.event_pcU (fun g hg => thread_sound hp hg) hX lastGet hst nuz
  change pz = s.site.pc at pc'
  obtain ⟨no2855,nofin⟩ := late_site s.site hbf
  rcases late with h | h
  · exact no2855 (pc'.symm.trans h)
  · rw [pc'] at h
    rw [nofin] at h
    cases h

/-- In a CTA that exited, the winner of either selected PV commit also issues
its final notification. A finite prefix alone need not contain the final election. -/
private theorem later_of_exit {Q L m X g k pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩) (sel : pc = 2546 ∨ pc = 2548)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc,.exit⟩) :
    ∃ j > k, ∃ sp', X.get (g,j) = some ⟨2553,.tc (.commit sp')⟩ := by
  obtain ⟨pex,last⟩ := hex
  have lastGet : X.get (g,(X.tr g).length-1) = some ⟨pex,.exit⟩ := by
    change (X.tr g)[(X.tr g).length-1]? = _
    rwa [← List.getLast?_eq_getElem?]
  obtain rfl := exit_site hX lastGet
  have hl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨ev,hev,ew⟩ := elected hp hX hf he (fun _ => nofun)
    (by change pc ∈ _; rcases sel with rfl | rfl <;> decide)
  exact later_core hp hX hf he (fun _ => nofun) (by omega) (by omega) (by omega)
    (fun s h => by rcases pv_site s (h ▸ sel) with rfl | rfl <;> rfl) ⟨ev,hev,ew⟩ lastGet
    (fun _ => nofun) (by omega) (.inl rfl)

/-- **A lane that issued an MMA and reaches its final rendezvous issued its final
notification after it.** -/
public theorem later_of_sync {Q L m X g k pc dst s acc mask z pz} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (issue : pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
      2530,2533,2535,2537,2539,2541,2543,2545])
    (hz : X.get (g,z) = some ⟨pz,.bar 0 none .sync⟩) (hk : k ≤ z)
    (fin : Lib.finalSync pz = true) :
    ∃ j > k, ∃ sp', X.get (g,j) = some ⟨2553,.tc (.commit sp')⟩ := by
  have arith := issue
  simp only [List.mem_cons, List.not_mem_nil, or_false] at arith
  exact later_core hp hX hf he (fun _ => nofun) (by omega) (by omega) (by omega)
    (fun st h => issue_site st (h ▸ issue)) (elected_issue hp hX hf he issue) hz
    (fun _ => nofun) hk (.inr fin)

public theorem later_final {Q L m X g k pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩) (sel : pc = 2546 ∨ pc = 2548)
    (hex : CtaExited L X (g / L.block)) :
    ∃ j > k, ∃ sp', X.get (g,j) = some ⟨2553,.tc (.commit sp')⟩ :=
  later_of_exit hp hX hf he sel (hex g (Frame.lt_of_get hX he) rfl)

public theorem commitAfterPV {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    Iface.CommitAfterPV L X := by
  intro hc g k pc sp he sel
  rcases hc.1 g (Frame.lt_of_get hX he) with h | hx
  · have hm := List.mem_of_getElem? he
    rw [h.1] at hm
    cases hm
  · exact later_of_exit hp hX hf he sel hx

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
