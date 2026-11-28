-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Export.RegLedger
import Kernels.InklingRelDecode.Proof.Protocol.Bar.One
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Lib.RegSchedule
import Lemmas.Step.CtaBarNamed
import Lemmas.Kernel.Frame

@[expose] public section

/-! # ERR-SETMAXNREG: every register request is legal

The four clauses of `SetMaxNReg.UnsafeAt`. Direction: every request is `inc 256` or `dec 24`
(`Lib.requestAt_cases`), so none is against the previous count. Warpgroup: the CTA has 256
threads. Agreement: the default partition's requests are `inc 256`, and a worker's request is
fixed by its ordinal (`Lib.worker_class`, from the ledger of `Export.ledger_event`). Order: a
request that is not the loop head's follows one or two barrier-1 events, and every thread of its
warpgroup has made the previous request before its arrival of the last of them
(`Protocol.Bar.one_baseCausality`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem fold_val : ∀ (l : List Event) (old : Option Nat),
    (∀ ev ∈ l, ∀ inc n inst, ev.kind = .setMaxReg inc n inst → n = 24 ∨ n = 256) →
    (∀ w, old = some w → w = 24 ∨ w = 256) → ∀ v,
    l.foldl (fun old ev => match ev.kind with | .setMaxReg _ n _ => some n | _ => old) old
      = some v → v = 24 ∨ v = 256
  | [], old, _, ok, v, h => ok v h
  | ev :: rest, old, all, ok, v, h => by
    simp only [List.foldl_cons] at h
    refine fold_val rest _ (fun e mem => all e (List.mem_cons_of_mem _ mem)) (fun w hw => ?_) v h
    obtain ⟨pc,k⟩ := ev
    cases k <;> simp only at hw
    · exact all _ (List.mem_cons_self ..) _ _ _ rfl |>.imp (fun h => by simp_all)
        (fun h => by simp_all)
    all_goals exact ok w hw

private theorem prior_val (hX : Consistent L kernel Assumptions.all m X) {e : EvId} {v : Nat}
    (h : SetMaxNReg.prior X e = some v) : v = 24 ∨ v = 256 := by
  unfold SetMaxNReg.prior at h
  refine fold_val _ none ?_ (by simp) v h
  intro ev mem inc n inst kind
  obtain ⟨j,get⟩ := List.mem_iff_getElem?.mp ((List.take_sublist _ _).subset mem)
  obtain ⟨pc,k⟩ := ev
  change k = _ at kind
  subst kind
  have := Export.request_value hX (g := e.1) (k := j) get
  rcases Lib.requestAt_cases this with ⟨-,h⟩ | ⟨-,h⟩ <;> simp [h]

private theorem arrival_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h k r : Nat} (hr : r < ((X.tr h).take k).countP (Execution.isBarId 1)) :
    ∃ j pc, j < k ∧ X.IsBarrier (h,j) 1 none pc ∧
      ((X.tr h).take j).countP (Execution.isBarId 1) = r := by
  obtain ⟨j,e,hj,hq,hcnt⟩ := NamedBar.exists_ordinal (Execution.isBarId 1) _ hr
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjk
    obtain ⟨pc,cnt,md,rfl⟩ := NamedBar.isBarId_form hq
    rw [List.take_take,Nat.min_eq_left (by omega)] at hcnt
    have hget : X.get (h,j) = some ⟨pc,.bar 1 cnt md⟩ := hj
    obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block hget
    exact ⟨j,pc,hjk,hget,hcnt⟩
  · cases hj

/-- **ERR-SETMAXNREG**: no register request is illegal. -/
theorem Safe.noRegister (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : ¬ SetMaxNReg.UnsafeAt Assumptions.all L X := by
  have hb : L.block = 256 := hp.block
  have words : RoleBytes L X := fun he => Protocol.Shared.role_bytes hp hX he
  rintro ⟨⟨g,k⟩,pc,inc,n,inst,req,c1 | c2 | c3 | c4⟩
  · obtain ⟨v,hv,lt⟩ := c1
    have val := Export.request_value hX req
    have pv := prior_val hX hv
    rcases Lib.requestAt_cases val with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp at lt <;> omega
  · simp only [hb] at c2
    omega
  · obtain ⟨⟨h,j⟩,pc',inc',n',inst',sg,req',ord,ne⟩ := c3
    have l1 := Export.ledger_event hp hX words req (fun _ => nofun)
    have l2 := Export.ledger_event hp hX words req' (fun _ => nofun)
    have g1 := Export.request_group hp hX hf words req
    have g2 := Export.request_group hp hX hf words req'
    have v1 := Export.request_value hX req
    have v2 := Export.request_value hX req'
    have grp : g % L.block / 128 = h % L.block / 128 := sg.2
    have eqn : ((X.tr g).take k).countP SetMaxNReg.isRequest =
        ((X.tr h).take j).countP SetMaxNReg.isRequest := ord
    rw [hb] at grp
    have same : Lib.requestSched pc = Lib.requestSched pc' := by
      rcases g1 with ⟨a1,d1⟩ | ⟨a1,d1⟩ <;> rcases g2 with ⟨a2,d2⟩ | ⟨a2,d2⟩
      · rw [Lib.dataReq_sched d1,Lib.dataReq_sched d2]
      · rw [hb] at a1 a2; omega
      · rw [hb] at a1 a2; omega
      · rw [eqn] at l1
        exact Lib.worker_class d1 d2 l1 l2
    rw [Lib.requestAt_sched (by rcases g1 with ⟨_,d⟩ | ⟨_,d⟩ <;> first
      | exact Lib.dataReq_mem d | exact Lib.workerReq_mem d)] at v1
    rw [Lib.requestAt_sched (by rcases g2 with ⟨_,d⟩ | ⟨_,d⟩ <;> first
      | exact Lib.dataReq_mem d | exact Lib.workerReq_mem d)] at v2
    rw [same] at v1
    have both := (Option.some.inj v1).symm.trans (Option.some.inj v2)
    simp only [Prod.mk.injEq] at both
    rcases ne with ne | ne
    · exact ne both.1
    · exact ne both.2
  · obtain ⟨exempt,pos,hall⟩ := c4
    apply hall
    have hne : pc ≠ 2337 := fun h => Lib.head_exempt (h ▸ exempt)
    have led := Export.ledger_event hp hX words req (fun _ => nofun)
    have mem : pc ∈ Lib.requestPcs := by
      rcases Export.request_group hp hX hf words req with ⟨_,d⟩ | ⟨_,d⟩
      exacts [Lib.dataReq_mem d,Lib.workerReq_mem d]
    have posr : 0 < ((X.tr g).take k).countP SetMaxNReg.isRequest := pos
    have shape := Lib.ledger_request led mem hne posr
    have klen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp req).1
    set c := ((X.tr g).take k).countP (Execution.isBarId 1) with hc
    set r := ((X.tr g).take k).countP SetMaxNReg.isRequest with hr
    obtain ⟨i,pci,hik,hbg,hgi⟩ := arrival_before hp hX (h := g) (k := k) (r := c-1) (by omega)
    have hpass : i + 1 < (X.tr g).length := by omega
    intro h hh sg
    have hcta : h / L.block = g / L.block := sg.1.2.2.symm
    have exited : (∃ j pcx, X.get (h,j) = some ⟨pcx,.exit⟩) →
        ∃ i' pc', X.IsBarrier (h,i') 1 none pc' ∧ ((X.tr h).take i').countP (Execution.isBarId 1) =
          ((X.tr g).take i).countP (Execution.isBarId 1) := by
      rintro ⟨j',pcx,hex⟩
      have three := Export.exit_barriers hp hX words hex
      obtain ⟨i',pc',-,hb',hc'⟩ := arrival_before hp hX (h := h) (k := j') (r := c-1) (by omega)
      exact ⟨i',pc',hb',hc'.trans hgi.symm⟩
    obtain ⟨i',pc',hbh,hord⟩ := Protocol.Bar.one_member hp hX hbg hpass (g := h) hcta exited
    have hord' : ((X.tr h).take i').countP (Execution.isBarId 1) = c - 1 := by
      simp only at hord
      omega
    have ledh := Export.ledger_event hp hX words hbh (fun _ => nofun)
    have site : pc' ∈ Lib.barOneSites := by
      obtain ⟨_,one | ⟨z,_⟩ | ⟨z,_⟩⟩ := Lib.recorded_bar hX hb hbh
      · exact one.2.2
      all_goals omega
    have nb := Lib.ledger_barrier ledh site
    rw [hord'] at nb
    have enough : r ≤ ((X.tr h).take i').countP SetMaxNReg.isRequest := by
      rcases shape with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have := nb.1 (by omega); omega
      · have := nb.2 (by omega); omega
    obtain ⟨j',ev,hj',hq,hcnt⟩ := NamedBar.exists_ordinal SetMaxNReg.isRequest
      ((X.tr h).take i') (r := r - 1) (by omega)
    rw [List.getElem?_take] at hj'
    split at hj'
    · rename_i hji
      rw [List.take_take,Nat.min_eq_left (by omega)] at hcnt
      obtain ⟨pcr,kd⟩ := ev
      cases kd with
      | setMaxReg inc' n' inst' =>
        refine ⟨j',pcr,inc',n',inst',hj',?_,?_⟩
        · show ((X.tr h).take j').countP SetMaxNReg.isRequest + 1 = r
          omega
        · have hsame : SameCta L h g := ⟨hh,Frame.lt_of_get hX req,hcta⟩
          exact Protocol.Bar.one_baseCausality hp hX hsame hbh hbg hpass
            (by simp only at hord ⊢; omega) hji hik klen
      | _ => simp [SetMaxNReg.isRequest] at hq
    · cases hj'

end PTX.Kernels.InklingRelDecode.Proof.Top
