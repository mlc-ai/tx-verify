-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.History
public import Kernels.InklingRelDecode.Proof.Prologue.ShapeMbar
import Lemmas.Flow.NotClc

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Control MbarRow

private theorem slot_inj {L g i j} (h : loc L g (Iface.kvReady i) = loc L g (Iface.kvReady j)) :
    i=j := by
  have a := congrArg Loc.addr h
  change L.sharedBase+(213216+8*i.val)=L.sharedBase+(213216+8*j.val) at a
  apply Fin.ext; omega

private theorem source_arr {L g e s b} (use : Use L g s e (loc L g (Iface.kvReady b)))
    (h : arrivesOn (loc L g (Iface.kvReady b)) e = true) : s = .arr b := by
  obtain ⟨pc,k⟩ := e
  cases use with
  | init _ _ _ kd => cases kd; contradiction
  | arr _ site addr _ => rw [slot_inj addr]; exact site
  | copy _ _ _ _ kd =>
    obtain ⟨_,_,kd,_,_⟩ := kd; cases kd; contradiction

private theorem source_copy {L g e s b} (use : Use L g s e (loc L g (Iface.kvReady b)))
    (h : issuesTo (loc L g (Iface.kvReady b)) e = true) : ∃ j, s = .ptc b j := by
  obtain ⟨pc,k⟩ := e
  cases use with
  | init _ _ _ kd => cases kd; contradiction
  | arr _ _ _ kd => change k=_ at kd; cases kd; contradiction
  | copy _ j site addr _ => exact ⟨j,slot_inj addr ▸ site⟩

private theorem four_add (c : Cnt) (e : Event) (b : Fin 3) :
    four (bump c e) b = four c b + (e.pc == ptcPc b 0).toNat + (e.pc == ptcPc b 1).toNat +
      (e.pc == ptcPc b 2).toNat + (e.pc == ptcPc b 3).toNat := by unfold four bump; omega

private theorem early_no_bar {d : D} {t ins e o L g} (pc : d.site.rank < 4*179)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∀ i, Execution.isBarId i e = false := by
  have lo := d.site.pc_range.1
  unfold Site.rank at pc
  have checked : (kernel.code.zipIdx.all fun (ins,p) =>
      !(27≤p && p<179) || !barOp ins.op) = true := by decide +kernel
  have test := List.all_eq_true.mp checked (ins,d.site.pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  have upper : d.site.pc<179 := by omega
  simp [lo,upper] at test
  intro i
  obtain ⟨p,k⟩ := e
  cases k <;> try rfl
  exact False.elim (by have h := fires_bar_op hf rfl; simp_all)

theorem history_next {Q L g w d dn e c m X k t ins o}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some e) (ht : (code Q L g w).AtD d t)
    (hc : kernel.code[d.site.pc]?=some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (pc : e.pc=d.site.pc) (hi : e.pc<574)
    (hist : History Q L g d c) (hn : Control.next Q L g d e = some (some dn)) :
    History Q L g dn (c.bump L g e) := by
  have use := fun {l} => use_of_fires hp hX he (l := l) (ht := ht) (pc := pc) (hi := hi)
    (hc := hc) (hf := hf)
  refine ⟨ref_next hist.visits pc hn,known_next hist.known hn ?_,gate_next hn hist.block,
    ?_,?_,?_,?_⟩
  · intro j site a bs kd
    obtain ⟨p,ek⟩ := e; cases kd; cases pc
    exact request_value hp hX (Frame.lt_of_get hX he) j site ht hc he hf
  · intro p eq
    obtain ⟨whereAt,m,i,kd⟩ := elect_before hn pc eq
    change 0<c.vote p+(wonAt p (laneOf L g) e).toNat
    simp [wonAt,whereAt,kd]
  · intro b
    let l := loc L g (Iface.kvReady b)
    change c.arrivals b+(arrivesOn l e).toNat ≤ c.visits (arrPc b)+(e.pc==arrPc b).toNat
    have bound := hist.arrive b
    cases h : arrivesOn l e
    · simp; omega
    · have obj : Frame.MbarOf e l := by
        obtain ⟨_,k⟩ := e; cases k <;> try contradiction
        exact (of_decide_eq_true h).symm
      have site := source_arr (use obj) h
      have pos : e.pc=arrPc b := pc.trans (congrArg Site.pc site)
      simp [pos,bound]
  · intro b
    let l := loc L g (Iface.kvReady b)
    change c.copies b+(issuesTo l e).toNat ≤ four (bump c.visits e) b
    rw [four_add]
    have bound := hist.copy b
    cases h : issuesTo l e
    · simp; omega
    · have obj : Frame.MbarOf e l := by
        obtain ⟨_,k⟩ := e; cases k <;> try contradiction
        rename_i _ sp
        exact (of_decide_eq_true h : sp.mbar=l)
      obtain ⟨j,site⟩ := source_copy (use obj) h
      have pos : e.pc=ptcPc b j := pc.trans (congrArg Site.pc site)
      have tick : ∀ b j, 1 ≤ ((ptcPc b j == ptcPc b 0).toNat +
          (ptcPc b j == ptcPc b 1).toNat + (ptcPc b j == ptcPc b 2).toNat +
          (ptcPc b j == ptcPc b 3).toNat) := by decide +kernel
      rw [pos]; have := tick b j; change c.copies b+1 ≤ _; omega
  · intro hi
    have lt := rank_next hn
    have no := early_no_bar (by omega : d.site.rank < 4*179) hc hf
    obtain ⟨h0,h1⟩ := hist.bars (by omega)
    simp [Counts.bump,no,h0,h1]

end PTX.Kernels.InklingRelDecode.Proof.Prologue
