-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PHandoff
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreArrival
public import Lemmas.Tcgen05.TmemRace
import Kernels.InklingRelDecode.Proof.Common.Export.LdWait
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarArrivals
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl

@[expose] public section

/-! # A softmax load or store is done before the MMA lane's event after its poll of the publication

The MMA lane's poll of the probability slot with `r / 2` earlier polls observes lane zero's
`r / 2`-th arrival on the slot, which is the publication of round `r` or of a later round of the
slot's parity; the `wait::st` of a store and the `wait::ld` of a load of that round are before every
such publication. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The publication of round `r` or a later one precedes the MMA lane's events after
`r / 2 + 1` polls of the probability slot of its parity.** -/
public theorem arrival_to_mma (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (words : RoleBytes L X) {c : Nat} (hc : c < L.grid) {r k : Nat}
    (hk : k < (X.tr (Protocol.KV.leader L X c 7)).length)
    (polls : r/2+1 ≤ okPolls ((Object.prob (MbarRow.slot2 r)).loc L c)
      ((X.tr (Protocol.KV.leader L X c 7)).take k)) :
    ∃ ia l tx cnt rel sc, X.get (c*L.block,ia) = some ⟨1013,.arrive l tx cnt rel sc⟩ ∧
      r ≤ ((X.tr (c*L.block)).take ia).countP (fun e : Event => e.pc == 1013) ∧
      baseCausality L X (c*L.block,ia) (Protocol.KV.leader L X c 7,k) := by
  have hz : c*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have hU := prob_handoff hp hX hf rows init words hc (MbarRow.slot2 r)
  obtain ⟨j,pc,p,acq,sc,hjk,hw,hq⟩ := UnitHandoff.exists_poll polls
  obtain ⟨ia,harr,hsync⟩ := hU _ j pc p acq sc (r/2) rfl hw (by simpa using hq) (c*L.block)
    ⟨0,rfl⟩
  obtain ⟨ev,hev,hit⟩ := hsync.arrives
  obtain ⟨tx,n,rel,sc',rfl,-⟩ := arrival_event rows hz hev hit
  obtain ⟨-,slot,bound⟩ := arrival_ordinal rows hz hev
  have : (MbarRow.slot2 r).val = r%2 := rfl
  exact ⟨ia,_,tx,n,rel,sc',hev,by omega,hU.hb (h := Protocol.KV.leader L X c 7) (g := c*L.block)
    (e := ia) rfl hw (by simpa using hq) ⟨0,rfl⟩ (by omega) hjk hk⟩

/-- **A store of round `r` is done before the MMA lane's events after `r / 2 + 1` polls of the
probability slot of its parity.** -/
public theorem store_before_mma (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (words : RoleBytes L X) {c : Nat}
    (hc : c < L.grid) {t sk pcy a vals sh r}
    (hy : X.get (t,sk) = some ⟨pcy,.tc (.st a vals sh)⟩) (hpcy : pcy = 1009 ∨ pcy = 2328)
    (lt : t%L.block < 128) (cta : t/L.block = c)
    (rd : pollRound 1257 ((X.tr t).take sk) = r+1) {k : Nat}
    (hk : k < (X.tr (Protocol.KV.leader L X c 7)).length)
    (polls : r/2+1 ≤ okPolls ((Object.prob (MbarRow.slot2 r)).loc L c)
      ((X.tr (Protocol.KV.leader L X c 7)).take k)) :
    StoreDoneBefore L X (t,sk) (Protocol.KV.leader L X c 7,k) := by
  have lp : c*L.block%L.block < 128 := by rw [Nat.mul_mod_left]; omega
  have cz : c*L.block/L.block = c := by simp [hp.block]
  obtain ⟨ia,l,tx,n,rel,sc,hev,hr,bc2⟩ := arrival_to_mma hp hX hf rows init words hc hk polls
  obtain ⟨⟨pcw,g1⟩,bc⟩ := store_arrival hp hX hf safe base hev lp lt (by rw [cta,cz]) hy hpcy
    rd hr
  exact ⟨⟨a,vals,sh,pcy,hy⟩,.inl ⟨(t,sk+1),⟨pcw,g1⟩,rfl,Nat.lt_succ_self _,.inl (bc.trans bc2)⟩⟩

/-- **A load of round `r` is waited for before the MMA lane's events after `r / 2 + 1` polls of
the probability slot of its parity.** -/
public theorem ld_before_mma (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (words : RoleBytes L X) {c : Nat}
    (hc : c < L.grid) {t k0 pcy a vals sh r}
    (hy : X.get (t,k0) = some ⟨pcy,.tc (.ld a vals sh)⟩) (hpcy : pcy = 1265 ∨ pcy = 2260)
    (lt : t%L.block < 128) (cta : t/L.block = c)
    (rd : pollRound 1257 ((X.tr t).take k0) = r+1) {k : Nat}
    (hk : k < (X.tr (Protocol.KV.leader L X c 7)).length)
    (polls : r/2+1 ≤ okPolls ((Object.prob (MbarRow.slot2 r)).loc L c)
      ((X.tr (Protocol.KV.leader L X c 7)).take k)) :
    WaitBefore L X .waitLd (t,k0) (Protocol.KV.leader L X c 7,k) := by
  have lp : c*L.block%L.block < 128 := by rw [Nat.mul_mod_left]; omega
  have cz : c*L.block/L.block = c := by simp [hp.block]
  obtain ⟨ia,l,tx,n,rel,sc,hev,hr,bc2⟩ := arrival_to_mma hp hX hf rows init words hc hk polls
  have tc : isTcColl ⟨pcy,.tc (.ld a vals sh)⟩ = true := by
    rcases hpcy with rfl|rfl <;> rfl
  obtain ⟨i,w,s1,-,s3,-,-⟩ := Export.ld_round hp hX hf base hy tc hpcy
  have low : Softmax.Export.mandatory ((X.tr t).take k0) <
      4*(((X.tr (c*L.block)).take ia).countP (fun e : Event => e.pc == 1013)) + 2 := by
    rcases hpcy with rfl|rfl
    · by_cases h0 : i = 0 <;> simp [h0] at s3 <;> omega
    · simp at s3
      omega
  obtain ⟨len,-,nu⟩ := arrival_handoff hp hX hf safe hev lp lt (by rw [cta,cz]) hy low
  obtain ⟨e1,g1⟩ : ∃ e1, X.get (t,k0+1) = some e1 :=
    ⟨_,List.getElem?_eq_some_iff.mpr ⟨len,rfl⟩⟩
  obtain ⟨pcw,rfl⟩ := Export.ld_wait hp hX hf nu (by omega) hy g1
  refine ⟨(t,k0+1),⟨pcw,g1⟩,rfl,Nat.lt_succ_self _,.inl ((arrival_handoff hp hX hf safe hev lp lt
    (by rw [cta,cz]) g1 ?_).2.1.trans bc2)⟩
  rw [mandatory_tc hX hp.block hy]
  exact low

end PTX.Kernels.InklingRelDecode.Proof.Tmem
