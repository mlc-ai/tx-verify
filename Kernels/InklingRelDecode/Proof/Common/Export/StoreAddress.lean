-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.EpilogueEvent
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Epilogue.AddrValue
import Kernels.InklingRelDecode.Proof.Lib.StoreIndex
public import Kernels.InklingRelDecode.Proof.Lib.Rows
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Lemmas.Flow.StoreGlobal

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private def gcheck (pc base src : Nat) : Bool := match kernel.code[pc]? with
  | some ⟨_, .mem a⟩ => decide (GlobalStore a base src)
  | _ => false

private theorem gcheck_store :
    ∀ j : Fin 64, gcheck (Epilogue.storePc j) (2380+j.val) (1832+j.val) = true := by
  decide +kernel

private theorem gcheck_lse : gcheck 2682 2379 1831 = true := by decide +kernel

private theorem gstore_of {pc base src : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (h : gcheck pc base src = true) : ∃ m, ins.op = .mem m ∧ GlobalStore m base src := by
  unfold gcheck at h
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [] at h <;> first | contradiction | exact ⟨_, rfl, of_decide_eq_true h⟩

private theorem mem_sites (s : Epilogue.Site) : s ∈ Epilogue.allSites := by
  cases s <;> simp [Epilogue.allSites]

private theorem site_inj {s s' : Epilogue.Site} (h : s.pc = s'.pc) : s = s' :=
  List.inj_on_of_nodup_map Epilogue.sites_nodup (mem_sites s) (mem_sites s') h

/-- The entry numbers of an epilogue state, from the launch (the numbers of `EntryNumbers`, with
the entry's validity facts read off the epilogue's own invariant). -/
private theorem entry_facts {Q L m g w} {e : Softmax.Control.Entry} (hp : Pre Q L m)
    (hg : g < L.threads) (nums : EntryNumbers Q L g w e) :
    e.split = (L.ctaidOf (g/L.block)).get .x ∧ e.head = (L.ctaidOf (g/L.block)).get .y * 6 ∧
      e.tokens = Q.nTok ∧ e.outBase = Q.oBase ∧ e.lseBase = Q.lseBase ∧
      e.firstWord.regBits.isSome ∧ e.tokens * e.split + 11 < 2^31 := by
  obtain ⟨⟨d0,rfl⟩,first,_⟩ := nums
  have hx := (Lib.coordinate_bounds hp hg).1
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,Lib.split_index_small hp hx⟩
  rw [first]
  rfl

private theorem word_mem : ∀ j : Fin 64,
    2380 + j.val ∈ Epilogue.Control.ctlLive (Epilogue.storePc j) := by decide +kernel

private theorem lse_mem : 2379 ∈ Epilogue.Control.ctlLive 2682 := by decide +kernel

private theorem first_token {Q L m z} (hp : Pre Q L m) (hz : z < Q.b) :
    (Lib.word (b32 (Q.qStart z))).toNat = Q.qStart z := by
  have := Lib.qStart_mono hp (r := z) (r' := Q.b) hz.le le_rfl
  have := hp.cuEnd
  have := hp.nTokRange
  simp only [Lib.word, Value.regBits, b32, truncBits, Option.getD_some, BitVec.toNat_ofNat]
  omega

/-- The row of a valid thread: its token is inside the request. -/
private theorem valid_token {e : Softmax.Control.Entry} {t n : Nat}
    (h : Softmax.Control.validRow e t = true) (q : e.qlen = n) :
    Softmax.Control.token t < n := by
  simp only [Softmax.Control.validRow, Softmax.Control.tokenFits, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have := h.2.1
  omega

/-- **The location of an epilogue store.** The word store `j` of thread `t` writes the four
bytes of `OPart[split, first + token, 6 y + head in group, 64 (t / 16 % 2) + j]` and the LSE
store those of `LsePart[split, first + token, 6 y + head in group]`, for a row inside its
request. -/
public theorem store_address {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.wr a bs⟩)
    (site : pc = 2682 ∨ ∃ j : Fin 64, pc = 2751 + j.val + j.val/2) :
    g%L.block < 128 ∧
    Lib.tokM (g%L.block) < Q.qLen ((L.ctaidOf (g/L.block)).get .z) ∧ a.size = 4 ∧
    ((∃ j : Fin 64, pc = 2751 + j.val + j.val/2 ∧
      a.loc = oLoc Q ((L.ctaidOf (g/L.block)).get .x)
        (Q.qStart ((L.ctaidOf (g/L.block)).get .z) + Lib.tokM (g%L.block))
        ((L.ctaidOf (g/L.block)).get .y * 6 + Lib.rowM (g%L.block) % 6)
        (64 * (g%L.block/16%2) + j.val)) ∨
     (pc = 2682 ∧ g%L.block/16%2 = 0 ∧ a.loc = lseLoc Q ((L.ctaidOf (g/L.block)).get .x)
        (Q.qStart ((L.ctaidOf (g/L.block)).get .z) + Lib.tokM (g%L.block))
        ((L.ctaidOf (g/L.block)).get .y * 6 + Lib.rowM (g%L.block) % 6))) := by
  have hg := Frame.lt_of_get hX he
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have range : 2565 ≤ pc ∧ pc < 2853 := by
    rcases site with rfl | ⟨j,rfl⟩
    · omega
    · have := j.isLt; omega
  obtain ⟨w,e,d,n,t,ins,u,hs,ht,inv,pce,hc,fire⟩ :=
    epilogue_event_entry hp hX hf he (by simp) range.1 range.2
  have lane := data_warp hp hX hk hs
  have nums := reached_numbers hp hX hg hk hs
  have qlen := nums.2.2
  have first := nums.2.1
  obtain ⟨hsplit,hhead,htok,hob,hlb,hbits,hrng⟩ := entry_facts hp hg nums
  have hentry := epiEntry_eq' ⟨hbits,hrng⟩ (g%L.block)
  have bz := (Lib.coordinate_bounds hp hg).2.2
  have bx := (Lib.coordinate_bounds hp hg).1
  have by_ : (L.ctaidOf (g/L.block)).get .y < 2 := (Lib.coordinate_bounds hp hg).2.1
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have sub0 : t.sub = 0 := sub
  have tokEq : Softmax.Control.token (g%L.block) = Lib.tokM (g%L.block) := Lib.tokOf_eq _
  have remEq : Softmax.Control.headInGroup (g%L.block) = Lib.rowM (g%L.block) % 6 :=
    Lib.remOf_eq _
  have rowLt := Lib.rowM_lt (g%L.block)
  have firstEq : (Lib.word e.firstWord).toNat = Q.qStart ((L.ctaidOf (g/L.block)).get .z) := by
    rw [first]; exact first_token hp bz
  rcases site with rfl | ⟨j,rfl⟩
  · have hsite : d.site = .lse := site_inj (by rw [← pce]; rfl)
    have both : (epiEntry e (g%L.block)).valid = true ∧
        Epilogue.Control.lead (g%L.block) = true := by
      simpa [Epilogue.Control.Inv, hsite] using inv
    have iv : (epiEntry e (g%L.block)).valid = true := both.1
    have vt : Lib.tokM (g%L.block) < Q.qLen ((L.ctaidOf (g/L.block)).get .z) := by
      rw [← tokEq]
      exact valid_token (e := e) (by rw [hentry] at iv; exact iv) qlen
    have tn := Lib.token_lt hp bz vt
    have reg := holds_mem regs (mem_factsFrom (by rw [hsite]; exact lse_mem))
    rw [Epilogue.Control.valueOf_lse, hentry] at reg
    simp only [Epilogue.Control.Entry.tile, Epilogue.Control.Entry.firstToken,
      Epilogue.Control.u64] at reg
    change t.regs 2379 = some (b64 ((e.lseBase + Lib.sx ((((Lib.word e.firstWord).toNat +
      (e.tokens * e.split + Softmax.Control.token (g%L.block))) * 12 +
      (e.head + Softmax.Control.headInGroup (g%L.block))) % 2^32) * 4) % 2^64)) at reg
    rw [firstEq, hsplit, htok, hhead, hlb, tokEq, remEq] at reg
    obtain ⟨eqN,ltN,alN⟩ := Lib.lse_address hp (s := (L.ctaidOf (g/L.block)).get .x)
      (f := Q.qStart ((L.ctaidOf (g/L.block)).get .z)) (tok := Lib.tokM (g%L.block))
      (h := (L.ctaidOf (g/L.block)).get .y * 6 + Lib.rowM (g%L.block) % 6) bx (by omega) tn
    rw [eqN] at reg
    have chk : gcheck d.site.pc 2379 1831 = true := by rw [hsite]; exact gcheck_lse
    obtain ⟨m0,hop,hm⟩ := gstore_of hc chk
    rw [hop] at fire
    have loc := fires_st_global (acc := a) (bs := bs) hm reg ltN alN sub0 fire rfl
    exact ⟨lane,vt,loc.2,Or.inr ⟨rfl,Epilogue.Control.lead_bit both.2,loc.1⟩⟩
  · have hsite : d.site = .store j := site_inj (by rw [← pce]; rfl)
    have iv : (epiEntry e (g%L.block)).valid = true := by
      simpa [Epilogue.Control.Inv, hsite] using inv
    have vt : Lib.tokM (g%L.block) < Q.qLen ((L.ctaidOf (g/L.block)).get .z) := by
      rw [← tokEq]
      exact valid_token (e := e) (by rw [hentry] at iv; exact iv) qlen
    have tn := Lib.token_lt hp bz vt
    have bd := Lib.output_word_small hp (h := ((L.ctaidOf (g/L.block)).get .y * 6 +
      Lib.rowM (g%L.block) % 6)) (d := 127) bx (by simp only [heads]; omega)
      (by simp only [headDim]; omega) tn
    simp only [heads, headDim] at bd
    have reg := holds_mem regs (mem_factsFrom (by rw [hsite]; exact word_mem j))
    rw [Epilogue.Control.valueOf_word j.isLt, hentry] at reg
    simp only [Epilogue.Control.Entry.rowAddr, Epilogue.Control.Entry.tile,
      Epilogue.Control.Entry.firstToken, Epilogue.Control.u64] at reg
    change t.regs (2380 + j.val) = some (b64 ((e.outBase + Lib.sx (((((Lib.word e.firstWord).toNat +
      (e.tokens * e.split + Softmax.Control.token (g%L.block))) * 12 +
      (e.head + Softmax.Control.headInGroup (g%L.block))) % 2^32) * 128 % 2^32) * 4 +
      g%L.block/16%2*256 + 4*j.val) % 2^64)) at reg
    rw [firstEq, hsplit, htok, hhead, hob, tokEq, remEq] at reg
    obtain ⟨eqN,ltN,alN⟩ := Lib.word_address hp (s := (L.ctaidOf (g/L.block)).get .x)
      (f := Q.qStart ((L.ctaidOf (g/L.block)).get .z)) (tok := Lib.tokM (g%L.block))
      (h := (L.ctaidOf (g/L.block)).get .y * 6 + Lib.rowM (g%L.block) % 6)
      (hb := g%L.block/16%2) (j := j.val) bx (by omega) tn (by omega) j.isLt
    rw [eqN] at reg
    have chk : gcheck d.site.pc (2380 + j.val) (1832 + j.val) = true := by
      rw [hsite]; exact gcheck_store j
    obtain ⟨m0,hop,hm⟩ := gstore_of hc chk
    rw [hop] at fire
    have loc := fires_st_global (acc := a) (bs := bs) hm reg ltN alN sub0 fire rfl
    exact ⟨lane,vt,loc.2,Or.inl ⟨j,rfl,loc.1⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
