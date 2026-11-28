-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PeerStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PExchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PstAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Lemmas.Order.ReadLast

@[expose] public section

/-! # The peer load returns the partner's peer store

The load of a lane `g` of warpgroup 0 at pc `477 + 5 k0` after `r + 1` pair-barrier events returns,
byte by byte, the bytes `8 el .. 8 el + 7` of the 16 bytes the partner `w0Partner` stored at pc
`403 + 10 k0` after `r` pair-barrier events (`peer_read_bytes`): the store is ordered before the
load by the pair barrier (`pex_sp`); every other writer of a byte is a thread access of the P
exchange (`pex_cls`), ordered before the store (barrier 9, fewer rounds), after the load (more
rounds), or the store itself (same round, same slot: `wg0Pst_inj`, `peer_store`'s uniqueness). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The warp of a lane of warpgroup 0 and its partner's have one parity. -/
theorem partner_warp_par {g : Nat} {h : Nat} (hp : Pre P L m)
    (hw : warp L g < 4) (hmod : h % L.block = (g % L.block) ^^^ 64) :
    warp L h % 2 = warp L g % 2 := by
  have hwg := warp_tid hp g
  have hwhh := warp_tid hp h
  have hb := hp.block
  have key : ∀ x < 128, (x ^^^ 64) / 32 = x / 32 ^^^ 2 := by decide
  have hg4 : g % L.block / 32 < 4 := by rw [← hwg]; exact hw
  have e1 : h % L.block / 32 = g % L.block / 32 ^^^ 2 := by
    rw [hmod]
    exact key _ (by omega)
  rw [hwhh, hwg, e1, xor2_mod _ hg4]

/-- A thread access of a byte of `pExchange` is at a pc of warpgroup 0's code. -/
private theorem pex_wg0At (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool} {l : Loc} {c : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hi : X.Access (g, k) a w) (hc : a.Covers l)
    (hl : MemRow.LocIn L c .pExchange l) (hcl : c = g / L.block) : Wg0At L g e.pc := by
  subst hcl
  obtain ⟨e', he', hr⟩ := access_region hp hX hFw hi hc hl.1
  rw [he] at he'
  cases he'
  rcases hr with ⟨-, h⟩ | ⟨hat, (h | h | h) | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, r, h | h⟩
  all_goals first
    | exact hat
    | exact absurd (locIn_eq h hl).2 (by simp)

/-- A write at a byte of `pExchange` that is no P store is a peer store, at its place. -/
private theorem pst_of_wr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {dst : Acc} {ws : List Byte} {l : Loc}
    (hget : X.get (g, k) = some ⟨pc, .wr dst ws⟩) (hat : Wg0At L g pc)
    (hn : ¬ ∃ j < 4, pc = 704 + j) (hc : dst.Covers l)
    (hl : MemRow.LocIn L (g / L.block) .pExchange l) :
    ∃ j < 8, pc = 403 + 10 * j ∧ MemRow.WsAcc L (g / L.block)
      (204800 + 4096 * ((L.tidOf g).x / 32 ^^^ 2) + 16 * ((L.tidOf g).x % 32) + 512 * j) 16
      dst := by
  have hg := Frame.lt_of_get hX hget
  have ht := MemRow.wg0_tid hat.1
  have hm : MemRow.MemEvent (⟨pc, .wr dst ws⟩ : Event) := .inr (.inr (.inl ⟨dst, ws, rfl⟩))
  rcases memRow_wg0 hp hX hFw hg hget hat hm with ⟨a1, b1, h⟩ | ⟨a1, b1, h, -⟩ |
    ⟨a1, b1, h, hw'⟩ | ⟨a1, b1, h, hl' | hst⟩
  · cases h
  · cases h
  · cases h
    rcases hw' with ⟨j, hj, hpc, hw⟩ | ⟨-, hw⟩ | ⟨j, hj, el, hel, hpc, -⟩
    · exact ⟨j, hj, hpc, hw⟩
    · exfalso
      have hrow : MemRow.SharedIn L (g / L.block) .rowMax dst :=
        MemRow.wsAcc_in hw (by simp only [Region.lo]; omega)
          (by simp only [Region.lo, Region.size]; omega)
      exact absurd (locIn_eq (hrow.locIn hc) hl).2 (by simp)
    · exact absurd ⟨j, hj, hpc⟩ hn
  · cases h
    obtain ⟨-, hl', -⟩ := hl'
    obtain ⟨hcs, -⟩ := hc
    have h2 := hl.1
    rw [hl'] at hcs
    rw [h2] at hcs
    cases hcs
  · cases h
    exact absurd (locIn_eq ((MemRow.wg0Stage_in hat.1 hst).locIn hc) hl).2 (by simp)

private theorem pexUse_n9 {t o r n9 np : Nat} {w : Bool} (h : PexUse t w o r n9 np) :
    n9 ≤ 2 * r + 2 := by
  unfold PexUse at h
  omega


/-- **The peer load returns the partner's peer store** (valid rows): the load of lane `g` at pc
`477 + 5 k0` after `r + 1` pair-barrier events returns the bytes `8 el .. 8 el + 7` of the 16-byte
store of the partner at pc `403 + 10 k0` after `r` pair-barrier events (`peer_store`), when every
such store writes sixteen bytes (`hlen`); `el` is the load's element. -/
theorem peer_read_bytes (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {g k r k0 : Nat} {a : Acc}
    {bs : List (Option Byte)} {kb : Nat} (hw : warp L g < 4) (hk0 : k0 < 8)
    (he : X.get (g, k) = some ⟨477 + 5 * k0, .rd a bs⟩)
    (hnp : ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1)
    (hkb : kb < (X.tr g).length)
    (hnb : ((X.tr g).take kb).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1)
    (hrR : r < blocksOf P L (g / L.block)) (hv : W0Below P L X (w0Partner L g) g kb)
    (hlen : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) →
      ws.length = 16) :
    ∃ j f a' ws, X.get (w0Partner L g, j) = some f ∧ f.pc = 403 + 10 * k0 ∧
      f.kind = .wr a' ws ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId (10 + warp L g % 2)) = r ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) ∧
      ∃ el < 2, a'.loc.addr + 8 * el = a.loc.addr ∧ bs = ((ws.drop (8 * el)).take 8).map some := by
  have hg := Frame.lt_of_get hX he
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hs, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  obtain ⟨j, f, hf, hfpc, hcj, htc, huniq⟩ := peer_store hp hX hFw hR hw hkb hk0 hnb hrR hv
  generalize hh : w0Partner L g = h at *
  have hpar := partner_warp_par (h := h) hp hw hmod
  have hcjh : ((X.tr h).take j).countP (Execution.isBarId (10 + warp L h % 2)) = r := by
    rw [hpar]; exact hcj
  obtain ⟨fpc, fk⟩ := f
  simp only at hfpc
  obtain ⟨a', ws, hk', hwa'⟩ := wg0_pstAt hp hX hFw hwh hk0 hf (hv j ⟨fpc, fk⟩ hf htc).2 hfpc
  simp only at hk'
  subst hk'
  have hat : Wg0At L g (477 + 5 * k0) := ⟨hw, by omega, by omega⟩
  have hm : MemRow.MemEvent (⟨477 + 5 * k0, .rd a bs⟩ : Event) := .inl ⟨a, bs, rfl⟩
  obtain ⟨el, hel, hwa⟩ : ∃ el < 2, MemRow.WsAcc L (g / L.block)
      (204800 + 4096 * ((L.tidOf g).x / 32) + 16 * ((L.tidOf g).x % 32) + 512 * k0 + 8 * el)
      8 a := by
    rcases memRow_wg0 hp hX hFw hg he hat hm with ⟨a1, b1, h1⟩ | ⟨a1, b1, h1, hr1⟩ |
      ⟨a1, b1, h1, -⟩ | ⟨a1, b1, h1, -⟩
    · cases h1
    · cases h1
      rcases hr1 with ⟨hpc, -⟩ | ⟨k1, hk1, el, hel, hpc, hw1⟩ | ⟨hpc, -⟩
      · try simp only at hpc
        omega
      · try simp only at hpc
        obtain rfl : k1 = k0 := by omega
        exact ⟨el, hel, hw1⟩
      · try simp only at hpc
        omega
    · cases h1
    · cases h1
  have hb0 : L.block = 384 := by have := hp.block; omega
  have hxg : (L.tidOf g).x = g % L.block := by rw [tidOf_x_eq hp, hb0]
  have hxh : tidOf L h = (g % L.block) ^^^ 64 := by
    show (L.tidOf h).x = _
    rw [tidOf_x_eq hp, ← hb0, ← hmod]
  have hdec : ∀ x < 128, (x ^^^ 64) / 32 ^^^ 2 = x / 32 ∧ (x ^^^ 64) % 32 = x % 32 := by decide
  have htg : g % L.block < 128 := by
    have := hwa.2
    have h2 := MemRow.wg0_tid hw
    rw [hxg] at h2
    exact h2
  obtain ⟨hdv, hmd⟩ := hdec _ htg
  obtain ⟨hl1, hs1⟩ := hwa
  obtain ⟨hl2, hs2⟩ := hwa'
  rw [hxg] at hl1
  rw [hxh, hdv, hmd, hdiv] at hl2
  have hsp : a.loc.space = a'.loc.space := by rw [hl1, hl2]; rfl
  have hct : a.loc.cta = a'.loc.cta := by rw [hl1, hl2]; rfl
  have hA : a.loc.addr = a'.loc.addr + 8 * el := by
    rw [hl1, hl2]
    simp only [wsLoc]
    omega
  have hws : ws.length = 16 := hlen j ⟨fpc, .wr a' ws⟩ a' ws hf hfpc rfl htc
  have hcov : ∀ k' < 8, a'.Covers (a.loc.at k') := fun k' hk' => by
    refine ⟨hsp, hct, ?_, ?_⟩ <;> simp only [Loc.at, hs2] <;> omega
  have hMR : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨_, he⟩
  have hMW : X.MemWrites (.thread (h, j)) a' ws := Or.inl ⟨fpc, hf⟩
  have hAr : X.Access (g, k) a false := Or.inl ⟨bs, ⟨_, he⟩, rfl⟩
  have hAw : X.Access (h, j) a' true := Or.inr (Or.inl ⟨ws, ⟨fpc, hf⟩, rfl⟩)
  have hrow : MemRow.SharedIn L (g / L.block) .pExchange a :=
    MemRow.wsAcc_in ⟨hl1, hs1⟩ (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega)
  have hloc : ∀ k' < 8, MemRow.LocIn L (g / L.block) .pExchange (a.loc.at k') := fun k' hk' =>
    MemRow.SharedIn.locIn hrow (Acc.covers_at (by omega))
  have hclsR : ∀ k' < 8, ∃ e1, PexCls P L X g k e1 false
      ((a.loc.at k').addr - L.sharedBase - 204800) (a.loc.at k').cta := fun k' hk' =>
    (pex_cls hp hX hFw hAr (Acc.covers_at (by omega)) (hloc k' hk')).imp fun e h => h.1
  have hclsW : ∀ k' < 8, ∃ e1, PexCls P L X h j e1 true ((a.loc.at k').addr - L.sharedBase - 204800)
      (a.loc.at k').cta := fun k' hk' =>
    (pex_cls hp hX hFw hAw (hcov k' hk') (hloc k' hk')).imp fun e h => h.1
  have hn9r : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 1 := by
    obtain ⟨e1, hc1⟩ := hclsR 0 (by omega)
    obtain ⟨r0, -, hu, -⟩ := hc1.use
    unfold PexUse at hu
    rcases hu with ⟨h1, -⟩ | ⟨-, h2, h3, -⟩ | ⟨h1, -⟩
    · cases h1
    · omega
    · cases h1
  have hn9s : ((X.tr h).take j).countP (Execution.isBarId 9) = 2 * r + 1 := by
    obtain ⟨e1, hc1⟩ := hclsW 0 (by omega)
    obtain ⟨r0, -, hu, -⟩ := hc1.use
    have he1 : e1 = ⟨fpc, .wr a' ws⟩ := Option.some.inj (hc1.get.symm.trans hf)
    unfold PexUse at hu
    rcases hu with ⟨-, h2, h3, -⟩ | ⟨h1, -⟩ | ⟨-, h2, h3, -⟩
    · omega
    · cases h1
    · obtain ⟨j', hj', hpc'⟩ := (hc1.ostPc rfl).mp (by omega)
      rw [he1] at hpc'
      simp only at hpc'
      omega
  have hv' : ∀ k' < a.size, ByteCausality L X (a.loc.at k') (.thread (h, j)) (.thread (g, k)) :=
    fun k' hk' => by
    obtain ⟨e1, hc1⟩ := hclsR k' (by omega)
    obtain ⟨e2, hc2⟩ := hclsW k' (by omega)
    exact .direct (.of_base L (pex_sp hp hX hFw hR hc2 hc1 rfl rfl (by rw [hn9s, hn9r])))
  have hnbr : Execution.isBarId 9 (⟨477 + 5 * k0, .rd a bs⟩ : Event) = false := by
    simp [Execution.isBarId]
  have hall : ∀ k' < a.size, ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k') → w' = .thread (h, j) ∨
        ByteCausality L X (a.loc.at k') w' (.thread (h, j)) ∨
        ByteCausality L X (a.loc.at k') (.thread (g, k)) w' := by
    intro k' hk' w' dst' bytes hMW' hc'
    have hk8 : k' < 8 := by omega
    have hl := hloc k' hk8
    have hI := hMW'.intent
    cases w' with
    | async i q =>
      exfalso
      obtain ⟨gi, ki⟩ := i
      rcases async_region hp hX hFw hI hc' hl.1 with ⟨b, h1⟩ | ⟨hr', pc, bb, s1, acc, mask,
        idx, hget, hbb, hat', hp', hfp⟩ | ⟨b, h1, -⟩
      · exact absurd (locIn_eq h1 hl).2 (by simp)
      · subst hp'
        cases hI.1
      · exact absurd (locIn_eq h1 hl).2 (by simp)
    | thread x =>
      obtain ⟨g', k''⟩ := x
      have hacc : X.Access (g', k'') dst' true := hI
      obtain ⟨e', hcls, hwr'⟩ := pex_cls hp hX hFw hacc hc' hl
      obtain ⟨r', hr'R, hu', -⟩ := hcls.use
      have hg' := Frame.lt_of_get hX hcls.get
      have hcta' : g' / L.block = g / L.block := by
        have := hcls.cta
        rw [hl1] at this
        exact this.symm
      have hk2 : k'' < (X.tr g').length := (List.getElem?_eq_some_iff.mp hcls.get).1
      have hb' := pexUse_n9 hu'
      rcases Nat.lt_trichotomy (((X.tr g').take k'').countP (Execution.isBarId 9)) (2 * r + 1)
        with hlt | heq | hgt
      · right; left
        have hj2 : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hf).1
        exact .direct (.of_base L (bar9_order hp hX hFw hR ⟨hg', Frame.lt_of_get hX hf,
          by rw [hcta', hdiv]⟩ hcls.warp hcls.get hcls.n9 hj2 (by rw [hn9s]; exact hlt)
          (by omega)))
      · left
        obtain ⟨bs', pc'', hget''⟩ := hwr' rfl
        have he' : e' = ⟨pc'', .wr dst' bs'⟩ := Option.some.inj (hcls.get.symm.trans hget'')
        have hodd : ¬ ∃ j' < 4, pc'' = 704 + j' := fun hex => by
          have := (hcls.ostPc rfl).mpr (by rw [he']; exact hex)
          omega
        have hat'' := pex_wg0At hp hX hFw hget'' hacc hc' hl hcta'.symm
        obtain ⟨j', hj', hpc', hwa''⟩ := pst_of_wr hp hX hFw hget'' hat'' hodd hc'
          (by rw [hcta']; exact hl)
        have hcnt' := hu'
        unfold PexUse at hcnt'
        rcases hcnt' with ⟨-, h2, h3, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩
        swap
        · cases h1
        swap
        · omega
        obtain ⟨hl3, hs3⟩ := hwa''
        obtain ⟨-, -, hc1, hc2⟩ := hc'
        rw [hl3] at hc1 hc2
        rw [hs3] at hc2
        simp only [wsLoc, Loc.at] at hc1 hc2
        have hA' : a'.loc.addr = L.sharedBase + (204800 + 4096 * (g % L.block / 32) +
            16 * (g % L.block % 32) + 512 * k0) := by rw [hl2]; rfl
        have ht1 := MemRow.wg0_tid hat''.1
        have ht2 : (g % L.block) ^^^ 64 < 128 := by
          have := MemRow.wg0_tid hwh
          have h3 : (L.tidOf h).x = (g % L.block) ^^^ 64 := hxh
          omega
        obtain ⟨ht'', hjk⟩ := MemRow.wg0Pst_inj (t := (L.tidOf g').x) (t' := (g % L.block) ^^^ 64)
          ht1 ht2 hj' hk0 (by omega)
        have hg'' : g' = h := by
          have h1 : g' % L.block = h % L.block := by
            have := tidOf_x_eq hp g'
            rw [hmod, ← ht'', this, hb0]
          have h4 : g' / L.block = h / L.block := by rw [hcta', hdiv]
          calc g' = L.block * (g' / L.block) + g' % L.block := (Nat.div_add_mod _ _).symm
            _ = L.block * (h / L.block) + h % L.block := by rw [h4, h1]
            _ = h := Nat.div_add_mod _ _
        subst hg''
        have hpc3 : e'.pc = 403 + 10 * k0 := by rw [he']; simp only; omega
        rw [hpar] at h3
        rw [huniq k'' e' hcls.get (fun _ h => by rw [he'] at h; cases h) hpc3 (by omega)]
      · right; right
        exact .direct (.of_base L (bar9_order hp hX hFw hR ⟨hg, hg', by rw [hcta']⟩ hw he
          hnbr hk2 (by rw [hn9r]; exact hgt) (by omega)))
  have hbl : bs.length = a.size := (hX.rf _ a bs hMR).1
  have hbytes : bs = ((ws.drop (8 * el)).take 8).map some := by
    apply List.ext_getElem?
    intro k'
    by_cases hk' : k' < 8
    · have hk'' : k' < a.size := by omega
      have h1 := read_byte_of_last_write_ordered hX hMR hk'' hMW (hcov k' hk') (hv' k' hk'')
        (hall k' hk'')
      rw [h1]
      have hi : 8 * el + k' < ws.length := by omega
      have hidx : (a.loc.at k').addr - a'.loc.addr = 8 * el + k' := by
        simp only [Loc.at]
        omega
      unfold wbyte
      rw [hidx]
      simp [hk', List.getElem?_eq_getElem hi]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  exact ⟨j, ⟨fpc, .wr a' ws⟩, a', ws, hf, hfpc, rfl, hcj, htc, el, hel, hA.symm, hbytes⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
