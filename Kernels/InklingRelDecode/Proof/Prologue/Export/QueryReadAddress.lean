-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Prologue.QueryInput
import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Lemmas.Flow.Arith32Word

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Arith32 Control

private theorem ldq_site (s : Site) (j : Fin 64) (h : s.pc = 388 + 2 * j.val) : s = .ldq j := by
  cases s with
  | ldq i =>
    have : i.val = j.val := by simp only [Site.pc] at h; omega
    exact congrArg Site.ldq (Fin.ext this)
  | _ => exfalso; revert h; revert j; decide +revert

private theorem load_shape : ∀ j : Fin 64,
    Lib.globalLoad (Site.ldq j).pc (2077 + j.val) 16 = true ∧
    2077 + j.val ∈ ctlLive (Site.ldq j).pc := by decide +kernel

private theorem reg_kind : ∀ j : Fin 64, copyReg (2077 + j.val) = false ∧
    queryReg (2077 + j.val) = true := by decide +kernel

/-- **A query load reads the two bytes of an element of the query tensor.** -/
public theorem query_read {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩) {j : Fin 64} (site : pc = 388 + 2 * j.val) :
    ∃ r < Q.b, ∃ tok < Q.qLen r, ∃ head < heads, ∃ d < headDim,
      r = (L.ctaidOf (g / L.block)).get .z ∧ tok = Lib.qTileRow (g % L.block) (j.val / 16) / 6 ∧
      head = (L.ctaidOf (g / L.block)).get .y * 6 + Lib.qTileRow (g % L.block) (j.val / 16) % 6 ∧
      d = Lib.qDim (g % L.block) j.val ∧
      a.loc = ⟨.global, 0, Q.qBase + 2 * ((Q.qStart r + tok) * Q.strideQ + head * headDim + d)⟩ ∧
      a.size = 2 := by
  have hj := site
  have hg := he.lt hX
  obtain ⟨w,d,t,ins,u,ht,inv,pce,hc,fire,lane,hist⟩ := prologue_occ hp hX hf he (by simp)
    (by change 27 < pc; omega) (by change pc < 574; omega)
  have pc' : pc = d.site.pc := pce
  subst pc'
  have hs : d.site = .ldq j := ldq_site _ j hj
  obtain ⟨gl,key⟩ := load_shape j
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have hsub : t.sub = 0 := by change t.sub = d.site.sub at sub; rw [hs] at sub; exact sub
  have reg := holds_mem regs (mem_factsFrom (hs ▸ key))
  let req := (L.ctaidOf (g/L.block)).get .z
  obtain ⟨hx,hy,hr⟩ := Lib.coordinate_bounds hp hg
  change req < Q.b at hr
  have val : valueOf Q L g w d (2077 + j.val) = u64 (qLane Q d.first (g % L.block)
      ((L.ctaidOf (g / L.block)).get .y) (j.val / 16) (j.val % 16)) := by
    rw [valueOf_query (reg_kind j).1 (reg_kind j).2]
    have := j.isLt
    rw [queryValue_lane (by omega) (by omega), Nat.add_sub_cancel_left]
  rw [val] at reg
  have lo : 41 < d.site.pc := by rw [hs]; simp only [Site.pc]; omega
  have first := hist.known.first (by omega)
  have last := hist.known.last (by omega)
  have on : queryOn (g % L.block) (j.val / 16) d = true := by
    simpa only [Control.Inv, hs] using inv
  have hb := hp.nTokRange
  have mono := hp.cuMono req hr
  have ce := hp.cuEnd
  have fine := Lib.qStart_mono hp (r := req + 1) (r' := Q.b) (by omega) le_rfl
  have qle := hp.qLenLe req hr
  have qlen_eq : qlen d = W (Q.qLen req) := qlen_word first last mono (by omega)
  have tokle : qTok (g % L.block) (j.val / 16) ≤ 10 := by
    unfold qTok qRow; omega
  have htok : qTok (g % L.block) (j.val / 16) < Q.qLen req := by
    have := on
    unfold queryOn at this
    dsimp only at this
    rw [qlen_eq] at this
    have eq : (BitVec.ofNat 64 ((g % L.block / 8 % 16 + 16 * (j.val / 16)) * 10923 / 65536)) =
        W (qTok (g % L.block) (j.val / 16)) := rfl
    rw [eq, scmp_gt_W (by omega) (by omega)] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have ql : Q.qLen req = Q.qStart (req + 1) - Q.qStart req := rfl
  have hgp : j.val / 16 < 4 := by omega
  have he16 : j.val % 16 < 16 := Nat.mod_lt _ (by decide)
  have hy2 : (L.ctaidOf (g / L.block)).get .y < 2 := hy
  have lane : g % L.block < 128 := ‹g % L.block < 128›
  set y := (L.ctaidOf (g / L.block)).get .y with hyd
  set tid := g % L.block with htid
  set gp := j.val / 16 with hgpd
  set e := j.val % 16 with hed
  have hs31 := hp.scalarsRange.1
  have rd : ∀ byte < 2, Q.reads (Q.qBase + 2 * ((Q.qStart req + qTok tid gp) * Q.strideQ +
      (y * 6 + (tid / 8 % 16 + 16 * gp) % 6) * 128 + (8 * (tid % 8) + e % 8 + 64 * (e / 8))) +
        byte) := fun byte hbyte =>
    .inl ⟨req, hr, qTok tid gp, htok, y * 6 + (tid / 8 % 16 + 16 * gp) % 6, by
      unfold heads; omega, 8 * (tid % 8) + e % 8 + 64 * (e / 8), by unfold headDim; omega,
      byte, hbyte, by unfold headDim; rfl⟩
  have bound := hp.readsRange _ (rd 0 (by omega))
  rw [Nat.add_zero] at bound
  have eq := qLane_eq (r := req) (tid := tid) (y := y) (gp := gp) (e := e) hs31 first
    (by omega) hy2 hgp he16 bound
  have bmod := Nat.mod_eq_of_lt (eq ▸ bound : qLane Q d.first tid y gp e < 2 ^ 64)
  obtain ⟨loc, size⟩ := Lib.global_load_loc hc (by rw [hs]; exact gl) hsub
    (x := qLane Q d.first tid y gp e % 2 ^ 64) (by simpa [u64] using reg)
    (Nat.mod_lt _ (by norm_num)) fire rfl
  rw [bmod, eq] at loc
  have s2 : a.size = 2 := by simpa using size
  exact ⟨req, hr, qTok tid gp, htok, y * 6 + (tid / 8 % 16 + 16 * gp) % 6, by unfold heads; omega,
    8 * (tid % 8) + e % 8 + 64 * (e / 8), by unfold headDim; omega, rfl, qTok_eq _ _ hgp, rfl, rfl,
    by rw [loc]; rfl, s2⟩

/-- A query load reads input bytes. -/
public theorem query_read_address {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩) (site : ∃ j : Fin 64, pc = 388 + 2 * j.val) :
    Iface.InputAcc Q a := by
  obtain ⟨j, hj⟩ := site
  obtain ⟨r, hr, tok, ht, head, hh, d, hd, -, -, -, -, loc, size⟩ := query_read hp hX hf he hj
  refine ⟨by rw [loc], by rw [loc], fun jj hj => ?_⟩
  rw [loc]
  exact .inl ⟨r, hr, tok, ht, head, hh, d, hd, jj, by omega, rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
