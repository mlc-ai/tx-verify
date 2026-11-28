-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Common.Export.TcForward
import Kernels.InklingRelDecode.Proof.Lib.TcInject
public import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleAgree
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Softmax.Export.PhysicalBar
import Kernels.InklingRelDecode.Proof.Lib.BarZero
public import Lemmas.Flow.OrdinalCount
public import Lemmas.Kernel.Safety.TableU
import Lemmas.Flow.NthEv

@[expose] public section

/-! # ERR-ALIGNED, `tcgen05` collectives: the lanes of a warp agree

Two lanes of a warp at their `k`-th collective `tcgen05` event are at one pc. By induction on `k`:
the earlier collective events of the two lanes are at the same pcs, so the numbers of earlier events
at each data position agree and so do the paired Tensor Memory operations. Those counts fix the
position (`Lib.tcVec_cases`), but for the rescale decision: the O load and the P store of a round
follow the same events. A lane that loads O decided to rescale and one that stores P did not (or
rescaled and passed the store's wait), and the decisions of a CTA's data lanes agree. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Tc
open PTX PTX.Flow PTX.Tmem.Pair Protocol.Shared Softmax.Export

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem tc_count_agree {q : Event → Bool} (hqp : ∀ e, q e = true → isTcColl e = true)
    {x jx y jy k : Nat} (ox : ((X.tr x).take jx).countP isTcColl = k)
    (oy : ((X.tr y).take jy).countP isTcColl = k)
    (same : ∀ n < k, ordEv X isTcColl q x n = ordEv X isTcColl q y n) :
    ((X.tr x).take jx).countP q = ((X.tr y).take jy).countP q := by
  rw [countP_ordinal hqp,countP_ordinal hqp,ox,oy]
  exact List.countP_congr fun n mem => by rw [same n (List.mem_range.mp mem)]

theorem ord_same {q : Event → Bool} {x jx y jy k : Nat}
    (ox : k ≤ ((X.tr x).take jx).countP isTcColl) (oy : k ≤ ((X.tr y).take jy).countP isTcColl)
    (ih : ∀ n < k, ∀ {ix iy ex ey}, X.get (x,ix) = some ex → X.get (y,iy) = some ey →
      isTcColl ex = true → isTcColl ey = true → ((X.tr x).take ix).countP isTcColl = n →
      ((X.tr y).take iy).countP isTcColl = n → ex.pc = ey.pc)
    (agree : ∀ {ix iy ex ey}, X.get (x,ix) = some ex → X.get (y,iy) = some ey →
      isTcColl ex = true → isTcColl ey = true → ex.pc = ey.pc → q ex = q ey) :
    ∀ n < k, ordEv X isTcColl q x n = ordEv X isTcColl q y n := by
  intro n hn
  obtain ⟨ix,ex,-,gx,tx,cx⟩ := exists_nthEv (X := X) (p := isTcColl) (g := x) (k := jx) (n := n)
    (by omega)
  obtain ⟨iy,ey,-,gy,ty,cy⟩ := exists_nthEv (X := X) (p := isTcColl) (g := y) (k := jy) (n := n)
    (by omega)
  have a := ordEv_eq (q := q) gx tx
  have b := ordEv_eq (q := q) gy ty
  rw [cx] at a
  rw [cy] at b
  rw [a,b]
  exact agree gx gy tx ty (ih n hn gx gy tx ty cx cy)

theorem tc_false {e : Event} (h : isTcColl e = true) : ∀ f, e.kind ≠ .ub f := by
  obtain ⟨pc,k⟩ := e
  intro f eq
  change k = .ub f at eq
  subst eq
  simp [isTcColl] at h

private theorem count_succ_of_not {g j : Nat} {e : Event} {p : Event → Bool}
    (he : X.get (g,j) = some e) (hp : p e = false) :
    ((X.tr g).take (j+1)).countP p = ((X.tr g).take j).countP p := by
  have he' : (X.tr g)[j]? = some e := he
  rw [List.take_add_one,he',Option.toList_some,List.countP_append]
  simp [hp]

/-- **A lane at the O load of a rescale and a lane at the P store of the same round with the same
earlier events cannot be.** -/
private theorem clash (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) {k x y jx jy i R : Nat} {kx ky : Kind}
    (w : SameWarp L x y)
    (gx : X.get (x,jx) = some ⟨2260,kx⟩) (gy : X.get (y,jy) = some ⟨1009,ky⟩)
    (tcx : isTcColl ⟨2260,kx⟩ = true) (tcy : isTcColl ⟨1009,ky⟩ = true)
    (ox : ((X.tr x).take jx).countP isTcColl = k) (oy : ((X.tr y).take jy).countP isTcColl = k)
    (ih : ∀ n < k, ∀ {x' y' ix iy ex ey}, SameWarp L x' y' → X.get (x',ix) = some ex →
      X.get (y',iy) = some ey → isTcColl ex = true → isTcColl ey = true →
      ((X.tr x').take ix).countP isTcColl = n → ((X.tr y').take iy).countP isTcColl = n →
      ex.pc = ey.pc)
    (pos : 1 ≤ i)
    (Nx : ((X.tr x).take jx).countP (Execution.isBarId 0) + 2 =
      3 + 5 * Iface.preloadCount Q L (x/L.block) + 4 * i + 2 + R)
    (Ny : ((X.tr y).take jy).countP (Execution.isBarId 0) + 2 =
      3 + 5 * Iface.preloadCount Q L (y/L.block) + 4 * i + 3 + R)
    (Rx : ((X.tr x).take jx).countP (fun e => e.pc == 2326) = R)
    (Ry : ((X.tr y).take jy).countP (fun e => e.pc == 2326) = R) : False := by
  have cta : x/L.block = y/L.block := w.1.2.2
  have lx : x%L.block < 128 := Export.tc_data_lane hp hX hf gx tcx
  have ly : y%L.block < 128 := Export.tc_data_lane hp hX hf gy tcy
  rw [← cta] at Ny
  obtain ⟨ux,a,b,c,r,ok,hux,gsx,skipF,cntx⟩ := ldO_source hp hX gx (tc_false tcx)
  obtain ⟨uy,e,huy,gey,pce,isb⟩ := tmemSt_source hp hX gy (tc_false tcy)
  obtain ⟨pe,ke⟩ := e
  change pe = 999 at pce
  subst pce
  cases ke <;> simp only [Execution.isBarId,Bool.false_eq_true] at isb
  rename_i id cnt md
  simp only [beq_iff_eq] at isb
  subst isb
  obtain ⟨hmd,-⟩ := Lib.recorded_bar hX hp.block gey
  subst hmd
  have stepy := countP_take_succ (p := Execution.isBarId 0) gey (by simp [Execution.isBarId])
  rw [huy] at stepy
  subst huy
  rcases bar20_source hp hX gey with ⟨kk,a2,b2,c2,r2,ok2,hkk,gys,skipT,cnty⟩|
    ⟨u2,e,hu2,gu,isbar,pce,cnt2,e2,e1,g2,p2,n2,g1,p1,n1⟩|zero
  · have uniX := rescale_agree hp hX hf safe gsx (fun _ => nofun)
      (by show Lib.afterFinal 2255=0; decide)
      (by show Lib.finalSync 2255=false; decide) lx
    have uniY := rescale_agree hp hX hf safe gys (fun _ => nofun)
      (by show Lib.afterFinal 2255=0; decide)
      (by show Lib.finalSync 2255=false; decide) ly
    have agree := decision_agree hp hX hf safe gsx gys lx ly cta.symm
      (by simp only [barOrdinal]; omega)
      (fun h ch lh n' lt => uniX h x ch lh rfl lx n' (by simp only [barOrdinal] at lt ⊢; omega))
      (fun h ch lh n' lt => uniY h y ch lh rfl ly n' (by simp only [barOrdinal] at lt ⊢; omega))
    rw [skipF,skipT] at agree
    exact Bool.noConfusion agree
  · have tc1 : isTcColl e1 = true := by
      rw [Lib.tcColl_event hX g1 n1]
      simp [p1,Lib.dataPcs]
    have c1 := countP_take_succ (p := isTcColl) g1 tc1
    rw [show u2+2+1 = uy by omega] at c1
    have c2 := count_succ_of_not (p := isTcColl) gey (by simp [isTcColl])
    obtain ⟨p1',kx'⟩ := e1
    change p1' = 2329 at p1
    subst p1
    -- the lane x made the same collective events, so its earlier one is the wait of the store
    have nubx := Frame.noUbBefore_of_get hX gx
    obtain ⟨jx',ex',hlt,gx',tcx',cx'⟩ := exists_nthEv (X := X) (p := isTcColl) (g := x)
      (k := jx) (n := k-1) (by omega)
    have same := ih (k-1) (by omega) w gx' g1 tcx' tc1 cx' (by omega)
    obtain ⟨pex,kex⟩ := ex'
    change pex = 2329 at same
    subst same
    have lenx : jx < (X.tr x).length := (List.getElem?_eq_some_iff.mp gx).1
    rcases Nat.lt_or_ge (jx'+1) jx with lt1|ge1
    · obtain ⟨e1x,g1x⟩ : ∃ e, X.get (x,jx'+1) = some e :=
        ⟨_,List.getElem?_eq_getElem (show jx'+1 < (X.tr x).length by omega)⟩
      obtain ⟨p1x,nxt⟩ := Export.after_waitStO hp hX hf gx' (tc_false tcx') g1x (nubx _ lt1 _ g1x)
      have tc1x : isTcColl e1x = false := by
        have nu1 := nubx _ lt1 _ g1x
        have := Lib.tcColl_event hX g1x nu1
        have nres : isTmemOp e1x = false := by
          cases h : isTmemOp e1x
          · rfl
          · have := Export.tmem_event_pc hX g1x h
            simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false] at this
            omega
        rw [this,nres,p1x]
        simp [Lib.dataPcs]
      obtain ⟨e2x,g2x⟩ : ∃ e, X.get (x,jx'+2) = some e :=
        ⟨_,List.getElem?_eq_getElem (show jx'+2 < (X.tr x).length by omega)⟩
      rcases Nat.lt_or_ge (jx'+2) jx with lt2|ge2
      · have p2x := nxt e2x g2x (nubx _ lt2 _ g2x)
        have tc2x : isTcColl e2x = true := by
          rw [Lib.tcColl_event hX g2x (nubx _ lt2 _ g2x),p2x]
          simp [Lib.dataPcs]
        have a1 := countP_take_succ (p := isTcColl) gx' tcx'
        have a2 := count_succ_of_not (p := isTcColl) g1x tc1x
        have a3 := nthEv_unique (p := isTcColl) gx tcx g2x tc2x (by
          rw [show jx'+2 = jx'+1+1 by rfl,a2,a1,cx']
          omega)
        omega
      · have : jx = jx'+2 := by omega
        subst this
        have p2x := nxt _ gx (tc_false tcx)
        change 2260 = 1009 at p2x
        omega
    · have : jx = jx'+1 := by omega
      subst this
      have := (Export.after_waitStO hp hX hf gx' (tc_false tcx') gx (tc_false tcx)).1
      change 2260 = 999 at this
      omega
  · have phys := physical_bar hp hX gey (fun _ => nofun) (by show 574 < 999; decide)
      (by show 999 < 2331; decide)
    have r2326 := count_succ_of_not (p := fun e : Event => e.pc == 2326) gey (by simp)
    simp only [entryOrdinal,zero] at phys
    rw [← cta] at phys
    omega

theorem pc_count_tc (hX : Consistent L kernel Assumptions.all m X) {g j P : Nat}
    (nub : Frame.NoUbBefore X g j) (hP : P ∈ Lib.dataPcs) :
    ((X.tr g).take j).countP (fun e => e.pc == P) =
      ((X.tr g).take j).countP (fun e => e.pc == P && isTcColl e) := by
  apply List.countP_congr
  intro e mem
  obtain ⟨n,hn,rfl⟩ := List.getElem_of_mem mem
  rw [List.length_take] at hn
  have hnj : n < j := by omega
  have get : X.get (g,n) = some (((X.tr g).take j)[n]) := by
    change (X.tr g)[n]? = _
    rw [← List.getElem?_take_of_lt hnj]
    exact List.getElem?_eq_getElem _
  generalize ((X.tr g).take j)[n] = ev at *
  have res := Lib.tcColl_event hX get (nub n hnj ev get)
  simp only [Bool.and_eq_true,beq_iff_eq]
  constructor
  · intro h
    refine ⟨h,?_⟩
    rw [res,h]
    simp [hP]
  · exact fun h => h.1

theorem tmem_tc {e : Event} (h : isTmemOp e = true) : isTcColl e = true := by
  obtain ⟨pc,kd⟩ := e
  cases kd <;> simp only [isTmemOp,Bool.false_eq_true] at h
  rename_i k
  cases k <;> first | rfl | (simp at h)

theorem tmem_pc (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    (get : X.get i = some e) (tc : isTcColl e = true) :
    isTmemOp e = !decide (e.pc ∈ Lib.dataPcs) := by
  have res := Lib.tcColl_event hX get (tc_false tc)
  rw [tc] at res
  cases h : isTmemOp e
  · rw [h] at res
    simpa using res.symm
  · have := Export.tmem_event_pc hX get h
    simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false] at this
    have : e.pc ∉ Lib.dataPcs := by
      simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false]
      omega
    simp [this]

private theorem agree_aux (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) : ∀ k {x y jx jy px py kx ky}, SameWarp L x y →
    X.get (x,jx) = some ⟨px,kx⟩ → X.get (y,jy) = some ⟨py,ky⟩ → isTcColl ⟨px,kx⟩ = true →
    isTcColl ⟨py,ky⟩ = true → ((X.tr x).take jx).countP isTcColl = k →
    ((X.tr y).take jy).countP isTcColl = k → px = py := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x y jx jy px py kx ky w gx gy tcx tcy ox oy
  have ihEv : ∀ n < k, ∀ {x' y' ix iy ex ey}, SameWarp L x' y' → X.get (x',ix) = some ex →
      X.get (y',iy) = some ey → isTcColl ex = true → isTcColl ey = true →
      ((X.tr x').take ix).countP isTcColl = n → ((X.tr y').take iy).countP isTcColl = n →
      ex.pc = ey.pc := by
    intro n hn x' y' ix iy ex ey sw a b c d e f
    obtain ⟨pa,ka⟩ := ex
    obtain ⟨pb,kb⟩ := ey
    exact ih n hn sw a b c d e f
  have ihxy := fun n hn {ix iy ex ey} => ihEv n hn (x' := x) (y' := y) w (ix := ix) (iy := iy)
    (ex := ex) (ey := ey)
  have cta : x/L.block = y/L.block := w.1.2.2
  have lanes : x%L.block/32 = y%L.block/32 := w.2
  have nubx := Frame.noUbBefore_of_get hX gx
  have nuby := Frame.noUbBefore_of_get hX gy
  have pcs : ∀ P ∈ Lib.dataPcs, ((X.tr x).take jx).countP (fun e => e.pc == P) =
      ((X.tr y).take jy).countP (fun e => e.pc == P) := by
    intro P hP
    rw [pc_count_tc hX nubx hP,pc_count_tc hX nuby hP]
    refine tc_count_agree (fun e h => by simpa using (Bool.and_eq_true_iff.mp h).2) ox oy
      (ord_same ox.ge oy.ge ihxy (fun _ _ tx ty h => by simp [h,tx,ty]))
  have tmem : tmemOps ((X.tr x).take jx) = tmemOps ((X.tr y).take jy) :=
    tc_count_agree (q := isTmemOp) (fun _ h => tmem_tc h) ox oy
      (ord_same ox.ge oy.ge ihxy (fun {ix iy ex ey} a b tx ty h => by
        rw [tmem_pc hX a tx,tmem_pc hX b ty,h]))
  obtain ⟨i,R,e',vx,cx,mx,l1,l2,l3,l4,l5,l6,bx⟩ := Export.tc_counts hp hX hf gx tcx
  obtain ⟨i',R',e'',vy,cy,my,k1,k2,k3,k4,k5,k6,by'⟩ := Export.tc_counts hp hX hf gy tcy
  obtain ⟨winx,a11x,a15x,othx⟩ := Export.tc_tmem hp hX hf gx tcx
  obtain ⟨winy,a11y,a15y,othy⟩ := Export.tc_tmem hp hX hf gy tcy
  have vec : Lib.tcVec px i R e' = Lib.tcVec py i' R' e'' := by
    rw [← vx,← vy]
    exact List.map_congr_left pcs
  have hx : Lib.TcFacts px i R e' (Lib.blocksOf Q L (x/L.block)) (tmemOps ((X.tr x).take jx))
      (decide (x%L.block/32 = 0)) :=
    ⟨mx,l1,l2,l3,l4,l5,l6,fun h => by simpa using winx h,a11x,a15x,fun h1 h2 => by
      simpa using othx h1 h2⟩
  have hy : Lib.TcFacts py i' R' e'' (Lib.blocksOf Q L (x/L.block)) (tmemOps ((X.tr x).take jx))
      (decide (x%L.block/32 = 0)) := by
    rw [tmem,cta,lanes]
    exact ⟨my,k1,k2,k3,k4,k5,k6,fun h => by simpa using winy h,a11y,a15y,fun h1 h2 => by
      simpa using othy h1 h2⟩
  rcases Lib.tcVec_cases hx hy vec with h|⟨rfl,rfl,hi,hR⟩|⟨rfl,rfl,hi,hR⟩
  · exact h
  · subst hi hR
    exfalso
    exact clash hp hX hf safe w gx gy tcx tcy ox oy ihEv (l2 (.inl rfl))
      (by simpa using bx (.inl rfl)) (by simpa using by' (.inr rfl)) cx cy
  · subst hi hR
    exfalso
    exact clash hp hX hf safe ⟨⟨w.1.2.1,w.1.1,w.1.2.2.symm⟩,w.2.symm⟩ gy gx tcy tcx oy ox ihEv
      (k2 (.inl rfl)) (by simpa using by' (.inl rfl)) (by simpa using bx (.inr rfl)) cy cx

/-- **Two lanes of a warp at their `k`-th collective `tcgen05` event are at one pc.** -/
public theorem tc_same_pc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) {x y jx jy px py kx ky} (w : SameWarp L x y)
    (gx : X.get (x,jx) = some ⟨px,kx⟩) (gy : X.get (y,jy) = some ⟨py,ky⟩)
    (tcx : isTcColl ⟨px,kx⟩ = true) (tcy : isTcColl ⟨py,ky⟩ = true)
    (ord : ((X.tr x).take jx).countP isTcColl = ((X.tr y).take jy).countP isTcColl) : px = py :=
  agree_aux hp hX hf safe _ w gx gy tcx tcy rfl ord.symm

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Tc
