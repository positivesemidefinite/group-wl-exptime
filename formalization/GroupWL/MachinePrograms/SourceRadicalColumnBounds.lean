import GroupWL.MachinePrograms.SourceRadicalColumn

namespace GroupWL.MachinePrograms.SourceRadicalColumn

theorem target_bound (p : ℕ) (scope coefficients : List ℕ) (b r j d i : ℕ)
    (hp : 1<p) (hj : j<r)
    (hi : i<(SourceNeighbors.selected scope r j b).length*
      (SourceRadicalClient.data p scope coefficients b r j d).width) :
    MatrixScatter.target (SourceNeighbors.selected scope r j b)
      (SourceRadicalClient.data p scope coefficients b r j d).width (r*b) (j*b) i < b*r*b := by
  let ns := SourceNeighbors.selected scope r j b
  let D := SourceRadicalClient.data p scope coefficients b r j d
  have hD : D.Valid p ns.length := SourceRadicalClient.data_valid p scope coefficients b r j d hp
  have hg : ns.length≤b := SourceNeighbors.selected_length_le _ _ _ _
  have hw : 0<D.width := by change i<ns.length*D.width at hi; nlinarith
  have hrow : i/D.width<ns.length := (Nat.div_lt_iff_lt_mul hw).2 hi
  have hblock : ns[i/D.width]?.getD 0<b := SourceReadoutClient.selected_read_lt scope r j b _ hrow
  have hcol : i%D.width<b := (Nat.mod_lt _ hw).trans_le (hD.width.trans hg)
  have hpair : (ns[i/D.width]?.getD 0)*r+j<b*r := by
    calc _ < (ns[i/D.width]?.getD 0+1)*r := by nlinarith
         _ ≤ b*r := Nat.mul_le_mul_right _ (by omega)
  change ns[i/D.width]?.getD 0*(r*b)+i%D.width+j*b<b*r*b
  calc
    _ = (ns[i/D.width]?.getD 0*r+j)*b+i%D.width := by ring
    _ < (ns[i/D.width]?.getD 0*r+j+1)*b := by nlinarith
    _ ≤ b*r*b := Nat.mul_le_mul_right _ (by omega)

theorem cost_le (p : ℕ) (scope coefficients : List ℕ) (b r j d : ℕ)
    (hp : 1<p) (hd : d≤2) :
    b*9+d*(SourceNeighbors.selected scope r j b).length*11+28+
        220*(d+(SourceNeighbors.selected scope r j b).length+p+1)^4+
        (SourceNeighbors.selected scope r j b).length*
          (SourceRadicalClient.data p scope coefficients b r j d).width*10 ≤
      290*(b+p+4)^4 := by
  let g := (SourceNeighbors.selected scope r j b).length
  let D := SourceRadicalClient.data p scope coefficients b r j d
  have hD : D.Valid p g := SourceRadicalClient.data_valid p scope coefficients b r j d hp
  have hg : g≤b := SourceNeighbors.selected_length_le _ _ _ _
  let q := b+p+4
  have hq : 1≤q := by dsimp [q]; omega
  have hb : b≤q := by dsimp [q]; omega
  have hbase : d+g+p+1≤q := by dsimp [q]; omega
  have hpow := Nat.pow_le_pow_left hbase 4
  have hq4 : q≤q^4 := Nat.le_self_pow (by decide : 4≠0) q
  have hq24 : q^2≤q^4 := by
    have hsq : 1≤q^2 := by nlinarith
    have h := Nat.mul_le_mul_left (q^2) hsq
    nlinarith
  have hwidth : g*D.width≤q*q := Nat.mul_le_mul (hg.trans hb) (hD.width.trans (hg.trans hb))
  have hdim : d*g≤2*q := Nat.mul_le_mul hd (hg.trans hb)
  change b*9+d*g*11+28+220*(d+g+p+1)^4+g*D.width*10≤290*q^4
  nlinarith

end GroupWL.MachinePrograms.SourceRadicalColumn
