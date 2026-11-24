import GroupWL.MachinePrograms.SourceRadicalCollection

/-! The completed radical table contains each actual kernel-lift entry at
its block/readout/radical coordinate. -/
namespace GroupWL.MachinePrograms.SourceRadicalTables
set_option maxHeartbeats 1600000

def address (b r block j c : ℕ) : ℕ := (block*r+j)*b+c

private theorem flat_div (x d y : ℕ) (hy : y<d) : (x*d+y)/d=x := by
  rw [Nat.mul_comm x d,Nat.mul_add_div (by omega : 0<d),Nat.div_eq_of_lt hy,Nat.add_zero]

theorem target_address (neighbors : List ℕ) (w b r j i : ℕ) :
    MatrixScatter.target neighbors w (r*b) (j*b) i=
      address b r (neighbors[i/w]?.getD 0) j (i%w) := by
  unfold MatrixScatter.target address
  ring

theorem address_readout (b r block j c : ℕ) (hj : j<r) (hc : c<b) :
    address b r block j c/b%r=j := by
  rw [address,flat_div _ _ _ hc,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hj]

theorem update_read_miss (p : ℕ) (scope coefficients dimensions initial : List ℕ)
    (b r k block j c : ℕ) (hp : 1<p) (hk : k<r) (hj : j<r) (hc : c<b) (hne : k≠j) :
    (update p scope coefficients dimensions initial b r k)[address b r block j c]?=
      initial[address b r block j c]? := by
  let ns := SourceNeighbors.selected scope r k b
  let D := SourceRadicalClient.data p scope coefficients b r k (dimensions[k]?.getD 0)
  have hD : D.Valid p ns.length := SourceRadicalClient.data_valid p scope coefficients b r k _ hp
  have hg : ns.length≤b := SourceNeighbors.selected_length_le _ _ _ _
  apply MatrixScatter.scatter_read_miss
  intro i hi he
  have hw : 0<D.width := by change i<ns.length*D.width at hi; nlinarith
  have hci : i%D.width<b := (Nat.mod_lt _ hw).trans_le (hD.width.trans hg)
  rw [target_address] at he
  have h := congrArg (fun z => z/b%r) he
  exact hne ((address_readout b r _ k _ hk hci).symm.trans
    (h.trans (address_readout b r block j c hj hc)))

theorem selected_injective (scope : List ℕ) (r j b : ℕ) :
    ∀ i<(SourceNeighbors.selected scope r j b).length,
      ∀ k<(SourceNeighbors.selected scope r j b).length,
        (SourceNeighbors.selected scope r j b)[i]?.getD 0=
          (SourceNeighbors.selected scope r j b)[k]?.getD 0 → i=k := by
  intro i hi k hk he
  have hn : (SourceNeighbors.selected scope r j b).Nodup :=
    List.Nodup.filter _ (List.nodup_range (n:=b))
  rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hk,Option.getD_some,Option.getD_some] at he
  exact hn.getElem_inj_iff.mp he

theorem update_read_hit (p : ℕ) (scope coefficients dimensions initial : List ℕ)
    (b r j a c : ℕ) (hp : 1<p) (hj : j<r) (hlen : initial.length=b*r*b)
    (ha : a<(SourceNeighbors.selected scope r j b).length)
    (hc : c<(SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).width) :
    (update p scope coefficients dimensions initial b r j)[address b r ((SourceNeighbors.selected scope r j b)[a]?.getD 0) j c]?.getD 0=
      (SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).lift[a*(SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).width+c]?.getD 0 := by
  let ns := SourceNeighbors.selected scope r j b
  let D := SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)
  have hD : D.Valid p ns.length := SourceRadicalClient.data_valid p scope coefficients b r j _ hp
  have hg : ns.length≤b := SourceNeighbors.selected_length_le _ _ _ _
  have hstride : D.width≤r*b := by
    calc D.width ≤ b := hD.width.trans hg
         _ ≤ r*b := by have h := Nat.mul_le_mul_right b (show 1≤r by omega); simpa using h
  have hi : a*D.width+c<ns.length*D.width := by nlinarith
  have ht : ∀ i<ns.length*D.width, MatrixScatter.target ns D.width (r*b) (j*b) i< initial.length := by
    intro i hi'
    rw [hlen]
    exact SourceRadicalColumn.target_bound p scope coefficients b r j _ i hp hj hi'
  have hit := MatrixScatter.scatter_read_hit ns D.lift initial D.width (r*b) (j*b)
    (ns.length*D.width) (a*D.width+c) hi ht
    (MatrixScatter.target_injective ns ns.length D.width (r*b) (j*b) hstride (selected_injective scope r j b))
  rw [target_address,flat_div _ _ _ hc,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc] at hit
  exact hit

theorem collect_read_hit (p : ℕ) (scope coefficients dimensions : List ℕ)
    (b r n j a c : ℕ) (hp : 1<p) (hn : n≤r) (hj : j<n)
    (ha : a<(SourceNeighbors.selected scope r j b).length)
    (hc : c<(SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).width) :
    (collect p scope coefficients dimensions b r n)[address b r ((SourceNeighbors.selected scope r j b)[a]?.getD 0) j c]?.getD 0=
      (SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).lift[a*(SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).width+c]?.getD 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [collect]
    by_cases he : j=n
    · subst j
      exact update_read_hit p scope coefficients dimensions _ b r n a c hp (by omega) (collect_length _ _ _ _ _ _ _) ha hc
    · have hD := SourceRadicalClient.data_valid p scope coefficients b r j (dimensions[j]?.getD 0) hp
      have hg := SourceNeighbors.selected_length_le scope r j b
      have hcb : c<b := hc.trans_le (hD.width.trans hg)
      rw [update_read_miss p scope coefficients dimensions _ b r n _ j c hp (by omega) (by omega) hcb (Ne.symm he)]
      exact ih (by omega) (by omega)

end GroupWL.MachinePrograms.SourceRadicalTables
