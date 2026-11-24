import GroupWL.PGroupCandidates

/-! Mixed-radix integer descriptions for recursive p-group candidates.
Level j stores j images and one carry, each in Fin (p^j). -/
namespace GroupWL.NumericCandidateCodes

def radix (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | D+1 => radix p D*(p^D)^(D+1)

theorem radix_pos {p : ℕ} (hp : 0<p) (D : ℕ) : 0<radix p D := by
  induction D with
  | zero => exact Nat.zero_lt_one
  | succ D ih => exact Nat.mul_pos ih (pow_pos (pow_pos hp D) (D+1))

theorem radix_le {p : ℕ} (hp : 1≤p) (D : ℕ) : radix p D≤p^(D^3) := by
  induction D with
  | zero => simp [radix]
  | succ D ih =>
      calc
        radix p (D+1)=radix p D*p^(D*(D+1)) := by rw [radix,←pow_mul]
        _≤p^(D^3)*p^(D*(D+1)) := Nat.mul_le_mul_right _ ih
        _=p^(D^3+D*(D+1)) := (pow_add _ _ _).symm
        _≤p^((D+1)^3) := Nat.pow_le_pow_right hp (by nlinarith)

def pack {p D : ℕ} (tail : Fin (radix p D))
    (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) : ℕ :=
  tail.val+radix p D*((finFunctionFinEquiv images).val+(p^D)^D*carry.val)

theorem pack_lt {p D : ℕ} (tail : Fin (radix p D))
    (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) : pack tail images carry<radix p (D+1) := by
  have hc := (finProdFinEquiv (carry,finFunctionFinEquiv images)).isLt
  have h := Nat.mul_le_mul_left (radix p D) (Nat.add_one_le_iff.mpr hc)
  change (finFunctionFinEquiv images).val+(p^D)^D*carry.val<p^D*((p^D)^D) at hc
  change radix p D*((finFunctionFinEquiv images).val+(p^D)^D*carry.val+1)≤radix p D*(p^D*((p^D)^D)) at h
  have ht := tail.isLt
  change tail.val+radix p D*((finFunctionFinEquiv images).val+(p^D)^D*carry.val)<radix p D*(p^D)^(D+1)
  rw [pow_succ]
  nlinarith

theorem pack_mod {p D : ℕ} (tail : Fin (radix p D))
    (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) :
    pack tail images carry%radix p D=tail.val := by
  simp [pack,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt tail.isLt]

theorem pack_div {p D : ℕ} (hp : 0<p) (tail : Fin (radix p D))
    (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) :
    pack tail images carry/radix p D=(finFunctionFinEquiv images).val+(p^D)^D*carry.val := by
  simp [pack,Nat.add_mul_div_left _ _ (radix_pos hp D),Nat.div_eq_of_lt tail.isLt]

theorem images_mod {p D : ℕ} (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) :
    ((finFunctionFinEquiv images).val+(p^D)^D*carry.val)%((p^D)^D)=(finFunctionFinEquiv images).val := by
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (finFunctionFinEquiv images).isLt]

theorem carry_div {p D : ℕ} (hp : 0<p) (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) :
    ((finFunctionFinEquiv images).val+(p^D)^D*carry.val)/((p^D)^D)%(p^D)=carry.val := by
  rw [Nat.add_mul_div_left _ _ (pow_pos (pow_pos hp D) D),Nat.div_eq_of_lt (finFunctionFinEquiv images).isLt,
    Nat.zero_add,Nat.mod_eq_of_lt carry.isLt]

end GroupWL.NumericCandidateCodes
