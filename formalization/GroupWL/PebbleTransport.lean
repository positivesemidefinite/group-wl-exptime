import GroupWL.PebbleGame

/-! Transport of actual game positions and winning strategies under group
isomorphisms. The slot set and after-pickup rule are preserved exactly. -/
namespace GroupWL.PebbleGame

variable {G H K : Type*} [Group G] [Group H] [Group K] {m : ℕ}

def mapRight (e : H ≃* K) (p : Position m G H) : Position m G K :=
  fun i => (p i).map (fun gh => (gh.1, e gh.2))

@[simp] theorem mapRight_some (e : H ≃* K) (p : Position m G H)
    (i : Fin m) (g : G) (h : K) :
    mapRight e p i = some (g, h) ↔ p i = some (g, e.symm h) := by
  cases hi : p i with
  | none => simp [mapRight, hi]
  | some gh =>
      rcases gh with ⟨g', h'⟩
      simp only [mapRight, hi, Option.map_some, Option.some.injEq, Prod.mk.injEq]
      exact and_congr Iff.rfl e.eq_symm_apply.symm

@[simp] theorem mapRight_erase (e : H ≃* K) (p : Position m G H) (i : Fin m) :
    mapRight e (erase p i) = erase (mapRight e p) i := by
  funext j
  by_cases h : j = i
  · subst j; simp only [mapRight, erase, Function.update_self, Option.map_none]
  · simp only [mapRight, erase, Function.update_of_ne h]

@[simp] theorem mapRight_place (e : H ≃* K) (p : Position m G H)
    (i : Fin m) (g : G) (h : H) :
    mapRight e (place p i g h) = place (mapRight e p) i g (e h) := by
  funext j
  by_cases hji : j = i
  · subst j; simp only [mapRight, place, Function.update_self, Option.map_some]
  · simp only [mapRight, place, Function.update_of_ne hji]

@[simp] theorem mapRight_empty (e : H ≃* K) :
    mapRight e (empty : Position m G H) = empty := rfl

@[simp] theorem mapRight_symm (e : H ≃* K) (p : Position m G H) :
    mapRight e.symm (mapRight e p) = p := by
  funext i
  cases hi : p i <;> simp [mapRight, hi]

theorem Atomic.mapRight (e : H ≃* K) {p : Position m G H} (hp : Atomic p) :
    Atomic (mapRight e p) := by
  obtain ⟨S, T, f, hf⟩ := hp
  refine ⟨S, T.map e.toMonoidHom, f.trans (e.subgroupMap T), ?_⟩
  intro i g h hm
  obtain ⟨hg, hh, he⟩ := hf i g (e.symm h) ((mapRight_some e p i g h).mp hm)
  have hmem : h ∈ T.map e.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨e.symm h, hh, e.apply_symm_apply h⟩
  refine ⟨hg, hmem, ?_⟩
  apply Subtype.ext
  change e (f ⟨g, hg⟩ : H) = h
  rw [he]
  exact e.apply_symm_apply h

theorem Winning.mapRight (e : H ≃* K) {p : Position m G H} (hp : Winning p) :
    Winning (mapRight e p) := by
  refine ⟨fun q => ∃ r, Winning r ∧ q = PebbleGame.mapRight e r, ⟨p, hp, rfl⟩, ?_⟩
  rintro q ⟨r, hr, rfl⟩ i
  obtain ⟨ha, f, hf⟩ := winning_step hr i
  refine ⟨?_, f.trans e.toEquiv, fun g => ⟨place r i g (f g), hf g, ?_⟩⟩
  · simpa only [mapRight_erase] using ha.mapRight e
  · exact (mapRight_place e r i g (f g)).symm

theorem winning_mapRight_iff (e : H ≃* K) (p : Position m G H) :
    Winning (mapRight e p) ↔ Winning p := by
  constructor
  · intro h
    simpa only [mapRight_symm] using h.mapRight e.symm
  · exact fun h => h.mapRight e

theorem Atomic.marked_equal {p : Position m G H} (hp : Atomic p)
    {i j : Fin m} {g : G} {h h' : H}
    (hi : p i = some (g, h)) (hj : p j = some (g, h')) : h = h' := by
  obtain ⟨S, T, e, he⟩ := hp
  obtain ⟨hg, hh, hi'⟩ := he i g h hi
  obtain ⟨hg', hh', hj'⟩ := he j g h' hj
  exact congrArg Subtype.val (hi'.symm.trans hj')

theorem Winning.marked_equal {p : Position m G H} (hp : Winning p)
    {i j : Fin m} {g : G} {h h' : H}
    (hi : p i = some (g, h)) (hj : p j = some (g, h'))
    (s : Fin m) (his : i ≠ s) (hjs : j ≠ s) : h = h' := by
  apply (winning_step hp s).1.marked_equal (i := i) (j := j)
  · simpa only [erase_ne _ _ _ his] using hi
  · simpa only [erase_ne _ _ _ hjs] using hj

end GroupWL.PebbleGame
