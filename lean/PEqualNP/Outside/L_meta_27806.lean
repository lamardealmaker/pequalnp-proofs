import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_27806

abbrev Sig (D : Type) := D → Bool

def read {D : Type} (a : List (Sig D)) (i : Nat) : Sig D := a.getD i (fun _ => false)

def app {D : Type} (op : GateOp) (xs : List (Sig D)) : Sig D :=
  fun z => op.eval (xs.map fun f => f z)

def value {D : Type} (g : Gate) (a : List (Sig D)) : Sig D :=
  app g.op (g.inputs.map (read a))

def run {D : Type} (a : List (Sig D)) : List Gate → List (Sig D)
  | [] => a
  | g :: gs => run (a ++ [value g a]) gs

lemma run_append {D : Type} (a : List (Sig D)) (gs hs : List Gate) :
    run a (gs ++ hs) = run (run a gs) hs := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => exact ih _

lemma run_extends {D : Type} (a : List (Sig D)) (gs : List Gate) :
    ∃ xs, run a gs = a ++ xs := by
  induction gs generalizing a with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨xs,h⟩ := ih (a ++ [value g a])
    exact ⟨value g a :: xs, by simpa [run, List.append_assoc] using h⟩

lemma map_run {D : Type} (a : List (Sig D)) (gs : List Gate) (z : D) :
    (run a gs).map (fun f => f z) =
      gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (a.map fun f => f z) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil]
    congr 3
    apply congrArg g.op.eval
    simp only [List.map_map, Function.comp_def, read]
    apply List.map_congr_left
    intro i _
    exact (List.getD_map a (fun _ : D => false) (fun f : Sig D => f z)).symm

def OK (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Known {D : Type} (a : List (Sig D)) (f : Sig D) : Prop := f ∈ a ∨ f = fun _ => false

lemma known_read {D : Type} (a : List (Sig D)) (i : Nat) : Known a (read a i) := by
  by_cases h : i < a.length
  · exact Or.inl (by rw [read,List.getD_eq_getElem a _ h]; exact List.getElem_mem ..)
  · exact Or.inr (List.getD_eq_default _ _ (by omega))

lemma index_of_known {D : Type} {a : List (Sig D)} {f : Sig D} (h : Known a f) :
    ∃ i, read a i = f := by
  rcases h with h | rfl
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    exact ⟨i.val, (List.getD_eq_get _ _ i).trans hi⟩
  · exact ⟨a.length, List.getD_eq_default _ _ (by omega)⟩

def Ext {D : Type} (a b : List (Sig D)) (cost : Nat) : Prop :=
  ∃ gs, run a gs = b ∧ gs.length ≤ cost ∧ ∀ g ∈ gs, OK g

lemma Ext.refl {D : Type} (a : List (Sig D)) : Ext a a 0 :=
  ⟨[], rfl, by simp, by simp⟩

lemma Ext.trans {D : Type} {a b c : List (Sig D)} {i j : Nat}
    (h : Ext a b i) (k : Ext b c j) : Ext a c (i+j) := by
  obtain ⟨xs,rfl,hx,ox⟩ := h
  obtain ⟨ys,rfl,hy,oy⟩ := k
  exact ⟨xs ++ ys, run_append .., by simpa using Nat.add_le_add hx hy,
    fun g hg => (List.mem_append.mp hg).elim (ox g) (oy g)⟩

lemma Ext.le {D : Type} {a b : List (Sig D)} {i j : Nat} (h : Ext a b i) (hij : i ≤ j) :
    Ext a b j := by
  obtain ⟨gs,hg,hl,ho⟩ := h
  exact ⟨gs,hg,hl.trans hij,ho⟩

lemma Ext.keep {D : Type} {a b : List (Sig D)} {c : Nat} (h : Ext a b c) {f : Sig D}
    (hf : Known a f) : Known b f := by
  obtain ⟨gs,rfl,_,_⟩ := h
  obtain ⟨xs,he⟩ := run_extends a gs
  rw [he]
  exact hf.imp (fun h => List.mem_append_left _ h) id

lemma encode_inputs {D : Type} (a : List (Sig D)) (xs : List (Sig D))
    (h : ∀ f ∈ xs, Known a f) : ∃ is : List Nat, is.map (read a) = xs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons f fs ih =>
    obtain ⟨i,hi⟩ := index_of_known (h f (by simp))
    obtain ⟨is,his⟩ := ih (fun v hv => h v (by simp [hv]))
    exact ⟨i :: is, by simp [hi,his]⟩

lemma emit {D : Type} (a : List (Sig D)) (op : GateOp) (xs : List (Sig D))
    (ho : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hl : xs.length ≤ 2)
    (hin : ∀ f ∈ xs, Known a f) :
    ∃ b, Ext a b 1 ∧ Known b (app op xs) := by
  obtain ⟨is,his⟩ := encode_inputs a xs hin
  let g : Gate := ⟨op,is⟩
  refine ⟨a ++ [value g a], ⟨[g],rfl,by simp,?_⟩, Or.inl ?_⟩
  · intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨ho,by simpa [← his] using hl⟩
  · simp [value,g,his]

def bor {D : Type} (f g : Sig D) : Sig D := fun z => f z || g z
def band {D : Type} (f g : Sig D) : Sig D := fun z => f z && g z

lemma emit_or {D : Type} {a : List (Sig D)} {f g : Sig D} (hf : Known a f) (hg : Known a g) :
    ∃ b, Ext a b 1 ∧ Known b (bor f g) := by
  have h := emit a .or [f,g] (by simp) (by simp) (by simpa using And.intro hf hg)
  have he : app .or [f,g] = bor f g := by funext z; simp [app,GateOp.eval,bor]
  rwa [he] at h

lemma emit_and {D : Type} {a : List (Sig D)} {f g : Sig D} (hf : Known a f) (hg : Known a g) :
    ∃ b, Ext a b 1 ∧ Known b (band f g) := by
  have h := emit a .and [f,g] (by simp) (by simp) (by simpa using And.intro hf hg)
  have he : app .and [f,g] = band f g := by funext z; simp [app,GateOp.eval,band]
  rwa [he] at h

def anySig {D I : Type} (fs : List I) (v : I → Sig D) : Sig D :=
  fun z => fs.any (fun i => v i z)

lemma make_any {D I : Type} (a : List (Sig D)) (v : I → Sig D) (fs : List I)
    (hn : fs ≠ []) (hv : ∀ i ∈ fs, Known a (v i)) :
    ∃ b, Ext a b (fs.length-1) ∧ Known b (anySig fs v) := by
  induction fs generalizing a with
  | nil => simp at hn
  | cons i is ih =>
    by_cases h : is = []
    · subst is
      refine ⟨a, Ext.refl a, ?_⟩
      have he : anySig [i] v = v i := by funext z; simp [anySig]
      rw [he]
      exact hv i (by simp)
    · obtain ⟨b,hab,hb⟩ := ih a h (fun j hj => hv j (by simp [hj]))
      obtain ⟨c,hbc,hc⟩ := emit_or (hab.keep (hv i (by simp))) hb
      have hl : 0 < is.length := List.length_pos_iff.mpr h
      exact ⟨c,(hab.trans hbc).le (by simp; omega),hc⟩

lemma make_pairs {D I : Type} (a : List (Sig D)) (fs : List I) (l r : I → Sig D)
    (hl : ∀ i ∈ fs, Known a (l i)) (hr : ∀ i ∈ fs, Known a (r i)) :
    ∃ b, Ext a b fs.length ∧ ∀ i ∈ fs, Known b (bor (l i) (r i)) := by
  induction fs generalizing a with
  | nil => exact ⟨a, Ext.refl a, by simp⟩
  | cons i is ih =>
    obtain ⟨b,hab,hb⟩ := ih a (fun j hj => hl j (by simp [hj])) (fun j hj => hr j (by simp [hj]))
    obtain ⟨c,hbc,hc⟩ := emit_or (hab.keep (hl i (by simp))) (hab.keep (hr i (by simp)))
    exact ⟨c, hab.trans hbc, by simpa using And.intro hc (fun j hj => hbc.keep (hb j hj))⟩

abbrev Dom (n m : Nat) := Fin n × Fin m
def left {n m : Nat} (i : Fin n) : Sig (Dom n m) := fun z => decide (i = z.1)
def right {n m : Nat} (j : Fin m) : Sig (Dom n m) := fun z => decide (j = z.2)
def raw (n m : Nat) : List (Sig (Dom n m)) := List.ofFn left ++ List.ofFn right

lemma raw_len (n m : Nat) : (raw n m).length = n+m := by simp [raw]
lemma raw_left {n m : Nat} (i : Fin n) : read (raw n m) i.val = left i := by
  rw [read,raw,List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp
lemma raw_right {n m : Nat} (i : Fin m) : read (raw n m) (n+i.val) = right i := by
  rw [read,raw,List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp
lemma raw_eval {n m : Nat} (z : Dom n m) :
    (raw n m).map (fun f => f z) = oneEach z.1 z.2 := by
  simp [raw,oneEach,List.map_ofFn,left,right,Function.comp_def]

def others {n k : Nat} (u : Fin n) (x : Fin k ↪ Fin n) : Finset (Fin n) :=
  Finset.univ \ insert u (Finset.univ.map x)

lemma others_card {n k : Nat} (u : Fin n) (x : Fin k ↪ Fin n) (h : ∀ i, x i ≠ u) :
    (others u x).card = n-(k+1) := by
  have hu : u ∉ Finset.univ.map x := by simpa using h
  rw [others, Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_insert_of_notMem hu]
  simp

def Covers {D : Type} (a b : List (Sig D)) : Prop := ∀ f ∈ a, Known b f

lemma Covers.read {D : Type} {a b : List (Sig D)} (h : Covers a b) (i : Nat) :
    Known b (L_meta_27806.read a i) :=
  (known_read a i).elim (h _) Or.inr

lemma Covers.extend {D : Type} {a b c : List (Sig D)} {t : Nat} {f : Sig D}
    (hc : Covers a b) (he : Ext b c t) (hf : Known c f) : Covers (a ++ [f]) c := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact he.keep (hc g h)
  · simpa only [List.mem_singleton.mp h] using hf

lemma simulate {D : Type} (gs : List Gate) (copy : Gate → Bool) (a b : List (Sig D))
    (hc : Covers a b) (hok : ∀ g ∈ gs, OK g)
    (cache : ∀ g ∈ gs, copy g = false → ∀ extra : List (Sig D), Known b (value g (a ++ extra))) :
    ∃ c, Ext b c (gs.filter copy).length ∧ Covers (run a gs) c := by
  induction gs generalizing a b with
  | nil => exact ⟨b, Ext.refl b, hc⟩
  | cons g gs ih =>
    have step : ∃ c, Ext b c (if copy g then 1 else 0) ∧ Known c (value g a) := by
      cases hg : copy g with
      | false => exact ⟨b,Ext.refl b,by simpa using cache g (by simp) hg []⟩
      | true =>
        have ho := hok g (by simp)
        simpa [value] using emit b g.op (g.inputs.map (read a)) ho.1 (by simpa using ho.2)
          (by simpa using fun i (_ : i ∈ g.inputs) => hc.read i)
    obtain ⟨c,he,hv⟩ := step
    obtain ⟨d,hd,hfinal⟩ := ih (a ++ [value g a]) c (hc.extend he hv)
      (fun t ht => hok t (by simp [ht])) (by
        intro t ht hcopy extra
        have h := cache t (by simp [ht]) hcopy (value g a :: extra)
        simpa [List.append_assoc] using he.keep h)
    refine ⟨d,(he.trans hd).le ?_,hfinal⟩
    cases hg : copy g <;> simp [hg,Nat.add_comm]

lemma read_ext {D : Type} (a extra : List (Sig D)) {i : Nat} (hi : i < a.length) :
    read (a ++ extra) i = read a i := List.getD_append a extra _ i hi

lemma point_read {D : Type} (a : List (Sig D)) (i : Nat) (z : D) :
    (a.map (fun f => f z)).getD i false = read a i z :=
  List.getD_map a (fun _ : D => false) (fun f : Sig D => f z)

lemma circuit_read {n m : Nat} (C : Circuit) (z : Dom n m) :
    read (run (raw n m) C.gates) C.output z = C.eval (oneEach z.1 z.2) := by
  rw [← point_read, map_run, raw_eval]
  rfl

def Below {D : Type} (z : D) (a b : List (Sig D)) : Prop :=
  a.length = b.length ∧ ∀ i, read a i z = true → read b i z = true

lemma Below.snoc {D : Type} {z : D} {a b : List (Sig D)} {f h : Sig D} (hab : Below z a b)
    (hf : f z = true → h z = true) : Below z (a ++ [f]) (b ++ [h]) := by
  refine ⟨by simp [hab.1],?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [read_ext _ _ hi,read_ext _ _ (hab.1 ▸ hi)]
    exact hab.2 i
  · rw [read,List.getD_append_right _ _ _ _ (by omega),read,List.getD_append_right _ _ _ _ (by have := hab.1; omega)]
    rw [← hab.1]
    cases i - a.length <;> simp [List.getD]
    exact hf

lemma value_mono {D : Type} {z : D} {a b : List (Sig D)} (hab : Below z a b) (g : Gate)
    (ho : g.op = .and ∨ g.op = .or) : value g a z = true → value g b z = true := by
  rcases ho with ho | ho
  · simp only [value,app,ho,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,
      and_imp,forall_apply_eq_imp_iff₂,id_eq]
    intro h i hi
    exact hab.2 i (h i hi)
  · simp only [value,app,ho,GateOp.eval,List.any_eq_true,List.mem_map,exists_exists_and_eq_and,id_eq]
    rintro ⟨i,hi,hv⟩
    exact ⟨i,hi,hab.2 i hv⟩

lemma run_below {D : Type} {z : D} (gs : List Gate) {a b : List (Sig D)} (hab : Below z a b)
    (ho : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) : Below z (run a gs) (run b gs) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    exact ih (hab.snoc (value_mono hab g (ho g (by simp)))) (fun t ht => ho t (by simp [ht]))

lemma run_point_eq {D : Type} {z : D} (gs : List Gate) {a b : List (Sig D)}
    (hab : a.map (fun f => f z) = b.map (fun f => f z)) (i : Nat) :
    read (run a gs) i z = read (run b gs) i z := by
  rw [← point_read,← point_read,map_run,map_run,hab]

def mix {n m k : Nat} (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) (i : Fin k) : Sig (Dom n m) :=
  bor (left (x i)) (right (y i))

def boost {n m k : Nat} (u : Fin n) (v : Fin m) (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) :
    Sig (Dom n m) := fun z =>
  decide ((∃ i, x i = z.1 ∨ y i = z.2) ∨ (u ≠ z.1 ∧ v ≠ z.2))

def sw {n m : Nat} (u : Fin n) (v : Fin m) : Sig (Dom n m) := bor (left u) (right v)

lemma boost_formula {n m k : Nat} (u : Fin n) (v : Fin m) (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) :
    bor (anySig (List.finRange k) (mix x y))
      (band (anySig (others u x).toList left) (anySig (others v y).toList right)) = boost u v x y := by
  classical
  funext z
  apply Bool.eq_iff_iff.mpr
  simp [bor,band,anySig,mix,left,right,others,boost,not_or]
  grind

lemma raw_knows_left {n m : Nat} (i : Fin n) : Known (raw n m) (left i) := by
  rw [← raw_left (m := m) i]
  exact known_read ..
lemma raw_knows_right {n m : Nat} (i : Fin m) : Known (raw n m) (right i) := by
  rw [← raw_right (n := n) i]
  exact known_read ..

lemma build_prefix {n m k : Nat} (u : Fin n) (v : Fin m) (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m)
    (hk : 1 ≤ k) (hn : k+2 ≤ n) (hm : k+2 ≤ m)
    (hx : ∀ i, x i ≠ u) (hy : ∀ i, y i ≠ v) :
    ∃ b, Ext (raw n m) b (n+m-2) ∧
      Covers (raw n m ++ [sw u v, boost u v x y]) b ∧ ∀ i, Known b (mix x y i) := by
  classical
  let L := (others u x).toList
  let R := (others v y).toList
  let I := List.finRange k
  have hL : L.length = n-(k+1) := by simp [L,others_card u x hx]
  have hR : R.length = m-(k+1) := by simp [R,others_card v y hy]
  have hI : I.length = k := by simp [I]
  have ni : I ≠ [] := by intro h; rw [h] at hI; simp at hI; omega
  have nl : L ≠ [] := by intro h; rw [h] at hL; simp at hL; omega
  have nr : R ≠ [] := by intro h; rw [h] at hR; simp at hR; omega
  obtain ⟨b1,e1,p⟩ := make_pairs (raw n m) I (fun i => left (x i)) (fun i => right (y i))
    (fun i _ => raw_knows_left _) (fun i _ => raw_knows_right _)
  have hp (i : Fin k) : Known b1 (mix x y i) := p i (by simp [I])
  obtain ⟨b2,e2,s⟩ := emit_or (e1.keep (raw_knows_left u)) (e1.keep (raw_knows_right v))
  obtain ⟨b3,e3,q⟩ := make_any b2 (mix x y) I ni (fun i _ => e2.keep (hp i))
  have t3 := (e1.trans e2).trans e3
  obtain ⟨b4,e4,l⟩ := make_any b3 left L nl (fun i _ => t3.keep (raw_knows_left i))
  obtain ⟨b5,e5,r⟩ := make_any b4 right R nr (fun i _ => (t3.trans e4).keep (raw_knows_right i))
  obtain ⟨b6,e6,t⟩ := emit_and (e5.keep l) r
  obtain ⟨b7,e7,f⟩ := emit_or (((e4.trans e5).trans e6).keep q) t
  have tail := ((((e3.trans e4).trans e5).trans e6).trans e7)
  have total := (e1.trans e2).trans tail
  refine ⟨b7,total.le (by omega),?_,fun i => (e2.trans tail).keep (hp i)⟩
  have hb : Known b7 (boost u v x y) := by rw [← boost_formula]; exact f
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact total.keep (Or.inl h)
  · rcases List.mem_cons.mp h with h | h
    · subst g; exact tail.keep s
    · simpa only [List.mem_singleton.mp h] using hb

def pairGate {n m : Nat} (i : Fin n) (j : Fin m) : Gate := ⟨.or,[i.val,n+j.val]⟩
def negGate (n m : Nat) : Gate := ⟨.not,[n+m]⟩

lemma pair_value {n m : Nat} (i : Fin n) (j : Fin m) (extra : List (Sig (Dom n m))) :
    value (pairGate i j) (raw n m ++ extra) = sw i j := by
  have hl : i.val < (raw n m).length := by rw [raw_len]; omega
  have hr : n+j.val < (raw n m).length := by rw [raw_len]; omega
  change app .or [read (raw n m ++ extra) i.val,read (raw n m ++ extra) (n+j.val)] = _
  rw [read_ext _ _ hl,read_ext _ _ hr,raw_left,raw_right]
  funext z
  simp [app,GateOp.eval,sw,bor]

lemma first_two {T : Type} (xs : List T) (a b : T) (h0 : xs[0]? = some a)
    (h1 : xs[1]? = some b) : xs = a :: b :: xs.drop 2 := by
  cases xs with
  | nil => simp at h0
  | cons t ts =>
    cases ts with
    | nil => simp at h1
    | cons z zs => simp_all

lemma original_start {n m : Nat} (u : Fin n) (v : Fin m) :
    run (raw n m) [pairGate u v, negGate n m] =
      raw n m ++ [sw u v, fun z => !(sw u v z)] := by
  have hp : value (pairGate u v) (raw n m) = sw u v := by simpa using pair_value u v []
  have hr : read (raw n m ++ [sw u v]) (n+m) = sw u v := by
    rw [read,List.getD_append_right _ _ _ _ (by rw [raw_len]),raw_len,Nat.sub_self]
    rfl
  simp only [run,hp,List.append_assoc,List.singleton_append]
  congr 3
  change app .not [read (raw n m ++ [sw u v]) (n+m)] = _
  rw [hr]
  rfl

lemma old_below {n m k : Nat} (u : Fin n) (v : Fin m) (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m)
    (z : Dom n m) : (!(sw u v z)) = true → boost u v x y z = true := by
  simp [sw,bor,left,right,boost]
  tauto

lemma old_eq_on_reject {n m k : Nat} (A : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m)
    (hgood : ∀ i, x i ≠ u ∧ y i ≠ v ∧ A (x i) v = true ∧ A u (y i) = true)
    (z : Dom n m) (ha : A z.1 z.2 ≠ true) : (!(sw u v z)) = boost u v x y z := by
  apply Bool.eq_iff_iff.mpr
  simp [sw,bor,left,right,boost]
  rintro i (hi | hi)
  · have hh := hgood i
    exact ⟨by grind,by intro h; exact ha (by simpa [hi,h] using hh.2.2.1)⟩
  · have hh := hgood i
    exact ⟨by intro h; exact ha (by simpa [hi,h] using hh.2.2.2),by grind⟩

lemma replace_read {n m k : Nat} (A : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) (gs : List Gate) (o : Nat)
    (hgood : ∀ i, x i ≠ u ∧ y i ≠ v ∧ A (x i) v = true ∧ A u (y i) = true)
    (ho : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (z : Dom n m)
    (hc : read (run (raw n m ++ [sw u v, fun t => !(sw u v t)]) gs) o z = A z.1 z.2) :
    read (run (raw n m ++ [sw u v, boost u v x y]) gs) o z = A z.1 z.2 := by
  let p := raw n m ++ [sw u v]
  by_cases ha : A z.1 z.2 = true
  · have refl : Below z p p := ⟨rfl,fun _ h => h⟩
    have hv := run_below gs (refl.snoc (f := fun t => !(sw u v t)) (h := boost u v x y)
      (old_below u v x y z)) ho
    simp only [p,List.append_assoc,List.singleton_append] at hv
    rw [ha]
    exact hv.2 o (hc.trans ha)
  · have h := old_eq_on_reject A u v x y hgood z ha
    refine Eq.trans (run_point_eq gs ?_ o) hc
    simp [h]

lemma pair_inj {n m k : Nat} (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) :
    Function.Injective (fun i => pairGate (x i) (y i)) := by
  intro i j he
  apply x.injective
  apply Fin.ext
  exact congrArg (fun g : Gate => g.inputs.headD 0) he

lemma skipped_bound {T : Type} [DecidableEq T] (xs : List T) (S : Finset T)
    (h : ∀ s ∈ S, s ∈ xs) :
    (xs.filter (fun t => decide (t ∉ S))).length + S.card ≤ xs.length := by
  have hin : S ⊆ (xs.filter (fun t => decide (t ∈ S))).toFinset := by
    intro s hs
    simp [h s hs,hs]
  have hb := (Finset.card_le_card hin).trans (List.toFinset_card_le _)
  have hc (l : List T) : (l.filter (fun t => decide (t ∉ S))).length +
      (l.filter (fun t => decide (t ∈ S))).length = l.length := by
    induction l with
    | nil => rfl
    | cons t ts ih =>
      by_cases ht : t ∈ S <;> simp [ht] at ih ⊢ <;> omega
  have := hc xs
  omega

end PEqualNP.Outside.L_meta_27806

open PEqualNP.Outside.L_meta_27806

theorem PEqualNP.Outside.L_meta_27806 : ∀ (n m k : Nat) (A : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit),
  1 ≤ k → k+2 ≤ n → k+2 ≤ m →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
  PEqualNP.Represents.Represents A C →
  C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [u.val,n+v.val]⟩ →
  C.gates[1]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [n+m]⟩ →
  (∀ g ∈ C.gates.drop 2, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  (∀ h, x h ≠ u ∧ y h ≠ v ∧ A (x h) v = true ∧ A u (y h) = true ∧
    ∃ g ∈ C.gates.drop 2, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs = [(x h).val,n+(y h).val]) →
  PEqualNP.Represents.RepSizeAtMost A (C.size + (n+m-(4+k))) := by
  classical
  intro n m k A u v x y C hk hn hm hfan _ hrep h0 h1 hpos hsel
  let gs := C.gates.drop 2
  have hgs : C.gates = pairGate u v :: negGate n m :: gs :=
    first_two C.gates _ _ h0 h1
  have good (i : Fin k) : x i ≠ u ∧ y i ≠ v ∧ A (x i) v = true ∧ A u (y i) = true :=
    ⟨(hsel i).1,(hsel i).2.1,(hsel i).2.2.1,(hsel i).2.2.2.1⟩
  obtain ⟨b,hpre,hcov,hpairs⟩ := build_prefix u v x y hk hn hm
    (fun i => (good i).1) (fun i => (good i).2.1)
  let tag := fun i : Fin k => pairGate (x i) (y i)
  let S : Finset Gate := Finset.univ.image tag
  have hcard : S.card = k := by
    rw [show S = Finset.univ.image tag from rfl,Finset.card_image_of_injective _ (pair_inj x y)]
    simp
  have htags : ∀ t ∈ S, t ∈ gs := by
    intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨g,hg,ho,hi⟩ := (hsel i).2.2.2.2
    have he : g = tag i := by cases g; simp_all [tag,pairGate]
    exact he ▸ hg
  let copy := fun t : Gate => decide (t ∉ S)
  have hsize : (gs.filter copy).length + k ≤ gs.length := by
    rw [← hcard]
    exact skipped_bound gs S htags
  let a := raw n m ++ [sw u v,boost u v x y]
  have ok : ∀ t ∈ gs, OK t := by
    intro t ht
    have hg : t ∈ C.gates := by rw [hgs]; simp [ht]
    exact ⟨(hpos t ht).elim (fun h => by simp [h]) (fun h => by simp [h]),(hfan t hg).2⟩
  have cache : ∀ t ∈ gs, copy t = false → ∀ extra : List (Sig (Dom n m)), Known b (value t (a ++ extra)) := by
    intro t _ ht extra
    have hmbr : t ∈ S := by simpa [copy] using ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hmbr
    change Known b (value (pairGate (x i) (y i)) ((raw n m ++ _) ++ extra))
    rw [List.append_assoc,pair_value]
    exact hpairs i
  obtain ⟨c,hprog,hc⟩ := simulate gs copy a b hcov ok cache
  obtain ⟨w,hw⟩ := index_of_known (hc.read C.output)
  obtain ⟨ts,ht,htlen,htok⟩ := hpre.trans hprog
  let newC : Circuit := ⟨ts,w⟩
  refine ⟨newC,htok,?_,?_⟩
  · have hlen : C.size = gs.length + 2 := by
      change C.gates.length = _
      rw [hgs]
      simp
    change ts.length ≤ _
    omega
  · intro i j
    let z : Dom n m := (i,j)
    have horig : read (run (raw n m ++ [sw u v,fun t => !(sw u v t)]) gs) C.output z = A i j := by
      have h : read (run (raw n m) C.gates) C.output z = A i j :=
        (circuit_read C z).trans (hrep i j)
      have he : C.gates = [pairGate u v,negGate n m] ++ gs := hgs
      rwa [he,run_append,original_start] at h
    have heval := replace_read A u v x y gs C.output good hpos z horig
    calc
      newC.eval (oneEach i j) = read (run (raw n m) ts) w z := (circuit_read newC z).symm
      _ = A i j := by rw [ht,hw]; exact heval
