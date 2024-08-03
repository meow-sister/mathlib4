import Batteries.Data.List.Pairwise
import Mathlib.Data.List.Infix
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

noncomputable section
open scoped List
local notation "‖" X "‖" => Fintype.card X

namespace List

@[simp] theorem getElem_reverse' {α} (l : List α) (i : Nat) (h1 h2) :
    (reverse l)[i]'h1 = l[length l - 1 - i]'h2 := by
  have := getElem_reverse l (length l - 1 -i) (by omega) (by omega)
  rw [← this]; congr; simp at h1; omega

theorem reverse_tail {α} (l : List α) : l.reverse.tail = l.dropLast.reverse := by
  ext i v; by_cases hi : i < l.length - 1
  · simp only [← drop_one]
    rw [getElem?_eq_getElem (by simpa), getElem?_eq_getElem (by simpa),
      ← getElem_drop _, getElem_reverse', getElem_reverse', getElem_dropLast]
    simp [show l.length - 1 - (1 + i) = l.length - 1 - 1 - i by omega]
    simp; omega; simp; omega; omega
  · rw [getElem?_eq_none, getElem?_eq_none]; simp; omega; simp; omega

theorem getLast_tail {α} (l : List α) (hl : l.tail ≠ [])
  : l.tail.getLast hl = l.getLast (by intro h; rw [h] at hl; simp at hl) := by
  simp [getLast_eq_get, ← drop_one] at hl |-; rw [← getElem_drop]
  simp [show 1 + (l.length - 1 - 1) = l.length - 1 by omega]; omega
end List

namespace SimpleGraph
open Classical
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace Walk
def fromList {l : List V} (ne : l ≠ []) (hl : l.Chain' (fun u v => G.Adj u v))
  : G.Walk (l.head ne) (l.getLast ne) :=
  match l with
  | [] => by simp at ne
  | a :: l' =>
    if h : l' = [] then
      (nil : G.Walk a a).copy (by simp) (by simp [h])
    else cons
      (show G.Adj a (l'.head h) by
        rw [List.chain'_cons'] at hl; apply hl.1; simp [List.head?_eq_head _ h])
      (fromList h
        (by rw [List.chain'_cons'] at hl; exact hl.2) |>.copy rfl
        (by conv_lhs =>
          simp (config := {singlePass := true}) only [← List.tail_cons (a := a) (as := l')]
          rw [List.getLast_tail]))

def fromList_support {l : List V} (ne : l ≠ []) (hl : l.Chain' (fun u v => G.Adj u v))
  : (fromList ne hl).support = l := by
  induction l with
  | nil => simp at ne
  | cons a l' ih =>
    simp [fromList]; split_ifs with l'_ne
    · simp [l'_ne]
    · simp; exact ih l'_ne _

@[simp] lemma support_tail' {u v} (p : G.Walk u v) (hp) :
    (p.tail hp).support = p.support.tail := by
  rw [← cons_support_tail p hp, List.tail_cons]

@[simp]
theorem tail_support_ne_nil {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) : p.support.tail ≠ [] :=
  by cases p <;> simp at hp |-

def firstDart_mem_darts {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
  : p.firstDart hp ∈ p.darts := by
  induction p <;> simp [Walk.firstDart, Walk.sndOfNotNil, Walk.notNilRec] at hp |-

def lm03 {α} (L : List α) (hL : L ≠ []) : (L.getLast hL :: L.dropLast) ~r L := by
  induction L using List.reverseRecOn with
  | nil => simp at hL
  | append_singleton a L _ =>
    simp; apply List.IsRotated.symm; apply List.isRotated_concat

def lm05 {α} {L : List α} (hL : L ≠ []) (hL' : L.head hL = L.getLast hL) : L.dropLast ~r L.tail :=
  match L with
  | [] => by simp
  | [_] => by simp
  | a :: b :: L => by simp at hL' |-; rw [hL']; apply lm03

@[simp] def support_head {u v : V} {p : G.Walk u v} : p.support.head (by simp) = u :=
  by induction p <;> simp

theorem head_reverse {α} (l : List α) (hL : l ≠ []) :
    l.reverse.head (by simpa) = l.getLast hL := by
  have : l.reverse.head? = l.getLast? := by simp
  rw [List.head?_eq_head (l := l.reverse) (by simpa)] at this
  rw [List.getLast?_eq_getLast (l := l) hL] at this
  exact Option.some_inj.mp this

@[simp] def support_getLast {u v : V} {p : G.Walk u v} : p.support.getLast (by simp) = v := by
  have : p.support.getLast (by simp) = p.reverse.support.head (by simp) := by simp [head_reverse]
  simp only [support_head, this]

def IsCycle.IsRotated_dropLast_tail {u : V} {c : G.Walk u u} (_ : IsCycle c) :
    c.support.dropLast ~r c.support.tail := by
  apply lm05 (show c.support ≠ [] by simp); simp

@[simp] def rotate_length_eq {u v : V} {c : G.Walk u u} (hv : v ∈ c.support)
  : (c.rotate hv).length = c.length := by
  have : (c.rotate hv).edges ~r c.edges := by apply rotate_edges
  simp only [← length_edges]; exact this.perm.length_eq

def rotate_Nil_iff {u v : V} {c : G.Walk u u} (hv : v ∈ c.support) :
    (c.rotate hv).Nil ↔ c.Nil := by
  simp only [nil_iff_length_eq, rotate_length_eq hv]

def IsCycle.support_dropLast_Nodup {u : V} {c : G.Walk u u} (qc : IsCycle c) :
    c.support.dropLast.Nodup := by
  rw [List.IsRotated.nodup_iff qc.IsRotated_dropLast_tail]
  exact qc.2

def prev_unique {u v : V} {c : G.Walk u v} {d₁ d₂ : G.Dart} (nodup : c.support.tail.Nodup)
    (hd₁ : d₁ ∈ c.darts) (hd₂ : d₂ ∈ c.darts) (eq : d₁.snd = d₂.snd)
  : d₁.fst = d₂.fst := by
  by_contra h
  have ne : d₁ ≠ d₂ := by contrapose h; simp at h |-; congr
  exact ne $ List.inj_on_of_nodup_map (c.map_snd_darts ▸ nodup) hd₁ hd₂ eq

def next_unique {u v : V} {c : G.Walk u v} {d₁ d₂ : G.Dart} (nodup : c.support.dropLast.Nodup)
    (hd₁ : d₁ ∈ c.darts) (hd₂ : d₂ ∈ c.darts) (eq : d₁.fst = d₂.fst)
  : d₁.snd = d₂.snd := by
  by_contra h
  have ne : d₁ ≠ d₂ := by contrapose h; simp at h |-; congr
  exact ne $ List.inj_on_of_nodup_map (c.map_fst_darts ▸ nodup) hd₁ hd₂ eq

def IsCycle.prev_unique {u : V} {c : G.Walk u u} {d₁ d₂ : G.Dart} (qc : IsCycle c)
    (hd₁ : d₁ ∈ c.darts) (hd₂ : d₂ ∈ c.darts) (eq : d₁.snd = d₂.snd)
  : d₁.fst = d₂.fst := c.prev_unique qc.2 hd₁ hd₂ eq

def IsCycle.next_unique {u : V} {c : G.Walk u u} {d₁ d₂ : G.Dart} (qc : IsCycle c)
    (hd₁ : d₁ ∈ c.darts) (hd₂ : d₂ ∈ c.darts) (eq : d₁.fst = d₂.fst)
  : d₁.snd = d₂.snd := c.next_unique qc.support_dropLast_Nodup hd₁ hd₂ eq

lemma sum_takeUntil_dropUntil_length {u v w : V} {p : G.Walk u v} (hw : w ∈ p.support)
  : (p.takeUntil w hw).length + (p.dropUntil w hw).length = p.length := by
  have := congr_arg (·.length) (p.take_spec hw)
  simpa only [length_append] using this

theorem darts_snd_getElem_support_tail
    {u v : V} {p : G.Walk u v} (i : ℕ) (h : i < p.length)
  : (p.darts[i]'(by simpa)).snd = p.support.tail[i]'(by simpa) := by
  simp [←p.map_snd_darts]

theorem darts_getElem_fst
    {u v : V} {p : G.Walk u v} (i : ℕ) (hi : i < p.length)
  : (p.darts[i]'(by simpa)).fst = p.support[i]'(by simp; omega) := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons u' v' w' adj tail ih =>
    simp at hi; by_cases h : i = 0
    · subst h; simp
    · simp (config := {singlePass := true}) [show i = i - 1 + 1 by omega]
      exact ih (i - 1) (by omega)

theorem darts_getElem_snd
    {u v : V} {p : G.Walk u v} (i : ℕ) (h : i < p.length)
  : (p.darts[i]'(by simpa)).snd = p.support[i + 1]'(by simpa) := by
  rw [darts_snd_getElem_support_tail i h]; simp only [← List.drop_one]
  rw [← List.getElem_drop]; congr 1; rw [add_comm]; simp; omega

namespace IsHamiltonianCycle
variable {v : V} {c : G.Walk v v} (qc : c.IsHamiltonianCycle)

protected theorem transfer {H} (hq) : (c.transfer H hq).IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at *
  refine And.intro (qc.1.transfer _) (fun a => ?_)
  simp only [support_transfer]
  exact qc.2 a

protected theorem rotate (u) : IsHamiltonianCycle (c.rotate (qc.mem_support u)) := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at *
  refine And.intro ?_ (fun a => ?_)
  apply qc.1.rotate; rw [← qc.2 a]
  exact List.perm_iff_count.mp (List.IsRotated.perm (by simp)) a

def mem_tail_support (u : V) : u ∈ c.support.tail := by
  rw [← List.count_pos_iff_mem]; have := qc.2 u; simp at this; omega

def mem_dropLast_support  (u : V) : u ∈ c.support.dropLast := by
  rw [List.IsRotated.mem_iff (IsCycle.IsRotated_dropLast_tail qc.1)]
  apply qc.mem_tail_support

def dart_with_fst (u : V) : G.Dart :=
  Exists.choose <| show ∃d ∈ c.darts, d.fst = u by
    simpa [← Walk.map_fst_darts] using qc.mem_dropLast_support u

def dart_with_snd (u : V) : G.Dart :=
  Exists.choose <| show ∃d ∈ c.darts, d.snd = u by
    simpa [← Walk.map_snd_darts] using qc.mem_tail_support u

protected def next (u : V) := (qc.dart_with_fst u).snd
protected def prev (u : V) := (qc.dart_with_snd u).fst

def prev_self_in_darts (u : V) : ∃ d ∈ c.darts, d.fst = qc.prev u ∧ d.snd = u := by
  unfold IsHamiltonianCycle.prev dart_with_snd
  generalize_proofs hd; have := hd.choose_spec; set d := hd.choose
  use d; simpa using this

def self_next_in_darts (u : V) : ∃ d ∈ c.darts, d.fst = u ∧ d.snd = qc.next u := by
  unfold IsHamiltonianCycle.next dart_with_fst
  generalize_proofs hd; have := hd.choose_spec; set d := hd.choose
  use d; simpa using this

def Adj_prev_self (u : V) : G.Adj (qc.prev u) u := by
  obtain ⟨d, _, hd'⟩ := qc.prev_self_in_darts u
  exact hd'.1 ▸ hd'.2 ▸ d.adj

def Adj_self_next (u : V) : G.Adj u (qc.next u) := by
  obtain ⟨d, _, hd'⟩ := qc.self_next_in_darts u
  exact hd'.2 ▸ hd'.1 ▸ d.adj

@[simp] def prev_next (u : V) : qc.prev (qc.next u) = u := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := qc.prev_self_in_darts (qc.next u)
  obtain ⟨d₂, hd₂, hd₂'⟩ := qc.self_next_in_darts u
  rw [← hd₁'.1, ← hd₂'.1]; rw [← hd₂'.2] at hd₁'
  exact qc.1.prev_unique hd₁ hd₂ hd₁'.2

@[simp] def next_prev (u : V) : qc.next (qc.prev u) = u := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := qc.self_next_in_darts (qc.prev u)
  obtain ⟨d₂, hd₂, hd₂'⟩ := qc.prev_self_in_darts u
  rw [← hd₁'.2, ← hd₂'.2]; rw [← hd₂'.1] at hd₁'
  exact qc.1.next_unique hd₁ hd₂ hd₁'.1

def rotate_next (u' u : V) : (qc.rotate u').next u = qc.next u := by
  unfold IsHamiltonianCycle.next dart_with_fst
  congr; ext d; apply Iff.and
  rw [List.IsRotated.mem_iff (c.rotate_darts _)]; apply Iff.rfl

def next_inj : Function.Injective qc.next := by
  intro v₁ v₂ eq; apply_fun qc.prev at eq; simpa using eq

theorem next_ne {u : V} : qc.next u ≠ u := by
  intro h; exact G.irrefl (h ▸ qc.Adj_self_next u)

def support_index_succ {u : V} {i : ℕ}
    (hi : i < c.length) (hi' : c.support[i]'(by simp; omega) = u)
  : c.support[i + 1]'(by simp; omega) = qc.next u := by
  have mem := List.getElem_mem c.darts i (by simpa)
  obtain ⟨d, mem', hd₂, hd₃⟩ := qc.self_next_in_darts u
  rw [← hi', ← c.darts_getElem_fst i hi] at hd₂
  rw [← c.darts_getElem_snd i hi, ← hd₃]
  exact qc.isCycle.next_unique mem mem' hd₂.symm

theorem next_next_ne {u : V} : qc.next (qc.next u) ≠ u := by
  have mem : u ∈ c.support := by apply qc.mem_support
  let c' := c.rotate mem
  have qc' : c'.IsHamiltonianCycle := qc.rotate u
  have len_ge_3 := qc'.isCycle.three_le_length
  have c'_at_0 : c'.support[0] = u := by simp [List.getElem_zero]
  have c'_at_1 : c'.support[1]'(by simp; omega) = qc'.next u :=
    qc'.support_index_succ (i := 0) (by omega) c'_at_0
  have c'_at_2 : c'.support[2]'(by simp; omega) = qc'.next (qc'.next u) :=
    qc'.support_index_succ (i := 1) (by omega) c'_at_1
  simp only [← qc.rotate_next u]
  intro h; change qc'.next (qc'.next u) = u at h
  simp_rw [← c'_at_2, ← c'_at_0] at h
  rw [← List.getElem_dropLast _ 2 (by simp; omega)] at h
  rw [← List.getElem_dropLast _ 0 (by simp; omega)] at h
  rw [List.Nodup.getElem_inj_iff qc'.support_dropLast_Nodup] at h
  simp at h

end IsHamiltonianCycle
end Walk

variable (G)

def closureNewEdges :=
  { (u, v) : V × V | G.degree u + G.degree v ≥ ‖V‖ ∧ u ≠ v ∧ ¬G.Adj u v }

def closureStep : SimpleGraph V :=
  if h : (closureNewEdges G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else
    G

def closureStep_diff_atmost_one : (closureStep G \ G).edgeSet.Subsingleton := by
  unfold closureStep
  split_ifs with h
  · simp
    apply Set.Subsingleton.anti (t := (edge h.some.1 h.some.2).edgeSet)
    · have : h.some.1 ≠ h.some.2 := h.some_mem.2.1
      simp [edge_edgeSet_of_ne (this)]
    · apply Set.diff_subset
  · simp

def closureStep_ge_self : G ≤ closureStep G := by
  unfold closureStep; split_ifs with h; simp; simp

def closureStep_deleteEdge {u v : V} (huv : ¬G.Adj u v) (huv' : G.closureStep.Adj u v)
  : G.closureStep.deleteEdges {s(u, v)} = G := by
  rw [← edgeSet_inj]; ext e; simp [edgeSet_deleteEdges]
  apply Iff.intro
  · rintro ⟨he₁, he₂⟩; by_contra he₃
    have mem₁ : e ∈ (closureStep G \ G).edgeSet := by simpa using ⟨he₁, he₃⟩
    have mem₂ : s(u, v) ∈ (closureStep G \ G).edgeSet := by simpa using ⟨huv', huv⟩
    exact he₂ $ (closureStep_diff_atmost_one G) mem₁ mem₂
  · intro he; apply And.intro (edgeSet_mono (closureStep_ge_self G) he)
    intro he'; simp [he'] at he; exact huv he

def closureStep_eq_iff' : closureStep G = G ↔ closureNewEdges G = ∅ := by
  unfold closureStep
  split_ifs with h
  · have : (G ⊔ edge h.some.1 h.some.2 = G) ↔ False := by
      simp [← isSubgraph_eq_le, IsSubgraph]
      use h.some.1, h.some.2
      simp [edge_adj]
      exact h.some_mem.2
    simp only [this, false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h

def closureStep_eq_iff : closureStep G = G ↔
    ∀ {u} {v}, u ≠ v → G.degree u + G.degree v ≥ ‖V‖ → G.Adj u v := by
  simp only [closureStep_eq_iff', closureNewEdges,
    Set.eq_empty_iff_forall_not_mem, Set.mem_setOf, Prod.forall]
  apply forall₂_congr; intros; tauto

def closureStep_deg_sum {u v : V} (huv : ¬G.Adj u v) (huv' : G.closureStep.Adj u v)
  : G.degree u + G.degree v ≥ ‖V‖ := by
  have ne : (closureNewEdges G).Nonempty := by
    by_contra h; simp [Set.nonempty_iff_ne_empty, ← closureStep_eq_iff'] at h
    rw [h] at huv'; exact huv huv'
  let w := ne.some
  have prop₁ : G.degree w.1 + G.degree w.2 ≥ ‖V‖ := ne.some_mem.1
  have mem₁ : s(u, v) ∈ (closureStep G \ G).edgeSet := by simp; exact ⟨huv', huv⟩
  have mem₂ : s(w.1, w.2) ∈ (closureStep G \ G).edgeSet := by
    have prop₂ : w.1 ≠ w.2 := ne.some_mem.2.1
    have prop₃ : ¬G.Adj w.1 w.2 := ne.some_mem.2.2
    have G_eq : G.closureStep = G ⊔ edge w.1 w.2 := by unfold closureStep; simp[ne]
    simp [-Prod.mk.eta, G_eq, edge_adj]
    exact And.intro prop₂ prop₃
  have edge_eq := (closureStep_diff_atmost_one G mem₁ mem₂).symm
  simp at edge_eq; cases' edge_eq with h h
  · rw [h] at prop₁; simpa using prop₁
  · rw [h] at prop₁; rw [add_comm]; simpa using prop₁

section Iterate
variable {α : Type*} [PartialOrder α] [Fintype α] {f : α → α} (hf : ∀ x, x ≤ f x)

lemma iterate_trivial {x : α} (hx : f x = x) (n : ℕ) : f^[n] x = x := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [add_comm, Function.iterate_add_apply]
    simp [ih, hx]

lemma iterate_trivial_from
    {m} {x : α} (hx : f^[m + 1] x = f^[m] x) {n : ℕ} (hn : n ≥ m) : f^[n] x = f^[m] x := by
  rw [add_comm, Function.iterate_add_apply] at hx
  rw [show n = n - m + m by omega, Function.iterate_add_apply]
  apply iterate_trivial hx

lemma monotone_iterate (x : α) : Monotone (fun n => f^[n] x) := by
  intro i j le; simp
  induction j with
  | zero => simp at le; rw [le]
  | succ k ih =>
    replace le : i ≤ k ∨ i = k + 1 := by omega
    cases' le with le le
    · rw [add_comm, Function.iterate_add_apply _ 1 k]
      exact (ih le).trans (hf _)
    · rw [le]

lemma eventually_constant_iterate (x : α)
  : ∃ n, ∀ m ≥ n, f^[m] x = f^[n] x := by
  obtain ⟨m, n, h₁, h₂⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => f^[n] x)
  use min m n; intro n' hn';
  have eq : f^[min m n] x = f^[min m n + 1] x := by
    have ineq₁ : f^[min m n] x ≤ f^[min m n + 1] x := by
      apply monotone_iterate hf; simp
    have ineq₂ : f^[min m n + 1] x ≤ f^[max m n] x := by
      apply monotone_iterate hf; simp; omega
    replace h₂ : f^[min m n] x = f^[max m n] x := by
      by_cases h : m <= n
      · simpa [h]
      · replace h : n ≤ m := by omega
        simp [h]; exact h₂.symm
    exact le_antisymm ineq₁ (h₂ ▸ ineq₂)
  exact iterate_trivial_from eq.symm hn'

def stop_index (x : α) : ℕ := (eventually_constant_iterate hf x).choose

def stop_index_spec (x : α)
  : ∀ m ≥ stop_index hf x, f^[m] x = f^[stop_index hf x] x :=
  (eventually_constant_iterate hf x).choose_spec

def eventuallyConstant (x : α) := f^[stop_index hf x] x

lemma func_eventuallyConstant (x : α)
  : f (eventuallyConstant hf x) = eventuallyConstant hf x := by
  simp only [eventuallyConstant, ← Function.iterate_succ_apply']
  apply stop_index_spec; simp

lemma self_le_eventuallyConstant (x : α) : x ≤ eventuallyConstant hf x := by
  simp only [eventuallyConstant]
  conv_lhs => rw [show x = f^[0] x from rfl]
  apply monotone_iterate hf; simp

def closure := eventuallyConstant closureStep_ge_self G
lemma self_le_closure : G ≤ closure G := by rw [closure]; apply self_le_eventuallyConstant

lemma closure_spec : ∀ {u} {v}, u ≠ v →
    G.closure.degree u + G.closure.degree v ≥ ‖V‖ → G.closure.Adj u v := by
  have : closureStep (closure G) = closure G := func_eventuallyConstant closureStep_ge_self G
  rwa [closureStep_eq_iff] at this

end Iterate

namespace IsHamiltonian
variable {G}

lemma _root_.List.tail_get {α} {i} (L : List α) (hi : i < L.tail.length) :
    L.tail[i] = L[i + 1]'(by simp at *; omega) := by
  induction L <;> simp at hi |-

lemma lm1 {u v} {p : G.Walk u v} {i} (hi : i < p.length + 1) :
    p.support[i]'(by simpa using hi) = p.getVert i := by
  induction p generalizing i with
  | nil => simp [Walk.getVert]
  | cons v p' ih =>
    cases' i with j; simp
    simp [Walk.getVert] at hi |-; exact ih (by omega)

lemma lm2 {u v} {p : G.Walk u v} (hi : 0 < p.length) :
    (p.darts[0]'(by simp; omega)).fst = u := by
  induction p with
  | nil => simp at hi
  | @cons u' v' w' adj tail _ => simp

lemma lm4 {u v} (p : G.Walk u v) (i : ℕ) (hi : 0 < i ∧ i < p.length) :
    (p.darts[i]'(by simp; omega)).fst = p.support.tail[i - 1]'(by simp; omega) := by
  simp only [← List.drop_one]; rw [← List.getElem_drop, p.darts_getElem_fst]
  simp only [show 1 + (i - 1) = i by omega]; exact hi.2; simp; omega

private theorem thm1
    {u : V} {p : G.Walk u u} (hp : p.length ≥ 3) (hp' : ∀ (a : V), List.count a p.support.tail = 1)
  : p.IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine And.intro ?_ hp'
  apply And.intro
  · rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij
    unfold Walk.edges;
    have nodup : p.support.tail.Nodup := by
      rw [List.nodup_iff_count_le_one]; intro a; exact le_of_eq (hp' a)
    rw [List.Nodup, List.pairwise_iff_getElem] at nodup
    have h₁ : i < p.length := by simpa using hi
    have h₂ : j < p.length := by simpa using hj
    have h₃ : i < p.darts.length := by simpa using hi
    have h₄ : j < p.darts.length := by simpa using hj
    have h₅ : i < p.support.tail.length := by simpa using hi
    have h₆ : j < p.support.tail.length := by simpa using hj
    simp at hi
    simp [dart_edge_eq_iff]
    apply And.intro
    · have h₇ := p.darts_snd_getElem_support_tail i h₁
      have h₈ := p.darts_snd_getElem_support_tail j h₂
      suffices p.darts[i].snd ≠ p.darts[j].snd by contrapose this; simp at this |-; congr
      simp only [h₇, h₈]; exact nodup i j h₅ h₆ hij
    · intro h
      by_cases ij : i + 1 < j
      · apply_fun (·.snd) at h; simp at h
        rw [p.darts_snd_getElem_support_tail i h₁, lm4 p j (by omega)] at h
        exact nodup i (j - 1) h₅ (by omega) (by omega) h
      · apply_fun (·.fst) at h
        by_cases i0 : i = 0
        · simp only [i0, lm2 (show 0 < p.length by omega)] at h
          have : p.support.tail[p.length - 1]'(by simp; omega) = u := by
            simp [List.tail_get, show p.length - 1 + 1 = p.length by omega, lm1]
          simp [← this, p.darts_snd_getElem_support_tail j h₂] at h
          exact nodup j (p.length - 1) h₆ (by simp; omega) (by omega) h.symm
        · simp [lm4 p i (by omega), p.darts_snd_getElem_support_tail j h₂] at h
          exact nodup (i - 1) j  (by omega) h₆ (by omega) h
  · apply And.intro
    · intro nil_p
      apply_fun (·.length) at nil_p
      simp only [Walk.length_nil] at nil_p; omega
    · rw [List.nodup_iff_count_le_one]; exact fun a => le_of_eq (hp' a)

theorem IsHamiltonianCycle.isHamiltonianCycle_of_tail_toFinset
    {u : V} {p : G.Walk u u} (hp : p.length = ‖V‖)
    (hV : ‖V‖ ≥ 3) (hp' : p.support.tail.toFinset = Finset.univ)
  : p.IsHamiltonianCycle := by
  apply thm1; rwa [hp]
  suffices p.support.tail ~ Finset.univ.toList by
    intro a; rw [List.Perm.count_eq this]
    apply List.count_eq_one_of_mem; apply Finset.nodup_toList; simp
  apply List.Perm.symm; apply List.Subperm.perm_of_length_le
  · rw [List.subperm_ext_iff]
    intro a ha; rw [List.count_eq_one_of_mem (Finset.nodup_toList _) ha]
    rw [Nat.succ_le, List.count_pos_iff_mem]
    rwa [Finset.mem_toList, ← hp', List.mem_toFinset] at ha
  · simp [hp]

private theorem dropUntil_not_nil {u v w : V} {p : G.Walk u v} (hw : w ∈ p.support) (ne : w ≠ v)
  : ¬(p.dropUntil w hw).Nil := by
  induction p with
  | @nil u => simp at hw; exfalso; exact ne hw
  | @cons u' v' w' adj tail ih =>
    simp at hw; cases' hw with hw₁ hw₂
    · subst hw₁; simp [Walk.dropUntil]
    · simp [Walk.dropUntil]; split_ifs with hw₃
      · subst hw₃; simp
      · exact ih hw₂ ne

open Walk
private theorem from_ClosureStep_aux
    {u u' v v' : V} {p : G.Walk u u'}
    (hV : ‖V‖ ≥ 3) (hp : p.support ~ Finset.univ.toList)
    (ne : v ≠ u') (vu' : G.Adj v u') (v'u : G.Adj v' u)
    (d : G.Dart) (hd : d ∈ p.darts) (hd₁ : d.fst = v) (hd₂ : d.snd = v')
  : IsHamiltonian G := by
  have hv : v ∈ p.support := by simp [List.Perm.mem_iff hp]
  have not_nil : ¬(p.dropUntil v hv).Nil := dropUntil_not_nil hv ne
  have snd_eq_v' : (p.dropUntil v hv).sndOfNotNil not_nil = v' := by
    rw [← hd₂]
    refine p.next_unique ?_
      (p.darts_dropUntil_subset _ $ (p.dropUntil v hv).firstDart_mem_darts not_nil)
      hd (by simp [hd₁])
    have : p.support.Nodup := by rw [List.Perm.nodup_iff hp]; apply Finset.nodup_toList
    apply List.Nodup.sublist (List.dropLast_sublist _) this
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail not_nil |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ => ⟨u, q, this⟩
  apply IsHamiltonianCycle.isHamiltonianCycle_of_tail_toFinset
  · simp [q, add_assoc]
    have := p.sum_takeUntil_dropUntil_length hv
    have := calc
      p.length + 1 = p.support.length := by simp
      _ = Finset.univ.toList.length := by apply List.Perm.length_eq hp
      _ = ‖V‖ := by simp
    omega
  · assumption
  · simp [q, support_tail', tail_support_append, List.reverse_tail,
      List.toFinset_append, Finset.eq_univ_iff_forall]
    intro w; by_contra hw; simp at hw; rcases hw with ⟨hw₁, hw₂, hw₃, hw₄⟩
    have mem_tail : w ∈ p.support.tail := by
      have mem : w ∈ p.support := by rw [List.Perm.mem_iff hp]; simp
      rw [Walk.support_eq_cons] at mem; simp at mem; exact mem.resolve_left hw₄
    have not_mem_drop : w ∉ (p.dropUntil v hv).support.tail := by
      have tail_not_nil := tail_support_ne_nil not_nil
      have : (p.dropUntil v hv).support.tail.getLast tail_not_nil = u' := by
        rw [List.getLast_tail, support_getLast]
      rw [← List.dropLast_append_getLast tail_not_nil, this]
      simp; exact ⟨hw₃, hw₁⟩
    have append : p.support.tail =
        (p.takeUntil v hv).support.tail ++ (p.dropUntil v hv).support.tail := by
      rw [← tail_support_append, take_spec]
    simp [append] at mem_tail
    cases' mem_tail with h h; exact hw₂ h; exact not_mem_drop h

private theorem from_ClosureStep_aux'
    {u v : V} {q : G.closureStep.Walk u u} (hq : q.IsHamiltonianCycle) (hV : ‖V‖ ≥ 3)
    (huv : G.degree u + G.degree v ≥ ‖V‖) (hv : v = hq.next u) (not_adj : ¬G.Adj u v)
  : ∃ w w' d, G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst = w' ∧ d.snd = w := by
  let X := (hq.next ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.next v}
  have cardX : G.degree u - 1 ≤ X.toFinset.card := calc
    _ = (G.neighborFinset u).card - 1 := by simp
    _ = (Finset.univ.filter (G.Adj u)).card - 1 := by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.next ·)).card - ({u} : Finset _).card := by
      simp [Finset.card_image_of_injective _ hq.next_inj]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.next ·)) \ {u}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [X]
  have cardY : G.degree v - 1 ≤ Y.toFinset.card := calc
    _ = (G.neighborFinset v).card - 1 := by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card - ({hq.next v} : Finset _).card := by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.next v}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [Y]
  have card_union : (X ∪ Y).toFinset.card ≤ ‖V‖ - 3 := calc
    _ ≤ ({v, hq.next v, u}ᶜ : Finset _).card := by
      apply Finset.card_le_card; rw [Finset.subset_compl_comm]
      intro w hw; simp [X, Y] at hw |-; apply And.intro
      · intro w' adj next; rcases hw with hw | hw | hw
        · rw [hw, hv] at next; rw [hq.next_inj next] at adj; simp at adj
        · rw [hw] at next; rw [hq.next_inj next] at adj; exfalso; exact not_adj adj
        · exact hw
      · intro adj; rcases hw with hw | hw | hw
        · rw [hw] at adj; simp at adj
        · exact hw
        · rw [hw] at adj; exfalso; exact not_adj adj.symm
    _ = _ := by
      suffices ({v, hq.next v, u} : Finset _).card = 3 by rw [Finset.card_compl, this]
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem]
      simp; simp [hv]; apply hq.next_next_ne; simp [hv]
      apply And.intro; rw [eq_comm]; apply hq.next_ne; apply hq.next_ne
  have non_empty : (X ∩ Y).toFinset.card ≠ 0 := fun h => by
    suffices ‖V‖ - 2 ≤ ‖V‖ - 3 by omega
    calc
      _ ≤ (G.degree u + G.degree v) - 2 := by
        apply Nat.sub_le_sub_right; exact huv
      _ ≤ (G.degree u - 1) + (G.degree v - 1) := by omega
      _ ≤ X.toFinset.card + Y.toFinset.card := add_le_add cardX cardY
      _ = (X ∪ Y).toFinset.card + (X ∩ Y).toFinset.card := by
        simp [-Set.toFinset_card]; symm; apply Finset.card_union_add_card_inter
      _ ≤ ‖V‖ - 3 + 0 := add_le_add card_union (le_of_eq h)
      _ = ‖V‖ - 3 := by simp
  obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp non_empty
  simp [X, Y] at hw
  rcases hw with ⟨⟨⟨w', hw'₁, hw'₂⟩, -⟩, hw₂, -⟩
  obtain ⟨d, hd₁, hd₂⟩ := hq.self_next_in_darts w'
  rw [hw'₂] at hd₂
  exact ⟨w, w', d, hw₂.symm, hw'₁.symm, hd₁, hd₂⟩

theorem from_ClosureStep (hG : IsHamiltonian (closureStep G)) : IsHamiltonian G := by
  by_cases trivial : Fintype.card V = 1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a, p, hp⟩ := hG trivial
    obtain ⟨d, hd, hd'⟩ : ∃ d ∈ p.darts, ¬G.Adj d.fst d.snd := by
      by_contra h; simp at h
      have edgeSubset (e) (he : e ∈ p.edges) : e ∈ G.edgeSet := by
        simp [Walk.edges] at he; obtain ⟨d, hd, hd'⟩ := he
        rw [← hd']; exact h _ hd
      let q := p.transfer G edgeSubset
      suffices q.IsHamiltonianCycle from nonHamiltonian (fun _ => ⟨a, q, this⟩)
      exact hp.transfer edgeSubset
    set u := d.fst; set v := d.snd
    have hu : u ∈ p.support := Walk.dart_fst_mem_support_of_mem_darts _ hd
    let q := p.rotate hu
    have hq : q.IsHamiltonianCycle := hp.rotate u
    have hd_q : d ∈ q.darts := by
      simp [q]; exact List.IsRotated.mem_iff (rotate_darts _ _) |>.mpr hd
    have q_not_nil : ¬q.Nil := by erw [rotate_Nil_iff]; exact hp.1.not_nil
    have next_u_eq_v : q.sndOfNotNil q_not_nil = v := by
      exact hq.1.next_unique (q.firstDart_mem_darts q_not_nil) hd_q rfl
    have uv_not_edge : s(u, v) ∉ (q.tail q_not_nil).edges := by
      have : q = cons (q.adj_sndOfNotNil q_not_nil) (q.tail q_not_nil) := by
        symm; apply q.cons_tail_eq
      have : q.edges = s(u, v) :: (q.tail q_not_nil).edges := by
        simp only [this, edges_cons]; simp; left; exact next_u_eq_v
      intro h
      have nodup := hq.1.edges_nodup
      rw [this] at nodup; exact List.not_nodup_cons_of_mem h nodup
    have G_closure_del : G.closureStep.deleteEdges {s(u, v)} = G := by
      exact closureStep_deleteEdge _ hd' d.adj
    let q' := q.tail q_not_nil
      |>.toDeleteEdge s(u, v) uv_not_edge
      |>.transfer G (by
        simp (config := {singlePass := true}) only [← G_closure_del]
        exact edges_subset_edgeSet _)
      |>.copy next_u_eq_v rfl
    have perm_q' : q'.support ~ Finset.univ.toList := by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp [q', List.perm_iff_count, hq.2]
      intro a; symm; apply List.count_eq_one_of_mem; apply Finset.nodup_toList; simp
    have hV : ‖V‖ ≥ 3 := hq.length_eq ▸ hq.isCycle.three_le_length
    have deg_sum := closureStep_deg_sum G hd' d.adj
    have next_u : v = hq.next u := by
      obtain ⟨d', hd'₁, hd'₂, hd'₃⟩ := hq.self_next_in_darts u
      exact hd'₃ ▸ hq.isCycle.next_unique hd_q hd'₁ hd'₂.symm
    obtain ⟨w, w', d', hw, hw', d'_mem, hd'₁, hd'₂⟩ :=
      from_ClosureStep_aux' hq hV deg_sum next_u hd'
    have q'_support : q'.support = q.support.tail := by simp [q']
    obtain ⟨i, i_lt, hi⟩ := List.getElem_of_mem d'_mem
    simp at i_lt
    rw [← hi, darts_getElem_snd i i_lt] at hd'₂
    rw [← hi, darts_getElem_fst i i_lt] at hd'₁
    have i_nz : i ≠ 0 := by
      intro i_zero; simp only [i_zero, List.getElem_zero, support_head] at hd'₁
      simp [hd'₁] at hw'
    have i_min_1 : i - 1 < q'.darts.length := by
      have q'_length : q'.length = q.length - 1 := by
        have := length_tail_add_one q_not_nil
        simp [q']; omega
      simp [q'_length]; omega
    have hd''₁ : (q'.darts[i - 1]).fst = w' := by
      rw [darts_getElem_fst]; simp only [q'_support, ← List.drop_one]
      rw [List.getElem_drop', ← hd'₁]; congr; omega; simpa using i_min_1
    have hd''₂ : (q'.darts[i - 1]).snd = w := by
      rw [darts_getElem_snd]; simp only [q'_support, ← List.drop_one]
      rw [List.getElem_drop', ← hd'₂]; congr 1; omega; simpa using i_min_1
    have w'_ne_u : w' ≠ u := by intro eq; simp [eq] at hw'
    have Hamiltonian :=
      from_ClosureStep_aux hV perm_q' w'_ne_u hw' hw q'.darts[i - 1]
      (List.getElem_mem _ _ _) hd''₁ hd''₂
    exact nonHamiltonian Hamiltonian

theorem from_closure_aux {n} (hG : ¬IsHamiltonian G) : ¬IsHamiltonian (closureStep^[n] G) := by
  induction n with
  | zero => simpa
  | succ m ih =>
    rw [add_comm]; contrapose ih
    simp [Function.iterate_add_apply] at ih |-
    exact from_ClosureStep ih

theorem from_closure (hG : IsHamiltonian (closure G)) : IsHamiltonian G := by
  unfold closure eventuallyConstant at hG
  contrapose hG; exact from_closure_aux hG

theorem completeGraph (hV : ‖V‖ = 1 ∨ ‖V‖ ≥ 3) : IsHamiltonian (⊤ : SimpleGraph V) := by
  cases' hV with hV hV
  · simp [IsHamiltonian]; exact absurd hV
  · have ne : (⊤ : Finset V).toList ≠ [] := by simp [← Finset.card_eq_zero]; omega
    let p := Walk.cons
      (show (⊤ : SimpleGraph V).Adj
          ((⊤ : Finset V).toList.getLast ne) ((⊤ : Finset V).toList.head ne) by
        simp [List.getLast_eq_get]
        rw [← List.getElem_zero _, List.Nodup.getElem_inj_iff]
        omega; exact Finset.univ.nodup_toList; simp; omega)
      (Walk.fromList (G := ⊤) ne
        (by simp; exact List.Pairwise.chain' Finset.univ.nodup_toList))
    suffices p.IsHamiltonianCycle from fun _ => ⟨((⊤ : Finset V).toList.getLast ne), p, this⟩
    apply IsHamiltonianCycle.isHamiltonianCycle_of_tail_toFinset
    · simp [p, ← Walk.length_support, fromList_support]
    · exact hV
    · simp [p, fromList_support]

lemma degree_mono (u : V) : Monotone (fun G => degree G u) := by
  intro G H le; simp [← card_neighborFinset_eq_degree]
  apply Finset.card_le_card; intro v hv; simp at hv |-; exact le hv

theorem Dirac (hV : ‖V‖ ≥ 3) (hG : ∀ u, 2 * G.degree u ≥ ‖V‖) : G.IsHamiltonian := by
  have : G.closure = (⊤ : SimpleGraph V) := by
    rw [eq_top_iff]; intro u v ne; simp at ne
    apply closure_spec G ne; calc
      ‖V‖ ≤ G.degree u + G.degree v := by have := hG u; have:= hG v; omega
      _ ≤ G.closure.degree u + G.closure.degree v :=
        add_le_add (degree_mono u (self_le_closure G)) (degree_mono v (self_le_closure G))
  exact from_closure (this ▸ completeGraph (by omega))

theorem Ore (hV : ‖V‖ ≥ 3) (hG : ∀ {u} {v}, ¬ G.Adj u v → G.degree u + G.degree v ≥ ‖V‖)
  : G.IsHamiltonian := by
  have : G.closure = (⊤ : SimpleGraph V) := by
    rw [eq_top_iff]; intro u v ne; simp at ne
    by_cases adj : G.Adj u v
    · exact self_le_closure G adj
    · apply closure_spec G ne; calc
      ‖V‖ ≤ G.degree u + G.degree v := hG adj
      _ ≤ G.closure.degree u + G.closure.degree v :=
        add_le_add (degree_mono u (self_le_closure G)) (degree_mono v (self_le_closure G))
  exact from_closure (this ▸ completeGraph (by omega))

end IsHamiltonian
end SimpleGraph
