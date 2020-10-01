import group_theory.perm.sign
import group_theory.subgroup
import data.list.perm
import fin_group
import array_perm_group

open equiv
open equiv.perm

/-- The group of all possible ways to assemble a Rubik's cube. Not all positions are solvable. -/
@[derive group] def rubiks_cube_overgroup := array_perm 8 (fin' 3) × array_perm 12 (fin' 2)

section widget

  inductive colour : Type | white | green | red | blue | orange | yellow

  open colour

  instance : has_to_string colour :=
  ⟨
    λ c, match c with
      | white := "#ffffff"
      | green := "#00ff00"
      | red := "#ff0000"
      | blue := "#0000ff"
      | orange := "#ff7f00"
      | yellow := "#ffff00"
    end
  ⟩

  open vector

  def list.vec {α : Sort*} : Π a : list α, vector α (a.length)
    | [] := nil
    | (x :: xs) := cons x (xs.vec)

  def corner_map : vector (vector colour 3) 8 :=
  [
    [white, orange, blue].vec,
    [white, blue, red].vec,
    [white, red, green].vec,
    [white, green, orange].vec,
    [yellow, orange, green].vec,
    [yellow, green, red].vec,
    [yellow, red, blue].vec,
    [yellow, blue, orange].vec
  ].vec

  def edge_map : vector (vector colour 2) 12 :=
  [
    [white, blue].vec,
    [white, red].vec,
    [white, green].vec,
    [white, orange].vec,
    [yellow, green].vec,
    [yellow, red].vec,
    [yellow, blue].vec,
    [yellow, orange].vec,
    [blue, orange].vec,
    [blue, red].vec,
    [green, red].vec,
    [green, orange].vec
  ].vec

  variables (cube : rubiks_cube_overgroup) (i : fin 8)

  def corner_sticker (i : fin 8) (o : fin 3) (cube : rubiks_cube_overgroup) : colour :=
    nth (nth corner_map (cube.fst.snd.inv_fun i)) (((cube.fst.fst.read i)⁻¹ : fin' 3) + o)

  def edge_sticker (i : fin 12) (o : fin 2) (cube : rubiks_cube_overgroup) : colour :=
    nth (nth edge_map (cube.snd.snd.inv_fun i)) (((cube.snd.fst.read i)⁻¹ : fin' 2) + o)

  open widget

  meta def sticker (x y : ℕ) (colour : colour) : html empty :=
    h "div" [attr.style [("grid-column", to_string x), ("grid-row", to_string y), ("background-color", to_string colour)]] []

  meta def rubiks_cube_overgroup.to_html (cube : rubiks_cube_overgroup) : html empty :=
    h
    "div"
    [
      attr.style
      [
        ("display", "grid"),
        ("grid-template-columns", "repeat(12, 20px)"),
        ("grid-template-rows", "repeat(9, 20px)"),
        ("row-gap", "2px"),
        ("column-gap", "2px"),
        ("margin", "10px")
      ]
    ]
    [
      sticker 4 1 ∘ corner_sticker 0 0 $ cube,
      sticker 5 1 ∘ edge_sticker 0 0 $ cube,
      sticker 6 1 ∘ corner_sticker 1 0 $ cube,
      sticker 4 2 ∘ edge_sticker 3 0 $ cube,
      sticker 5 2 white,
      sticker 6 2 ∘ edge_sticker 1 0 $ cube,
      sticker 4 3 ∘ corner_sticker 3 0 $ cube,
      sticker 5 3 ∘ edge_sticker 2 0 $ cube,
      sticker 6 3 ∘ corner_sticker 2 0 $ cube,

      sticker 1 4 ∘ corner_sticker 0 1 $ cube,
      sticker 2 4 ∘ edge_sticker 3 1 $ cube,
      sticker 3 4 ∘ corner_sticker 3 2 $ cube,
      sticker 1 5 ∘ edge_sticker 8 1 $ cube,
      sticker 2 5 orange,
      sticker 3 5 ∘ edge_sticker 11 1 $ cube,
      sticker 1 6 ∘ corner_sticker 7 2 $ cube,
      sticker 2 6 ∘ edge_sticker 7 1 $ cube,
      sticker 3 6 ∘ corner_sticker 4 1 $ cube,

      sticker 4 4 ∘ corner_sticker 3 1 $ cube,
      sticker 5 4 ∘ edge_sticker 2 1 $ cube,
      sticker 6 4 ∘ corner_sticker 2 2 $ cube,
      sticker 4 5 ∘ edge_sticker 11 0 $ cube,
      sticker 5 5 green,
      sticker 6 5 ∘ edge_sticker 10 0 $ cube,
      sticker 4 6 ∘ corner_sticker 4 2 $ cube,
      sticker 5 6 ∘ edge_sticker 4 1 $ cube,
      sticker 6 6 ∘ corner_sticker 5 1 $ cube,

      sticker 7 4 ∘ corner_sticker 2 1 $ cube,
      sticker 8 4 ∘ edge_sticker 1 1 $ cube,
      sticker 9 4 ∘ corner_sticker 1 2 $ cube,
      sticker 7 5 ∘ edge_sticker 10 1 $ cube,
      sticker 8 5 red,
      sticker 9 5 ∘ edge_sticker 9 1 $ cube,
      sticker 7 6 ∘ corner_sticker 5 2 $ cube,
      sticker 8 6 ∘ edge_sticker 5 1 $ cube,
      sticker 9 6 ∘ corner_sticker 6 1 $ cube,

      sticker 10 4 ∘ corner_sticker 1 1 $ cube,
      sticker 11 4 ∘ edge_sticker 0 1 $ cube,
      sticker 12 4 ∘ corner_sticker 0 2 $ cube,
      sticker 10 5 ∘ edge_sticker 9 0 $ cube,
      sticker 11 5 blue,
      sticker 12 5 ∘ edge_sticker 8 0 $ cube,
      sticker 10 6 ∘ corner_sticker 6 2 $ cube,
      sticker 11 6 ∘ edge_sticker 6 1 $ cube,
      sticker 12 6 ∘ corner_sticker 7 1 $ cube,

      sticker 4 7 ∘ corner_sticker 4 0 $ cube,
      sticker 5 7 ∘ edge_sticker 4 0 $ cube,
      sticker 6 7 ∘ corner_sticker 5 0 $ cube,
      sticker 4 8 ∘ edge_sticker 7 0 $ cube,
      sticker 5 8 yellow,
      sticker 6 8 ∘ edge_sticker 5 0 $ cube,
      sticker 4 9 ∘ corner_sticker 7 0 $ cube,
      sticker 5 9 ∘ edge_sticker 6 0 $ cube,
      sticker 6 9 ∘ corner_sticker 6 0 $ cube
    ]

end widget

section face_turns

  private def cycle_impl {α : Type*} [decidable_eq α] : α → list α → perm α
    | _ [] := 1
    | a (x :: xs) := swap a x * cycle_impl x xs

  private def cycle {α : Type*} [decidable_eq α] : list α → perm α
    | [] := 1
    | (x :: xs) := cycle_impl x xs

  open array

  def wr {n m : ℕ} (i : fin n) (x : fin m) (a : array n (fin' m)) := write a i x

  def U : rubiks_cube_overgroup :=
    ⟨⟨1, cycle [0, 1, 2, 3]⟩, ⟨1, cycle [0, 1, 2, 3]⟩⟩
  def D : rubiks_cube_overgroup :=
    ⟨⟨1, cycle [4, 5, 6, 7]⟩, ⟨1, cycle [4, 5, 6, 7]⟩⟩
  def R : rubiks_cube_overgroup :=
    ⟨⟨wr 1 1 ∘ wr 6 2 ∘ wr 5 1 ∘ wr 2 2 $ 1, cycle [1, 6, 5, 2]⟩, ⟨1, cycle [1, 9, 5, 10]⟩⟩
  def L : rubiks_cube_overgroup :=  
    ⟨⟨wr 0 2 ∘ wr 3 1 ∘ wr 4 2 ∘ wr 7 1 $ 1, cycle [0, 3, 4, 7]⟩, ⟨1, cycle [3, 11, 7, 8]⟩⟩
  def F : rubiks_cube_overgroup :=
    ⟨⟨wr 2 1 ∘ wr 5 2 ∘ wr 4 1 ∘ wr 3 2 $ 1, cycle [2, 5, 4, 3]⟩, ⟨wr 2 1 ∘ wr 10 1 ∘ wr 4 1 ∘ wr 11 1 $ 1, cycle [2, 10, 4, 11]⟩⟩
  def B : rubiks_cube_overgroup :=
    ⟨⟨wr 0 1 ∘ wr 7 2 ∘ wr 6 1 ∘ wr 1 2 $ 1, cycle [0, 7, 6, 1]⟩, ⟨wr 0 1 ∘ wr 8 1 ∘ wr 6 1 ∘ wr 9 1 $ 1, cycle [0, 8, 6, 9]⟩⟩
  def U2 := U^2
  def D2 := D^2
  def R2 := R^2
  def L2 := L^2
  def F2 := F^2
  def B2 := B^2
  def U' := U⁻¹
  def D' := D⁻¹
  def R' := R⁻¹
  def L' := L⁻¹
  def F' := F⁻¹
  def B' := B⁻¹

  instance : has_coe_to_fun rubiks_cube_overgroup := ⟨(λ a, rubiks_cube_overgroup → rubiks_cube_overgroup), λ x y, x * y⟩

end face_turns

/-- The set of all solvable Rubik's cubes. -/
def rubiks_cube : set rubiks_cube_overgroup := {c | c.fst.snd.sign = c.snd.snd.sign ∧ multiset.prod ⟦c.fst.fst.to_list⟧ = 1 ∧ multiset.prod ⟦c.snd.fst.to_list⟧ = 1}

namespace rubiks_cube

  section perm_to_list

    variables {α β : Type*}

    open list

    private lemma list_swap_lt {n m : ℕ} : 0 < n → n < m.succ → n - 1 < m :=
    begin
      intros h₁ h₂,
      cases n,
      {
        exfalso,
        apply nat.not_lt_zero,
        apply h₁,
      },
      rw [nat.sub_one, nat.pred_succ],
      apply nat.lt_of_succ_lt_succ,
      apply h₂,
    end

    @[simp] def list.swap : Π (l : list α) (i j : ℕ), i < j → j < l.length → list α
      | [] _ _ _ h := false.elim (nat.not_lt_zero _ h)
      | (x :: xs) _ 0 h _ := false.elim (nat.not_lt_zero _ h)
      | (x :: xs) 0 (j' + 1) h₁ h₂ := xs.nth_le j' (list_swap_lt h₁ h₂) :: xs.take j' ++ x :: xs.drop (j' + 1)
      | (x :: xs) (i' + 1) (j' + 1) h₁ h₂ := x :: xs.swap i' j' (nat.lt_of_succ_lt_succ h₁) (nat.lt_of_succ_lt_succ h₂)

    lemma list_perm_swap {l : list α} {i j h₁ h₂} : list.swap l i j h₁ h₂ ~ l :=
    begin
      revert i j,
      induction l,
      {
        intros i j _ h,
        exfalso,
        apply nat.not_lt_zero,
        apply h,
      },
      intros i j h₁ h₂,
      cases i, swap,
      {
        cases j,
        {
          exfalso,
          apply nat.not_lt_zero,
          apply h₁,
        },
        apply perm.cons,
        apply l_ih,
      },
      cases j,
      {
        exfalso,
        apply nat.not_lt_zero,
        apply h₁,
      },
      dsimp,
      rw [← cons_append, ← singleton_append, ← @singleton_append _ l_hd],
      apply perm_append_comm.trans,
      rw [singleton_append, cons_append],
      apply perm.cons,
      rw ← append_assoc,
      apply perm_append_comm.trans,
      apply (perm.append_left _ perm_append_comm).trans,
      apply eq.rec (perm.refl _),
      dsimp,
      rw ← drop_eq_nth_le_cons,
      apply take_append_drop,
    end

    @[simp] lemma list_swap_length {l : list α} {i j h₁ h₂} : (list.swap l i j h₁ h₂).length = l.length :=
    begin
      apply perm.length_eq,
      apply list_perm_swap,
    end

    private lemma swap_cases [de : decidable_eq α] {x y z : α} (p : α → Prop) : p x → p y → p z → p (swap x y z) :=
    begin
      intros h_x h_y h_z,
      cases de z x with z_ne_x z_eq_x, swap,
      {
        simp *,
      },
      cases de z y with z_ne_y z_eq_y, swap,
      {
        simp *,
      },
      rw swap_apply_of_ne_of_ne; assumption,
    end

    private lemma swap_map [de : decidable_eq α] [decidable_eq β] {x y z : α} {f : α → β} (inj : function.injective f) : swap (f x) (f y) (f z) = f (swap x y z) :=
    begin
      cases de z x, swap,
      {
        simp *,
      },
      cases de z y, swap,
      {
        simp *,
      },
      rw swap_apply_of_ne_of_ne, rotate,
      {
        simp *,
      },
      {
        simp *,
      },
      rw swap_apply_of_ne_of_ne; assumption,
    end
    
    lemma list_swap_nth_le {l : list α} {i j k h₁ h₂ h₃ h₄} : (list.swap l i j h₁ h₂).nth_le k h₃ = l.nth_le (swap i j k) h₄ :=
    begin
      revert i j k,
      induction l,
      {
        intros,
        exfalso,
        apply nat.not_lt_zero,
        apply h₂,
      },
      intros,
      cases j,
      {
        exfalso,
        apply nat.not_lt_zero,
        apply h₁,
      },
      cases i,
      {
        dsimp,
        cases k,
        {
          simp_rw swap_apply_left,
          refl,
        },
        cases nat.decidable_eq k j with k_ne_j k_eq_j,
        {
          have k_pos : k.succ ≠ 0,
          {
            intros,
            contradiction,
          },
          have k_ne_j' : k.succ ≠ j.succ,
          {
            intros h,
            apply k_ne_j,
            apply nat.succ.inj,
            apply h,
          },
          simp_rw swap_apply_of_ne_of_ne k_pos k_ne_j',
          dsimp,
          cases (lt_or_gt_of_ne k_ne_j) with k_lt_j k_gt_j,
          {
            rw nth_le_append, swap,
            {
              rw length_take,
              apply lt_min,
              {
                apply k_lt_j,
              },
              {
                apply lt_trans k_lt_j,
                apply nat.lt_of_succ_lt_succ,
                apply h₂,
              },
            },
            suffices : ∀ {l : list α} {n i h₁ h₂}, (take n l).nth_le i h₁ = l.nth_le i h₂,
            {
              rw this,
            },
            intros l,
            induction l with l_hd l l_ih,
            {
              intros n i h₁ h₂,
              exfalso,
              apply nat.not_lt_zero,
              apply h₂,
            },
            intros n i h₁ h₂,
            cases n,
            {
              exfalso,
              apply nat.not_lt_zero,
              apply h₁,
            },
            cases i,
            {
              refl,
            },
            apply l_ih,
          },
          {
            have take_length : (take j l_tl).length = j,
            {
              rw length_take,
              apply min_eq_left,
              apply le_of_lt,
              apply nat.lt_of_succ_lt_succ,
              apply h₂,
            },
            rw nth_le_append_right, swap,
            {
              rw take_length,
              apply le_of_lt,
              apply k_gt_j,
            },
            simp_rw take_length,
            cases k,
            {
              exfalso,
              apply nat.not_lt_zero,
              apply k_gt_j,
            },
            have k_ge_j : k ≥ j,
            {
              apply nat.le_of_lt_succ,
              apply k_gt_j,
            },
            simp_rw @nat.succ_sub k j k_ge_j,
            dsimp,
            rw nth_le_drop',
            congr,
            rw nat.succ_add,
            rw nat.add_sub_cancel',
            apply k_ge_j,
          },
        },
        {
          subst k,
          simp_rw swap_apply_right,
          dsimp,
          have : ∀ {l₁ l₂ : list α} {x : α} {i : ℕ} {h}, l₁.length = i → (l₁ ++ x :: l₂).nth_le i h = x,
          {
            intros l₁,
            induction l₁,
            {
              intros,
              subst i,
              refl,
            },
            intros l₂ x i h₁ h₂,
            cases i,
            {
              contradiction,
            },
            dsimp,
            rw l₁_ih,
            apply nat.succ.inj,
            apply h₂,
          },
          apply this,
          rw length_take,
          apply min_eq_left,
          apply nat.le_of_succ_le_succ,
          apply le_of_lt,
          apply h₂,
        },
      },
      {
        intros,
        dsimp,
        cases k,
        {
          dsimp,
          have i_pos : 0 ≠ i.succ,
          {
            intros h,
            contradiction,
          },
          have j_pos : 0 ≠ j.succ,
          {
            intros h,
            contradiction,
          },
          simp_rw swap_apply_of_ne_of_ne i_pos j_pos,
          simp,
        },
        dsimp,
        conv_rhs
        {
          congr, skip,
          rw swap_map nat.succ_injective,
        },
        dsimp,
        apply l_ih,
      },
    end

    lemma perm_array_swap_eq_to_list_swap {n : ℕ} {a : array n α} {i j h₁ h₂} : (perm_array a (swap i j)).to_list = list.swap a.to_list i j h₁ h₂ :=
    begin
      apply ext_le,
      {
        simp,
      },
      intros k h₃ h₄,
      rw array.to_list_nth_le, swap,
      {
        rwa array.to_list_length at h₃,
      },
      simp_rw perm_array_def,
      dsimp,
      have : equiv.symm (swap i j) = swap i j := rfl,
      rw this,
      clear this,
      rw array.to_list_length at *,
      rw list_swap_nth_le, swap,
      {
        rw array.to_list_length,
        apply swap_cases (< n),
        {
          apply lt.trans h₁,
          apply h₂,
        },
        {
          apply h₂,
        },
        {
          apply h₃,
        },
      },
      rw array.to_list_nth_le, swap,
      {
        apply swap_cases (< n),
        {
          apply lt.trans h₁,
          apply h₂,
        },
        {
          apply h₂,
        },
        {
          apply h₃,
        },
      },
      congr,
      apply fin.eq_of_veq,
      rw swap_apply_def,
      dsimp,
      rw swap_apply_def,
      cases fin.decidable_eq _ ⟨k, _⟩ i with k_ne_i k_eq_i,
      {
        rw if_neg, swap,
        {
          apply k_ne_i,
        },
        rw @if_neg (k = ↑i), swap,
        {
          intros h,
          apply k_ne_i,
          apply fin.eq_of_veq,
          apply h,
        },
        cases fin.decidable_eq _ ⟨k, _⟩ j with k_ne_j k_eq_j,
        {
          rw if_neg, swap,
          {
            apply k_ne_j,
          },
          rw if_neg, swap,
          {
            intros h,
            apply k_ne_j,
            apply fin.eq_of_veq,
            apply h,
          },
          refl,
        },
        rw if_pos, swap,
        {
          apply k_eq_j,
        },
        rw if_pos, swap,
        {
          rw ← k_eq_j,
          refl,
        },
      },
      rw if_pos, swap,
      {
        apply k_eq_i,
      },
      rw if_pos, swap,
      {
        rw ← k_eq_i,
        refl,
      },
    end

    theorem perm_to_list {n : ℕ} {a : array n α} {p : perm (fin n)} : (perm_array a p).to_list ~ a.to_list :=
    begin
      apply swap_induction_on p,
      {
        rw perm_array_perm_one,
      },
      clear p,
      intros p i j i_ne_j ih,
      apply perm.trans _ ih,
      clear ih,
      rw ← perm_array_comp,
      generalize : perm_array a p = l,
      clear a,
      wlog i_lt_j : i < j using i j,
      {
        apply lt_or_gt_of_ne,
        apply i_ne_j,
      },
      swap,
      {
        rw swap_comm,
        apply this,
        symmetry,
        apply i_ne_j,
      },
      rw perm_array_swap_eq_to_list_swap, rotate,
      {
        apply i_lt_j,
      },
      {
        rw array.to_list_length,
        apply fin.is_lt,
      },
      apply list_perm_swap,
    end

  end perm_to_list

  private lemma list.map₂_nth_le {α β γ : Type*} {a b} {f : α → β → γ} {i : ℕ} {h h₁ h₂} : (list.map₂ f a b).nth_le i h = f (a.nth_le i h₁) (b.nth_le i h₂) :=
  begin
    revert b i,
    induction a,
    {
      intros b i h h₁ h₂,
      exfalso,
      apply nat.not_lt_zero,
      apply h₁,
    },
    intros b,
    cases b,
    {
      intros i h h₁ h₂,
      exfalso,
      apply nat.not_lt_zero,
      apply h₂,
    },
    intros i h h₁ h₂,
    dsimp,
    cases i,
    {
      refl,
    },
    dsimp,
    apply a_ih,
  end

  lemma mul_to_list {α : Type*} [group α] {n : ℕ} {a b : array n α} : (a * b).to_list = list.map₂ (*) a.to_list b.to_list :=
  begin
    apply list.ext_le,
    {
      simp,
    },
    intros i h_i h_i₂,
    rw array.to_list_length at *,
    rw list.map₂_nth_le; try { rwa array.to_list_length },
    simp only [array.to_list_nth_le _ h_i, array.read_mul],
  end

  lemma inv_to_list {α : Type*} [group α] {n : ℕ} {a : array n α} : a⁻¹.to_list = list.map (has_inv.inv) a.to_list :=
  begin
    apply list.ext_le,
    {
      simp,
    },
    intros i h_i h_i₂,
    rw array.to_list_length at *,
    rw list.nth_le_map; try { rwa array.to_list_length },
    simp only [array.to_list_nth_le _ h_i],
    refl,
  end

  lemma mul_prod {α : Type*} [comm_group α] {a b : list α} : a.length = b.length → (list.map₂ (*) a b).prod = a.prod * b.prod :=
  begin
    revert b,
    induction a,
    {
      intros b h,
      rw list.eq_nil_of_length_eq_zero h.symm,
      simp,
    },
    intros b h,
    cases b,
    {
      contradiction,
    },
    dsimp,
    simp only [list.prod_cons],
    rw a_ih; injection h,
    apply mul_mul_mul_comm,
  end

  lemma inv_prod {α : Type*} [comm_group α] {a : list α} : (list.map (has_inv.inv) a).prod = a.prod⁻¹ :=
  begin
    induction a,
    {
      simp,
    },
    simp [list.prod_cons, mul_comm, *],
  end

  lemma perm_prod {α : Type*} [comm_group α] {n : ℕ} {a : array n α} {p : perm (fin n)} : (perm_array a p).to_list.prod = a.to_list.prod :=
  begin
    apply list.perm.prod_eq,
    apply perm_to_list,
  end

  lemma one_mem : (1 : rubiks_cube_overgroup) ∈ rubiks_cube :=
  begin
    split; try { split }; refl,
  end

  lemma mul_mem {a b : rubiks_cube_overgroup} : a ∈ rubiks_cube → b ∈ rubiks_cube → a * b ∈ rubiks_cube :=
  begin
    intros h_a h_b,
    split,
    {
      simp [h_a.left, h_b.left],
    },
    split;
    {
      dsimp,
      rw [mul_to_list, multiset.coe_prod, mul_prod],
      swap,
      {
        refl,
      },
      have : (perm_array a.fst.fst b.fst.snd).to_list.prod = a.fst.fst.to_list.prod,
      {
        apply list.perm.prod_eq,
        apply perm_to_list,
      },
      rw perm_prod,
      rcases h_a with ⟨_, h_a₁, h_a₂⟩,
      rcases h_b with ⟨_, h_b₁, h_b₂⟩,
      simp [multiset.coe_prod, *] at *,
    },
  end

  lemma inv_mem {x : rubiks_cube_overgroup} : x ∈ rubiks_cube → x⁻¹ ∈ rubiks_cube :=
  begin
    intros h,
    split,
    {
      simp [sign_inv, h.left],
    },
    split;
    {
      dsimp,
      rw [multiset.coe_prod, perm_prod, inv_to_list, inv_prod, one_inv.symm],
      apply inv_inj.mpr,
      rcases h with ⟨_, h₁, h₂⟩,
      simp [multiset.coe_prod, *] at *,
    },
  end

  protected def group : subgroup rubiks_cube_overgroup :=
  {
    carrier := rubiks_cube,
    one_mem' := one_mem,
    mul_mem' := @mul_mem,
    inv_mem' := @inv_mem,
  }

end rubiks_cube