import Thermal.FiniteExtras
noncomputable section

theorem ComparatorCore.check_Thermal_h_lower :
    ∀ (q : Nat) (a b : Fin q),
  @LE.le.{0} Rat Rat.instLE
    (@Neg.neg.{0} Rat Rat.instNeg (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (Thermal.h q a b) := @_root_.Thermal.h_lower

theorem ComparatorCore.check_Thermal_h_upper :
    ∀ (q : Nat) (a b : Fin q),
  @LE.le.{0} Rat Rat.instLE (Thermal.h q a b)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (@Nat.cast.{0} Rat Rat.instNatCast q)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) := @_root_.Thermal.h_upper

theorem ComparatorCore.check_Thermal_h_sum :
    ∀ (q : Nat) (a : Fin q),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0} (Fin q) Rat Rat.addCommMonoid (@Finset.univ.{0} (Fin q) (Fin.fintype q)) fun (b : Fin q) =>
      Thermal.h q a b)
    (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) := @_root_.Thermal.h_sum

theorem ComparatorCore.check_Thermal_epsilon_pos :
    ∀ (q m : Nat) (hq : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.epsilon q m) := @_root_.Thermal.epsilon_pos

theorem ComparatorCore.check_Thermal_epsilon_lt_one :
    ∀ (q m : Nat) (hq : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q),
  @LT.lt.{0} Rat Rat.instLT (Thermal.epsilon q m) (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.epsilon_lt_one

theorem ComparatorCore.check_Thermal_w_bounds :
    ∀ (q : Nat) (ε : Rat) (a b : Fin q),
  And
    (@LE.le.{0} Rat Rat.instLE
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@HPow.hPow.{0, 0, 0} Rat Nat Rat
          (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid))) ε
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (Thermal.w q ε a b))
    (@LE.le.{0} Rat Rat.instLE (Thermal.w q ε a b)
      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (@Nat.cast.{0} Rat Rat.instNatCast q)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat
            (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid))) ε
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := @_root_.Thermal.w_bounds

theorem ComparatorCore.check_Thermal_w_positive :
    ∀ (q : Nat) (ε : Rat)
  (he0 : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
  (he1 : @LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (a b : Fin q),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.w q ε a b) := @_root_.Thermal.w_positive

theorem ComparatorCore.check_Thermal_isingWeight_positive :
    ∀ (q : Nat) (ε p : Rat)
  (he0 : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
  (he1 : @LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (hp0 : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) p)
  (hp1 : @LT.lt.{0} Rat Rat.instLT p (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (same : Bool)
  (a b : Fin q),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (Thermal.isingWeight q ε p same a b) := @_root_.Thermal.isingWeight_positive

theorem ComparatorCore.check_Thermal_pottsWeight_positive :
    ∀ (q : Nat) (ε v : Rat)
  (he0 : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
  (he1 : @LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (hv : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) v) (same : Bool)
  (a b : Fin q),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (Thermal.pottsWeight q ε v same a b) := @_root_.Thermal.pottsWeight_positive

theorem ComparatorCore.check_Thermal_collision_uniform :
    ∀ {I : Type} [inst : Fintype.{0} I] [inst_1 : DecidableEq.{1} I] (q : Nat) [Nonempty.{1} I] (r : Rat),
  @Eq.{1} Rat (@Thermal.collision I inst inst_1 q fun (x : I → Fin q) => r)
    (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) := @_root_.Thermal.collision_uniform

theorem ComparatorCore.check_Thermal_expansion_eq_one_of_vanish :
    ∀ {J : Type} [inst : DecidableEq.{1} J] (c : Finset.{0} J → Rat) (ε : Rat) (C : Finset.{0} J)
  (hc0 :
    @Eq.{1} Rat (c (@EmptyCollection.emptyCollection.{0} (Finset.{0} J) (@Finset.instEmptyCollection.{0} J)))
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (hc :
    ∀ (T : Finset.{0} J),
      @Finset.Nonempty.{0} J T → @Eq.{1} Rat (c T) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))),
  @Eq.{1} Rat (@Thermal.expansion J inst c ε C) (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.expansion_eq_one_of_vanish

theorem ComparatorCore.check_Thermal_expansion_ge_one :
    ∀ {J : Type} [inst : DecidableEq.{1} J] (c : Finset.{0} J → Rat) (ε : Rat) (C : Finset.{0} J)
  (hc0 :
    @Eq.{1} Rat (c (@EmptyCollection.emptyCollection.{0} (Finset.{0} J) (@Finset.instEmptyCollection.{0} J)))
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  (hc :
    ∀ (T : Finset.{0} J),
      @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (c T)),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
    (@Thermal.expansion J inst c ε C) := @_root_.Thermal.expansion_ge_one

theorem ComparatorCore.check_Thermal_h_gram :
    ∀ (q : Nat) (a b : Fin q),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0} (Fin q) Rat Rat.addCommMonoid (@Finset.univ.{0} (Fin q) (Fin.fintype q)) fun (k : Fin q) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.h q a k) (Thermal.h q b k))
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@Nat.cast.{0} Rat Rat.instNatCast q)
      (Thermal.h q a b)) := @_root_.Thermal.h_gram

theorem ComparatorCore.check_Thermal_gram_sum_squares :
    ∀ {Ω K : Type} [inst : Fintype.{0} Ω] [inst_1 : Fintype.{0} K] (p : Ω → Rat) (v : Ω → K → Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0} Ω Rat Rat.addCommMonoid (@Finset.univ.{0} Ω inst) fun (x : Ω) =>
      @Finset.sum.{0, 0} Ω Rat Rat.addCommMonoid (@Finset.univ.{0} Ω inst) fun (y : Ω) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (p x) (p y))
          (@Finset.sum.{0, 0} K Rat Rat.addCommMonoid (@Finset.univ.{0} K inst_1) fun (k : K) =>
            @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (v x k) (v y k)))
    (@Finset.sum.{0, 0} K Rat Rat.addCommMonoid (@Finset.univ.{0} K inst_1) fun (k : K) =>
      @HPow.hPow.{0, 0, 0} Rat Nat Rat
        (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid)))
        (@Finset.sum.{0, 0} Ω Rat Rat.addCommMonoid (@Finset.univ.{0} Ω inst) fun (x : Ω) =>
          @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (p x) (v x k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Thermal.gram_sum_squares

theorem ComparatorCore.check_Thermal_tensor_gram :
    ∀ {I : Type} [inst : Fintype.{0} I] [inst_1 : DecidableEq.{1} I] (q : Nat) (x y : I → Fin q),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0} (I → Fin q) Rat Rat.addCommMonoid
      (@Finset.univ.{0} (I → Fin q)
        (@Pi.instFintype.{0, 0} I (fun (a : I) => Fin q) inst_1 inst fun (a : I) => Fin.fintype q))
      fun (k : I → Fin q) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@Thermal.tensorFeature I inst q x k)
        (@Thermal.tensorFeature I inst q y k))
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@Fintype.card.{0} I inst))
      (@Finset.prod.{0, 0} I Rat Rat.commMonoid (@Finset.univ.{0} I inst) fun (i : I) => Thermal.h q (x i) (y i))) := @_root_.Thermal.tensor_gram

theorem ComparatorCore.check_Thermal_collision_sum_squares :
    ∀ {I : Type} [inst : Fintype.{0} I] [inst_1 : DecidableEq.{1} I] (q : Nat) (p : (I → Fin q) → Rat),
  @Eq.{1} Rat
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@Fintype.card.{0} I inst))
      (@Thermal.collision I inst inst_1 q p))
    (@Finset.sum.{0, 0} (I → Fin q) Rat Rat.addCommMonoid
      (@Finset.univ.{0} (I → Fin q)
        (@Pi.instFintype.{0, 0} I (fun (a : I) => Fin q) inst_1 inst fun (a : I) => Fin.fintype q))
      fun (k : I → Fin q) =>
      @HPow.hPow.{0, 0, 0} Rat Nat Rat
        (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid)))
        (@Finset.sum.{0, 0} (I → Fin q) Rat Rat.addCommMonoid
          (@Finset.univ.{0} (I → Fin q)
            (@Pi.instFintype.{0, 0} I (fun (a : I) => Fin q) inst_1 inst fun (a : I) => Fin.fintype q))
          fun (x : I → Fin q) =>
          @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (p x) (@Thermal.tensorFeature I inst q x k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Thermal.collision_sum_squares

theorem ComparatorCore.check_Thermal_collision_nonneg :
    ∀ {I : Type} [inst : Fintype.{0} I] [inst_1 : DecidableEq.{1} I] (q : Nat)
  (hq : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
  (p : (I → Fin q) → Rat),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.collision I inst inst_1 q p) := @_root_.Thermal.collision_nonneg

theorem ComparatorCore.check_Thermal_coefficient_nonneg :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.c F T) := @_root_.Thermal.coefficient_nonneg

theorem ComparatorCore.check_Thermal_balanced_coefficient_zero :
    ∀ (F : Thermal.CA) (hb : Thermal.Balanced F) (T : Finset.{0} Thermal.Lattice)
  (ht : @Finset.Nonempty.{0} Thermal.Lattice T),
  @Eq.{1} Rat (Thermal.c F T) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) := @_root_.Thermal.balanced_coefficient_zero

theorem ComparatorCore.check_Thermal_w_sum :
    ∀ (q : Nat) (ε : Rat) (a : Fin q),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0} (Fin q) Rat Rat.addCommMonoid (@Finset.univ.{0} (Fin q) (Fin.fintype q)) fun (b : Fin q) =>
      Thermal.w q ε a b)
    (@Nat.cast.{0} Rat Rat.instNatCast q) := @_root_.Thermal.w_sum

theorem ComparatorCore.check_Thermal_balanced_W :
    ∀ (F : Thermal.CA) (hb : Thermal.Balanced F) (ε : Rat) (C : Finset.{0} Thermal.Lattice),
  @Eq.{1} Rat (Thermal.W F ε C) (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.balanced_W

theorem ComparatorCore.check_Thermal_onto_collision_core :
    ∀ (F : Thermal.CA) (balance : Thermal.CA.Onto F → Thermal.Balanced F) (ho : Thermal.CA.Onto F),
  And
    (∀ (T : Finset.{0} Thermal.Lattice),
      @Finset.Nonempty.{0} Thermal.Lattice T →
        @Eq.{1} Rat (Thermal.c F T) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
    (∀ (ε : Rat) (C : Finset.{0} Thermal.Lattice),
      @Eq.{1} Rat (Thermal.W F ε C) (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) := @_root_.Thermal.onto_collision_core

theorem ComparatorCore.check_Thermal_physical_dimensions :
    And
  (@Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))))
  (And
    (@Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2304) (instOfNatNat (nat_lit 2304))))
    (@Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 66049) (instOfNatNat (nat_lit 66049)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 16908544) (instOfNatNat (nat_lit 16908544))))) := @_root_.Thermal.physical_dimensions

theorem ComparatorCore.check_Thermal_exploration_rational_budget :
    And
  (@Eq.{1} Rat
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 128) (@Rat.instOfNat (nat_lit 128)))
          (@OfNat.ofNat.{0} Rat (nat_lit 961) (@Rat.instOfNat (nat_lit 961)))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Rat (nat_lit 64) (@Rat.instOfNat (nat_lit 64)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 17345) (@Rat.instOfNat (nat_lit 17345)))
      (@OfNat.ofNat.{0} Rat (nat_lit 61504) (@Rat.instOfNat (nat_lit 61504)))))
  (And
    (@LT.lt.{0} Rat Rat.instLT
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 17345) (@Rat.instOfNat (nat_lit 17345)))
        (@OfNat.ofNat.{0} Rat (nat_lit 61504) (@Rat.instOfNat (nat_lit 61504))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))))
    (And
      (@Eq.{1} Rat
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
              (@OfNat.ofNat.{0} Rat (nat_lit 17345) (@Rat.instOfNat (nat_lit 17345)))
              (@OfNat.ofNat.{0} Rat (nat_lit 61504) (@Rat.instOfNat (nat_lit 61504))))))
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 123008) (@Rat.instOfNat (nat_lit 123008)))
          (@OfNat.ofNat.{0} Rat (nat_lit 44159) (@Rat.instOfNat (nat_lit 44159)))))
      (@LT.lt.{0} Rat Rat.instLT
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 123008) (@Rat.instOfNat (nat_lit 123008)))
          (@OfNat.ofNat.{0} Rat (nat_lit 44159) (@Rat.instOfNat (nat_lit 44159))))
        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))))) := @_root_.Thermal.exploration_rational_budget

theorem ComparatorCore.check_Thermal_h_abs_bound :
    ∀ (q : Nat) (hq : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
  (a b : Fin q),
  @LE.le.{0} Rat Rat.instLE (@abs.{0} Rat Rat.instLattice Rat.addGroup (Thermal.h q a b))
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (@Nat.cast.{0} Rat Rat.instNatCast q)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) := @_root_.Thermal.h_abs_bound

theorem ComparatorCore.check_Thermal_collision_upper :
    ∀ {I : Type} [inst : Fintype.{0} I] [inst_1 : DecidableEq.{1} I] (q : Nat)
  (hq : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
  (p : (I → Fin q) → Rat)
  (hp0 :
    ∀ (x : I → Fin q), @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (p x))
  (hp :
    @Eq.{1} Rat
      (@Finset.sum.{0, 0} (I → Fin q) Rat Rat.addCommMonoid
        (@Finset.univ.{0} (I → Fin q)
          (@Pi.instFintype.{0, 0} I (fun (a : I) => Fin q) inst_1 inst fun (a : I) => Fin.fintype q))
        fun (x : I → Fin q) => p x)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))),
  @LE.le.{0} Rat Rat.instLE (@Thermal.collision I inst inst_1 q p)
    (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@Fintype.card.{0} I inst)) := @_root_.Thermal.collision_upper

theorem ComparatorCore.check_Thermal_outputLaw_nonneg :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (a :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          T x) →
      Fin (Thermal.CA.q F)),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.outputLaw F T a) := @_root_.Thermal.outputLaw_nonneg

theorem ComparatorCore.check_Thermal_outputLaw_total :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (a :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)) =>
      Thermal.outputLaw F T a)
    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.outputLaw_total

theorem ComparatorCore.check_Thermal_coefficient_upper_closed :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Rat Rat.instLE (Thermal.c F T)
    (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@Finset.card.{0} Thermal.Lattice T)) := @_root_.Thermal.coefficient_upper_closed

theorem ComparatorCore.check_Thermal_coefficient_empty_closed :
    ∀ (F : Thermal.CA),
  @Eq.{1} Rat
    (Thermal.c F
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} Thermal.Lattice)
        (@Finset.instEmptyCollection.{0} Thermal.Lattice)))
    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.coefficient_empty_closed

theorem ComparatorCore.check_Thermal_local_weight_positive :
    ∀ {F : Thermal.CA} {Q : Nat} (M : Thermal.Model F Q)
  (he :
    And
      (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Thermal.Model.ε F Q M))
      (@LT.lt.{0} Rat Rat.instLT (@Thermal.Model.ε F Q M)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
  (ho :
    ∀ (r : Bool),
      @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Thermal.Model.openWeight F Q M r))
  (hc :
    ∀ (r : Bool),
      @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Thermal.Model.closedScale F Q M r))
  (ξ : Thermal.Config (Thermal.CA.q F) Q) (e : Thermal.Edge),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.localWeight Q F M ξ e) := @_root_.Thermal.local_weight_positive

theorem ComparatorCore.check_Thermal_ising_local_positive :
    ∀ (F : Thermal.CA) (ξ : Thermal.Config (Thermal.CA.q F) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (e : Thermal.Edge),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.localWeight (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) F (Thermal.ising F) ξ e) := @_root_.Thermal.ising_local_positive

theorem ComparatorCore.check_Thermal_potts_local_positive :
    ∀ (F : Thermal.CA) (v : Nat) (ε : Rat)
  (he :
    And (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε)
      (@LT.lt.{0} Rat Rat.instLT ε (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
  (ξ : Thermal.Config (Thermal.CA.q F) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v v))
  (e : Thermal.Edge),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.localWeight (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v v) F (Thermal.potts F v ε)
      ξ e) := @_root_.Thermal.potts_local_positive

theorem ComparatorCore.check_Thermal_epsilonU_pos :
    ∀ (F : Thermal.CA),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.epsilonU F) := @_root_.Thermal.epsilonU_pos

theorem ComparatorCore.check_Thermal_epsilonU_lt_one :
    ∀ (F : Thermal.CA),
  @LT.lt.{0} Rat Rat.instLT (Thermal.epsilonU F) (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.epsilonU_lt_one

theorem ComparatorCore.check_Thermal_magnetic_local_positive :
    ∀ (F : Thermal.CA) (ξ : Thermal.Config (Thermal.CA.q F) (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (e : Thermal.Edge),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.localWeight (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) F (Thermal.magnetic F) ξ e) := @_root_.Thermal.magnetic_local_positive

theorem ComparatorCore.check_Thermal_unique_local_positive :
    ∀ (F : Thermal.CA)
  (ξ : Thermal.Config (Thermal.CA.q F) (@OfNat.ofNat.{0} Nat (nat_lit 66049) (instOfNatNat (nat_lit 66049))))
  (e : Thermal.Edge),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.localWeight (@OfNat.ofNat.{0} Nat (nat_lit 66049) (instOfNatNat (nat_lit 66049))) F
      (Thermal.uniqueModel F) ξ e) := @_root_.Thermal.unique_local_positive

theorem ComparatorCore.check_Thermal_sum_restrict :
    ∀ {α A : Type} [inst : DecidableEq.{1} α] [inst_1 : Fintype.{0} A] (S T : Finset.{0} α)
  (hst :
    @LE.le.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α) (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
      S T)
  (f :
    ((@Subtype.{1} α fun (x : α) =>
          @Membership.mem.{0, 0} α (Finset.{0} α)
            (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
        A) →
      Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} α fun (x : α) =>
          @Membership.mem.{0, 0} α (Finset.{0} α)
            (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
        A)
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} α fun (x : α) =>
            @Membership.mem.{0, 0} α (Finset.{0} α)
              (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
          A)
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} α fun (x : α) =>
            @Membership.mem.{0, 0} α (Finset.{0} α)
              (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
          (fun
              (a :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
            A)
          (fun
              (a b :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
            @Subtype.instDecidableEq.{1} α
              (@Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T)
              inst a b)
          (@Finset.Subtype.fintype.{0} α T)
          fun
            (a :
              @Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
          inst_1))
      fun
        (x :
          (@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
            A) =>
      f
        fun
          (i :
            @Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
        x
          (@Subtype.mk.{1} α
            (fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
            (@Subtype.val.{1} α
              (fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
              i)
            (@hst
              (@Subtype.val.{1} α
                (fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                i)
              (@Subtype.property.{1} α
                (fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                i))))
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
        (@Nat.cast.{0} Rat Rat.instNatCast (@Fintype.card.{0} A inst_1))
        (@Finset.card.{0} α (@SDiff.sdiff.{0} (Finset.{0} α) (@Finset.instSDiff.{0} α inst) T S)))
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} α fun (x : α) =>
            @Membership.mem.{0, 0} α (Finset.{0} α)
              (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
          A)
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
            A)
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
            (fun
                (a :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
              A)
            (fun
                (a b :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
              @Subtype.instDecidableEq.{1} α
                (@Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S)
                inst a b)
            (@Finset.Subtype.fintype.{0} α S)
            fun
              (a :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
            inst_1))
        fun
          (x :
            (@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
              A) =>
        f x)) := @_root_.Thermal.sum_restrict

theorem ComparatorCore.check_Thermal_average_restrict :
    ∀ {α : Type} [inst : DecidableEq.{1} α] (q : Nat)
  (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) (S T : Finset.{0} α)
  (hst :
    @LE.le.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α) (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
      S T)
  (f :
    ((@Subtype.{1} α fun (x : α) =>
          @Membership.mem.{0, 0} α (Finset.{0} α)
            (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
        Fin q) →
      Rat),
  @Eq.{1} Rat
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} α fun (x : α) =>
            @Membership.mem.{0, 0} α (Finset.{0} α)
              (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
          Fin q)
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
            Fin q)
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
            (fun
                (a :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
              Fin q)
            (fun
                (a b :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
              @Subtype.instDecidableEq.{1} α
                (@Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T)
                inst a b)
            (@Finset.Subtype.fintype.{0} α T)
            fun
              (a :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
            Fin.fintype q))
        fun
          (x :
            (@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
              Fin q) =>
        f
          fun
            (i :
              @Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
          x
            (@Subtype.mk.{1} α
              (fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
              (@Subtype.val.{1} α
                (fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                i)
              (@hst
                (@Subtype.val.{1} α
                  (fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                  i)
                (@Subtype.property.{1} α
                  (fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                  i))))
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@Finset.card.{0} α T)))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} α fun (x : α) =>
            @Membership.mem.{0, 0} α (Finset.{0} α)
              (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
          Fin q)
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
            Fin q)
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
            (fun
                (a :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
              Fin q)
            (fun
                (a b :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
              @Subtype.instDecidableEq.{1} α
                (@Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S)
                inst a b)
            (@Finset.Subtype.fintype.{0} α S)
            fun
              (a :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
            Fin.fintype q))
        fun
          (x :
            (@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
              Fin q) =>
        f x)
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@Finset.card.{0} α S))) := @_root_.Thermal.average_restrict

theorem ComparatorCore.check_Thermal_inputSupport_mono :
    ∀ (F : Thermal.CA) {S T : Finset.{0} Thermal.Lattice}
  (hst :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S T),
  @LE.le.{0} (Finset.{0} Thermal.Lattice)
    (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
    (Thermal.inputSupport F S) (Thermal.inputSupport F T) := @_root_.Thermal.inputSupport_mono

theorem ComparatorCore.check_Thermal_blockMap_restrict :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hst :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S T)
  (x :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (Thermal.inputSupport F T) x) →
      Fin (Thermal.CA.q F)),
  @Eq.{1}
    ((i :
        @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
      Fin (Thermal.CA.q F))
    (fun
        (i :
          @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) =>
      Thermal.blockMap F T x
        (@Subtype.mk.{1} Thermal.Lattice
          (fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (@Subtype.val.{1} Thermal.Lattice
            (fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x)
            i)
          (@hst
            (@Subtype.val.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x)
              i)
            (@Subtype.property.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x)
              i))))
    (Thermal.blockMap F S
      fun
        (j :
          @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F S) x) =>
      x
        (@Subtype.mk.{1} Thermal.Lattice
          (fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x)
          (@Subtype.val.{1} Thermal.Lattice
            (fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F S) x)
            j)
          (@Thermal.inputSupport_mono F S T hst
            (@Subtype.val.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F S) x)
              j)
            (@Subtype.property.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F S) x)
              j)))) := @_root_.Thermal.blockMap_restrict

theorem ComparatorCore.check_Thermal_outputLaw_expect :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (f :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F)) →
      Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (a :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F T a) (f a))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x) →
          Fin (Thermal.CA.q F))
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T))
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice (Thermal.inputSupport F T))
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (x :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T) x) →
              Fin (Thermal.CA.q F)) =>
        f (Thermal.blockMap F T x))
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
        (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
        (@Finset.card.{0} Thermal.Lattice (Thermal.inputSupport F T)))) := @_root_.Thermal.outputLaw_expect

theorem ComparatorCore.check_Thermal_outputLaw_restrict_expect :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hst :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S T)
  (f :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
        Fin (Thermal.CA.q F)) →
      Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (b :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F T b)
        (f
          fun
            (i :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x) =>
          b
            (@Subtype.mk.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x)
              (@Subtype.val.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x)
                i)
              (@hst
                (@Subtype.val.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x)
                  i)
                (@Subtype.property.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x)
                  i)))))
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice S)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (a :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F S a) (f a)) := @_root_.Thermal.outputLaw_restrict_expect

theorem ComparatorCore.check_Thermal_outputLaw_marginal :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hST :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S T)
  (a :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          S x) →
      Fin (Thermal.CA.q F)),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (b :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F T b)
        (@ite.{1} Rat
          (@Eq.{1}
            ((i :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) →
              Fin (Thermal.CA.q F))
            (fun
                (i :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              b
                (@Subtype.mk.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x)
                  (@Subtype.val.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i)
                  (@hST
                    (@Subtype.val.{1} Thermal.Lattice
                      (fun (x : Thermal.Lattice) =>
                        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                            (@Finset.instSetLike.{0} Thermal.Lattice))
                          S x)
                      i)
                    (@Subtype.property.{1} Thermal.Lattice
                      (fun (x : Thermal.Lattice) =>
                        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                            (@Finset.instSetLike.{0} Thermal.Lattice))
                          S x)
                      i))))
            a)
          (@Fintype.decidablePiFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              instDecidableEqFin (Thermal.CA.q F))
            (@Finset.Subtype.fintype.{0} Thermal.Lattice S)
            (fun
                (i :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              b
                (@Subtype.mk.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x)
                  (@Subtype.val.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i)
                  (@hST
                    (@Subtype.val.{1} Thermal.Lattice
                      (fun (x : Thermal.Lattice) =>
                        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                            (@Finset.instSetLike.{0} Thermal.Lattice))
                          S x)
                      i)
                    (@Subtype.property.{1} Thermal.Lattice
                      (fun (x : Thermal.Lattice) =>
                        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                            (@Finset.instSetLike.{0} Thermal.Lattice))
                          S x)
                      i))))
            a)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
    (Thermal.outputLaw F S a) := @_root_.Thermal.outputLaw_marginal

theorem ComparatorCore.check_Thermal_outputLaw_integer_numerator :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (a :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          T x) →
      Fin (Thermal.CA.q F)),
  @Eq.{1} Rat (Thermal.outputLaw F T a)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Int.cast.{0} Rat Rat.instIntCast (Thermal.outputCount F T a))
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
        (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
        (@Finset.card.{0} Thermal.Lattice (Thermal.inputSupport F T)))) := @_root_.Thermal.outputLaw_integer_numerator

theorem ComparatorCore.check_Thermal_coefficient_integer_numerator :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @Eq.{1} Rat (Thermal.c F T)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Int.cast.{0} Rat Rat.instIntCast (Thermal.collisionNumerator F T))
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
        (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Finset.card.{0} Thermal.Lattice (Thermal.inputSupport F T))))) := @_root_.Thermal.coefficient_integer_numerator

theorem ComparatorCore.check_Thermal_coefficient_denominator :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @Exists.{1} Int fun (k : Int) =>
    @Eq.{1} Rat (Thermal.c F T)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) (@Int.cast.{0} Rat Rat.instIntCast k)
        (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
          (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{0} Thermal.Lattice (Thermal.inputSupport F T))))) := @_root_.Thermal.coefficient_denominator

theorem ComparatorCore.check_Thermal_inputSupport_card :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} Thermal.Lattice (Thermal.inputSupport F T))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Finset.card.{0} Thermal.Lattice (Thermal.CA.N F))
      (@Finset.card.{0} Thermal.Lattice T)) := @_root_.Thermal.inputSupport_card

theorem ComparatorCore.check_Thermal_coefficient_lower :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (hc : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.c F T)),
  @LE.le.{0} Rat Rat.instLE
    (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
      (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
      (@Neg.neg.{0} Int Int.instNegInt
        (@Nat.cast.{0} Int instNatCastInt
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{0} Thermal.Lattice (Thermal.CA.N F)))
            (@Finset.card.{0} Thermal.Lattice T)))))
    (Thermal.c F T) := @_root_.Thermal.coefficient_lower

theorem ComparatorCore.check_Thermal_outputLaw_pair_restrict_expect :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hst :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S T)
  (f :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
        Fin (Thermal.CA.q F)) →
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) →
          Fin (Thermal.CA.q F)) →
        Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (b :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)) =>
      @Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T)
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (d :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) →
              Fin (Thermal.CA.q F)) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F T b)
            (Thermal.outputLaw F T d))
          (f
            (fun
                (i :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              b
                (@Subtype.mk.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x)
                  (@Subtype.val.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i)
                  (@hst
                    (@Subtype.val.{1} Thermal.Lattice
                      (fun (x : Thermal.Lattice) =>
                        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                            (@Finset.instSetLike.{0} Thermal.Lattice))
                          S x)
                      i)
                    (@Subtype.property.{1} Thermal.Lattice
                      (fun (x : Thermal.Lattice) =>
                        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                            (@Finset.instSetLike.{0} Thermal.Lattice))
                          S x)
                      i))))
            fun
              (i :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            d
              (@Subtype.mk.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x)
                (@Subtype.val.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x)
                  i)
                (@hst
                  (@Subtype.val.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i)
                  (@Subtype.property.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i)))))
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice S)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (a :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x) →
            Fin (Thermal.CA.q F)) =>
      @Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) →
          Fin (Thermal.CA.q F))
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S)
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice S)
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (e :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x) →
              Fin (Thermal.CA.q F)) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F S a)
            (Thermal.outputLaw F S e))
          (f a e)) := @_root_.Thermal.outputLaw_pair_restrict_expect

theorem ComparatorCore.check_Thermal_extendPattern_on :
    ∀ (F : Thermal.CA) (C : Finset.{0} Thermal.Lattice)
  (x :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          C x) →
      Fin (Thermal.CA.q F))
  (i :
    @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
          (@Finset.instSetLike.{0} Thermal.Lattice))
        C x),
  @Eq.{1} (Fin (Thermal.CA.q F))
    (Thermal.extendPattern F C x
      (@Subtype.val.{1} Thermal.Lattice
        (fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            C x)
        i))
    (x i) := @_root_.Thermal.extendPattern_on

theorem ComparatorCore.check_Thermal_subset_collision :
    ∀ (F : Thermal.CA) (S C : Finset.{0} Thermal.Lattice)
  (hst :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S C),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            C x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              C x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              C x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    C x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    C x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                C)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice C)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  C x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (x :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                C x) →
            Fin (Thermal.CA.q F)) =>
      @Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              C x) →
          Fin (Thermal.CA.q F))
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                C x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                C x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      C x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      C x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  C)
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice C)
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    C x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (y :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  C x) →
              Fin (Thermal.CA.q F)) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F C x)
            (Thermal.outputLaw F C y))
          (@Finset.prod.{0, 0} Thermal.Lattice Rat Rat.commMonoid S fun (i : Thermal.Lattice) =>
            Thermal.h (Thermal.CA.q F) (Thermal.extendPattern F C x i) (Thermal.extendPattern F C y i)))
    (Thermal.c F S) := @_root_.Thermal.subset_collision

theorem ComparatorCore.check_Thermal_W_expansion :
    ∀ (F : Thermal.CA) (ε : Rat) (C : Finset.{0} Thermal.Lattice),
  @Eq.{1} Rat (Thermal.W F ε C)
    (@Thermal.expansion Thermal.Lattice
      (fun (a b : Thermal.Lattice) => @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
      (Thermal.c F) ε C) := @_root_.Thermal.W_expansion

theorem ComparatorCore.check_Thermal_zero_coefficient_tensorMoment :
    ∀ (F : Thermal.CA) (S : Finset.{0} Thermal.Lattice)
  (hz : @Eq.{1} Rat (Thermal.c F S) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
  (k :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          S x) →
      Fin (Thermal.CA.q F)),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice S)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (x :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F S x)
        (@Thermal.tensorFeature
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice S) (Thermal.CA.q F) x k))
    (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) := @_root_.Thermal.zero_coefficient_tensorMoment

theorem ComparatorCore.check_Thermal_delta_tensor :
    ∀ {I : Type} [inst : Fintype.{0} I] [DecidableEq.{1} I] (q : Nat) (x a : I → Fin q),
  @Eq.{1} Rat
    (@Finset.prod.{0, 0} I Rat Rat.commMonoid (@Finset.univ.{0} I inst) fun (i : I) =>
      @HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (Thermal.h q (x i) (a i)))
    (@ite.{1} Rat (@Eq.{1} (I → Fin q) x a)
      (@Fintype.decidablePiFintype.{0, 0} I (fun (a : I) => Fin q) (fun (a : I) => instDecidableEqFin q) inst x a)
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@Fintype.card.{0} I inst))
      (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) := @_root_.Thermal.delta_tensor

theorem ComparatorCore.check_Thermal_zero_coefficients_uniform :
    ∀ (F : Thermal.CA)
  (hz :
    ∀ (S : Finset.{0} Thermal.Lattice),
      @Finset.Nonempty.{0} Thermal.Lattice S →
        @Eq.{1} Rat (Thermal.c F S) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))),
  Thermal.Balanced F := @_root_.Thermal.zero_coefficients_uniform

theorem ComparatorCore.check_Thermal_Algorithm_prim_pow :
    @Primrec₂.{0, 0, 0} Nat Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  fun (a b : Nat) =>
  @HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) a b := @_root_.Thermal.Algorithm.prim_pow

theorem ComparatorCore.check_Thermal_Algorithm_prim_natCast :
    @Primrec.{0, 0} Nat Int (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) fun (n : Nat) => @Nat.cast.{0} Int instNatCastInt n := @_root_.Thermal.Algorithm.prim_natCast

theorem ComparatorCore.check_Thermal_Algorithm_prim_negSucc :
    @Primrec.{0, 0} Nat Int (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) Int.negSucc := @_root_.Thermal.Algorithm.prim_negSucc

theorem ComparatorCore.check_Thermal_Algorithm_prim_intSplit :
    @Primrec.{0, 0} Int (Sum.{0, 0} Nat Nat) (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  (@Primcodable.sum.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} Int (Sum.{0, 0} Nat Nat)) Int (fun (x : Int) => Sum.{0, 0} Nat Nat)
    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} Int (Sum.{0, 0} Nat Nat)) Int (Sum.{0, 0} Nat Nat)
      (@Equiv.instEquivLike.{1, 1} Int (Sum.{0, 0} Nat Nat)))
    Equiv.intEquivNatSumNat) := @_root_.Thermal.Algorithm.prim_intSplit

theorem ComparatorCore.check_Thermal_Algorithm_prim_intCases :
    ∀ {α β : Type} [inst : Primcodable.{0} α] [inst_1 : Primcodable.{0} β] {f : α → Int} {g h : α → Nat → β}
  (hf : @Primrec.{0, 0} α Int inst (@Primcodable.ofDenumerable.{0} Int Denumerable.int) f)
  (hg : @Primrec₂.{0, 0, 0} α Nat β inst (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) inst_1 g)
  (hh : @Primrec₂.{0, 0, 0} α Nat β inst (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) inst_1 h),
  @Primrec.{0, 0} α β inst inst_1 fun (a : α) => @Int.casesOn.{1} (fun (x : Int) => β) (f a) (g a) (h a) := @_root_.Thermal.Algorithm.prim_intCases

theorem ComparatorCore.check_Thermal_Algorithm_prim_natAbs :
    @Primrec.{0, 0} Int Nat (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Int.natAbs := @_root_.Thermal.Algorithm.prim_natAbs

theorem ComparatorCore.check_Thermal_Algorithm_prim_neg :
    @Primrec.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) fun (n : Int) => @Neg.neg.{0} Int Int.instNegInt n := @_root_.Thermal.Algorithm.prim_neg

theorem ComparatorCore.check_Thermal_Algorithm_prim_subNatNat :
    @Primrec₂.{0, 0, 0} Nat Nat Int (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  Int.subNatNat := @_root_.Thermal.Algorithm.prim_subNatNat

theorem ComparatorCore.check_Thermal_Algorithm_prim_intAdd :
    @Primrec₂.{0, 0, 0} Int Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  fun (a b : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) a b := @_root_.Thermal.Algorithm.prim_intAdd

theorem ComparatorCore.check_Thermal_Algorithm_prim_intSub :
    @Primrec₂.{0, 0, 0} Int Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  fun (a b : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a b := @_root_.Thermal.Algorithm.prim_intSub

theorem ComparatorCore.check_Thermal_Algorithm_prim_evalLocal :
    @Primrec.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))) Nat
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Nat) (List.{0} Nat)
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  fun (p : Prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat))) =>
  Thermal.Algorithm.evalLocal (@Prod.fst.{0, 0} Nat (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat)) p)
    (@Prod.fst.{0, 0} (List.{0} Nat) (List.{0} Nat)
      (@Prod.snd.{0, 0} Nat (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat)) p))
    (@Prod.snd.{0, 0} (List.{0} Nat) (List.{0} Nat)
      (@Prod.snd.{0, 0} Nat (Prod.{0, 0} (List.{0} Nat) (List.{0} Nat)) p)) := @_root_.Thermal.Algorithm.prim_evalLocal

theorem ComparatorCore.check_Thermal_Algorithm_prim_mem :
    ∀ {α : Type} [inst : Primcodable.{0} α] [DecidableEq.{1} α],
  @PrimrecRel.{0, 0} α (List.{0} α) inst (@Primcodable.list.{0} α inst) fun (a : α) (l : List.{0} α) =>
    @Membership.mem.{0, 0} α (List.{0} α) (@List.instMembership.{0} α) l a := @_root_.Thermal.Algorithm.prim_mem

theorem ComparatorCore.check_Thermal_Algorithm_prim_dedup :
    ∀ {α : Type} [inst : Primcodable.{0} α] [inst_1 : DecidableEq.{1} α],
  @Primrec.{0, 0} (List.{0} α) (List.{0} α) (@Primcodable.list.{0} α inst) (@Primcodable.list.{0} α inst)
    (@List.dedup.{0} α inst_1) := @_root_.Thermal.Algorithm.prim_dedup

theorem ComparatorCore.check_Thermal_Algorithm_prim_maximum :
    @Primrec.{0, 0} (List.{0} Nat) Nat (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.maximum := @_root_.Thermal.Algorithm.prim_maximum

theorem ComparatorCore.check_Thermal_Algorithm_prim_distance :
    @Primrec₂.{0, 0, 0} Thermal.Algorithm.Point Thermal.Algorithm.Point Nat
  (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Int Denumerable.int))
  (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Int Denumerable.int))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.distance := @_root_.Thermal.Algorithm.prim_distance

theorem ComparatorCore.check_Thermal_Algorithm_prim_diameter :
    @Primrec.{0, 0} (List.{0} Thermal.Algorithm.Point) Nat
  (@Primcodable.list.{0} Thermal.Algorithm.Point
    (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
      (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.diameter := @_root_.Thermal.Algorithm.prim_diameter

theorem ComparatorCore.check_Thermal_Algorithm_prim_neighborhood :
    @Primrec.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.list.{0} Thermal.Algorithm.Point
    (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
      (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
  Thermal.Algorithm.neighborhood := @_root_.Thermal.Algorithm.prim_neighborhood

theorem ComparatorCore.check_Thermal_Algorithm_prim_qValue :
    @Primrec.{0, 0} Thermal.Algorithm.Code Nat
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.qValue := @_root_.Thermal.Algorithm.prim_qValue

theorem ComparatorCore.check_Thermal_Algorithm_prim_inputDigit :
    @Primrec.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat (Prod.{0, 0} Thermal.Algorithm.Point Nat))) Nat
  (@Primcodable.prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat (Prod.{0, 0} Thermal.Algorithm.Point Nat))
    (@Primcodable.prod.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} Thermal.Algorithm.Point Nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} Thermal.Algorithm.Point Nat
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int))
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.inputDigit := @_root_.Thermal.Algorithm.prim_inputDigit

theorem ComparatorCore.check_Thermal_Algorithm_prim_ruleDigit :
    @Primrec.{0, 0} (Prod.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) Nat
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.ruleDigit := @_root_.Thermal.Algorithm.prim_ruleDigit

theorem ComparatorCore.check_Thermal_Algorithm_prim_ncard :
    @Primrec.{0, 0} Thermal.Algorithm.Code Nat
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.ncard := @_root_.Thermal.Algorithm.prim_ncard

theorem ComparatorCore.check_Thermal_Algorithm_prim_ruleRadius :
    @Primrec.{0, 0} Thermal.Algorithm.Code Nat
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.ruleRadius := @_root_.Thermal.Algorithm.prim_ruleRadius

theorem ComparatorCore.check_Thermal_Algorithm_prim_denominator :
    @Primrec.{0, 0} Thermal.Algorithm.Code Nat
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.denominator := @_root_.Thermal.Algorithm.prim_denominator

theorem ComparatorCore.check_Thermal_Algorithm_prim_uniqueDenominator :
    @Primrec.{0, 0} Thermal.Algorithm.Code Nat
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.uniqueDenominator := @_root_.Thermal.Algorithm.prim_uniqueDenominator

theorem ComparatorCore.check_Thermal_Algorithm_prim_fraction :
    @Primrec.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool))))
  (Prod.{0, 0} Int Nat)
  (@Primcodable.prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool)))
    (@Primcodable.prod.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} Bool Bool) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.prod.{0, 0} Bool Bool Primcodable.bool Primcodable.bool))))
  (@Primcodable.prod.{0, 0} Int Nat (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  Thermal.Algorithm.fraction := @_root_.Thermal.Algorithm.prim_fraction

theorem ComparatorCore.check_Thermal_Algorithm_prim_intSign :
    @Primrec.{0, 0} Int Bool (@Primcodable.ofDenumerable.{0} Int Denumerable.int) Primcodable.bool fun (z : Int) =>
  @Decidable.decide (@LT.lt.{0} Int Int.instLTInt z (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (Int.decLt z (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := @_root_.Thermal.Algorithm.prim_intSign

theorem ComparatorCore.check_Thermal_Algorithm_prim_intPositive :
    @Primrec.{0, 0} Int Bool (@Primcodable.ofDenumerable.{0} Int Denumerable.int) Primcodable.bool fun (z : Int) =>
  @Decidable.decide (@LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) z)
    (Int.decLt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) z) := @_root_.Thermal.Algorithm.prim_intPositive

theorem ComparatorCore.check_Thermal_Algorithm_prim_intMul :
    @Primrec₂.{0, 0, 0} Int Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
  fun (a b : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) a b := @_root_.Thermal.Algorithm.prim_intMul

theorem ComparatorCore.check_Thermal_Algorithm_prim_pointAdd :
    @Primrec₂.{0, 0, 0} Thermal.Algorithm.Point Thermal.Algorithm.Point Thermal.Algorithm.Point
  (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Int Denumerable.int))
  (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Int Denumerable.int))
  (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Int Denumerable.int))
  fun (a b : Thermal.Algorithm.Point) =>
  @HAdd.hAdd.{0, 0, 0} Thermal.Algorithm.Point Thermal.Algorithm.Point Thermal.Algorithm.Point
    (@instHAdd.{0} Thermal.Algorithm.Point (@Prod.instAdd.{0, 0} Int Int Int.instAdd Int.instAdd)) a b := @_root_.Thermal.Algorithm.prim_pointAdd

theorem ComparatorCore.check_Thermal_Algorithm_prim_assignmentDigit :
    @Primrec.{0, 0}
  (Prod.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)) (Prod.{0, 0} Nat Thermal.Algorithm.Point)) Nat
  (@Primcodable.prod.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
    (Prod.{0, 0} Nat Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
    (@Primcodable.prod.{0, 0} Nat Thermal.Algorithm.Point (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.assignmentDigit := @_root_.Thermal.Algorithm.prim_assignmentDigit

theorem ComparatorCore.check_Thermal_Algorithm_prim_evalAt :
    @Primrec.{0, 0} Thermal.Algorithm.AtInput Nat
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code
    (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (Prod.{0, 0} Nat Thermal.Algorithm.Point))
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
      (@Primcodable.prod.{0, 0} Nat Thermal.Algorithm.Point (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.evalAt := @_root_.Thermal.Algorithm.prim_evalAt

theorem ComparatorCore.check_Thermal_Algorithm_prim_inputList :
    @Primrec.{0, 0} Thermal.Algorithm.FiniteInput (List.{0} Thermal.Algorithm.Point)
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.list.{0} Thermal.Algorithm.Point
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  (@Primcodable.list.{0} Thermal.Algorithm.Point
    (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
      (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
  Thermal.Algorithm.inputList := @_root_.Thermal.Algorithm.prim_inputList

theorem ComparatorCore.check_Thermal_Algorithm_prim_intKernel :
    @Primrec.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) Int
  (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.prod.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) =>
  Thermal.Algorithm.intKernel (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p)
    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) p))
    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) p)) := @_root_.Thermal.Algorithm.prim_intKernel

theorem ComparatorCore.check_Thermal_Algorithm_prim_pairTerm :
    @Primrec.{0, 0} Thermal.Algorithm.PairInput Int
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.FiniteInput (Prod.{0, 0} Nat Nat)
    (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
      (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
          (@Primcodable.list.{0} Thermal.Algorithm.Point
            (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
              (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
          (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
      (@Primcodable.list.{0} Thermal.Algorithm.Point
        (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
          (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
    (@Primcodable.prod.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) Thermal.Algorithm.pairTerm := @_root_.Thermal.Algorithm.prim_pairTerm

theorem ComparatorCore.check_Thermal_Algorithm_prim_assignmentCount :
    @Primrec.{0, 0} Thermal.Algorithm.FiniteInput Nat
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.list.{0} Thermal.Algorithm.Point
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.assignmentCount := @_root_.Thermal.Algorithm.prim_assignmentCount

theorem ComparatorCore.check_Thermal_Algorithm_prim_finiteNumerator :
    @Primrec.{0, 0} Thermal.Algorithm.FiniteInput Int
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.list.{0} Thermal.Algorithm.Point
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  (@Primcodable.ofDenumerable.{0} Int Denumerable.int) Thermal.Algorithm.finiteNumerator := @_root_.Thermal.Algorithm.prim_finiteNumerator

theorem ComparatorCore.check_Thermal_patternEquiv_val :
    ∀ (q : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l)
  (n :
    Fin
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
        (@List.length.{0} Thermal.Lattice l)))
  (i :
    @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
          (@Finset.instSetLike.{0} Thermal.Lattice))
        (@List.toFinset.{0} Thermal.Lattice
          (fun (a b : Thermal.Lattice) =>
            @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
          l)
        x),
  @Eq.{1} Nat
    (@Fin.val q
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1}
          (Fin
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
              (@List.length.{0} Thermal.Lattice l)))
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l)
                x) →
            Fin q))
        (Fin
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
            (@List.length.{0} Thermal.Lattice l)))
        (fun
            (x :
              Fin
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                  (@List.length.{0} Thermal.Lattice l))) =>
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l)
                x) →
            Fin q)
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1}
            (Fin
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@List.length.{0} Thermal.Lattice l)))
            ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l)
                  x) →
              Fin q))
          (Fin
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
              (@List.length.{0} Thermal.Lattice l)))
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l)
                x) →
            Fin q)
          (@Equiv.instEquivLike.{1, 1}
            (Fin
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@List.length.{0} Thermal.Lattice l)))
            ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l)
                  x) →
              Fin q)))
        (Thermal.patternEquiv q l hl) n i))
    (Thermal.Algorithm.assignmentDigit
      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
        (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) q l)
        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point
          (@Fin.val
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
              (@List.length.{0} Thermal.Lattice l))
            n)
          (@Subtype.val.{1} Thermal.Lattice
            (fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l)
                x)
            i)))) := @_root_.Thermal.patternEquiv_val

theorem ComparatorCore.check_Thermal_inputList_set :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice),
  @Eq.{1} (Finset.{0} Thermal.Algorithm.Point)
    (@List.toFinset.{0} Thermal.Algorithm.Point
      (fun (a b : Thermal.Algorithm.Point) =>
        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
      (Thermal.Algorithm.inputList (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
    (Thermal.inputSupport (Thermal.decodeRule a)
      (@List.toFinset.{0} Thermal.Lattice
        (fun (a b : Thermal.Lattice) => @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        l)) := @_root_.Thermal.inputList_set

theorem ComparatorCore.check_Thermal_evalAt_correct :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice) (n : Nat) (i : Thermal.Lattice),
  @Eq.{1} Nat
    (Thermal.Algorithm.evalAt
      (@Prod.mk.{0, 0} Thermal.Algorithm.Code
        (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (Prod.{0, 0} Nat Thermal.Algorithm.Point)) a
        (@Prod.mk.{0, 0} (List.{0} Thermal.Algorithm.Point) (Prod.{0, 0} Nat Thermal.Algorithm.Point) l
          (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n i))))
    (@Fin.val (Thermal.CA.q (Thermal.decodeRule a))
      (Thermal.CA.global (Thermal.decodeRule a)
        (fun (j : Thermal.Lattice) =>
          @Fin.mk (Thermal.CA.q (Thermal.decodeRule a))
            (Thermal.Algorithm.assignmentDigit
              (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j)))
            (@Nat.mod_lt
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@Prod.fst.{0, 0} Nat Thermal.Algorithm.Point
                  (@Prod.snd.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                    (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                    (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                      (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                      (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                      (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j))))
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@Prod.fst.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)
                    (@Prod.fst.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                      (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                        (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j))))
                  (@List.idxOf.{0} Thermal.Algorithm.Point
                    (@instBEqProd.{0, 0} Int Int
                      (@Std.PreorderPackage.toBEq.{0} Int
                        (@Std.LinearPreorderPackage.toPreorderPackage.{0} Int
                          (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} Int Int.instLinearOrderPackage)))
                      (@Std.PreorderPackage.toBEq.{0} Int
                        (@Std.LinearPreorderPackage.toPreorderPackage.{0} Int
                          (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} Int Int.instLinearOrderPackage))))
                    (@Prod.snd.{0, 0} Nat Thermal.Algorithm.Point
                      (@Prod.snd.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                        (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                          (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                          (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                          (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j))))
                    (@Prod.snd.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)
                      (@Prod.fst.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                        (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                          (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                          (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                          (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j)))))))
              (@Prod.fst.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)
                (@Prod.fst.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                  (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                  (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                    (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                    (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                    (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j))))
              (@id.{0}
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Prod.fst.{0, 0} Nat (List.{0} Thermal.Algorithm.Point)
                    (@Prod.fst.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                      (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat (List.{0} Thermal.Algorithm.Point))
                        (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (Thermal.Algorithm.qValue a) l)
                        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n j)))))
                (@Decidable.byContradiction
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Prod.fst.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat)) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Prod.fst.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat)) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  fun
                    (a_1 :
                      Not
                        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@Prod.fst.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat)) a)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) =>
                  Thermal.evalAt_correct._proof_1 a a_1))))
        i)) := @_root_.Thermal.evalAt_correct

theorem ComparatorCore.check_Thermal_outputCount_expect :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (f :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F)) →
      Int),
  @Eq.{1} Int
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      Int Int.instAddCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T)
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (a :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (Thermal.outputCount F T a) (f a))
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            (Thermal.inputSupport F T) x) →
        Fin (Thermal.CA.q F))
      Int Int.instAddCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T))
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice (Thermal.inputSupport F T))
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T) x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (x :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x) →
            Fin (Thermal.CA.q F)) =>
      f (Thermal.blockMap F T x)) := @_root_.Thermal.outputCount_expect

theorem ComparatorCore.check_Thermal_collisionNumerator_input :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @Eq.{1} Int (Thermal.collisionNumerator F T)
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            (Thermal.inputSupport F T) x) →
        Fin (Thermal.CA.q F))
      Int Int.instAddCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T))
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice (Thermal.inputSupport F T))
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T) x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (x :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x) →
            Fin (Thermal.CA.q F)) =>
      @Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x) →
          Fin (Thermal.CA.q F))
        Int Int.instAddCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T))
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice (Thermal.inputSupport F T))
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (y :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T) x) →
              Fin (Thermal.CA.q F)) =>
        @Finset.prod.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x)
          Int Int.instCommMonoid
          (@Finset.univ.{0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice T))
          fun
            (i :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) =>
          Thermal.integerKernel (Thermal.CA.q F) (Thermal.blockMap F T x i) (Thermal.blockMap F T y i)) := @_root_.Thermal.collisionNumerator_input

theorem ComparatorCore.check_Thermal_inputAssignmentEquiv_apply :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice)
  (n :
    Fin
      (Thermal.Algorithm.assignmentCount
        (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l))),
  @Eq.{1}
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (Thermal.inputSupport (Thermal.decodeRule a)
            (@List.toFinset.{0} Thermal.Lattice
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              l))
          x) →
      Fin (Thermal.CA.q (Thermal.decodeRule a)))
    (@DFunLike.coe.{1, 1, 1}
      (Equiv.{1, 1}
        (Fin
          (Thermal.Algorithm.assignmentCount
            (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport (Thermal.decodeRule a)
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l))
              x) →
          Fin (Thermal.CA.q (Thermal.decodeRule a))))
      (Fin
        (Thermal.Algorithm.assignmentCount
          (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
      (fun
          (x :
            Fin
              (Thermal.Algorithm.assignmentCount
                (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l))) =>
        (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport (Thermal.decodeRule a)
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l))
              x) →
          Fin (Thermal.CA.q (Thermal.decodeRule a)))
      (@EquivLike.toFunLike.{1, 1, 1}
        (Equiv.{1, 1}
          (Fin
            (Thermal.Algorithm.assignmentCount
              (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport (Thermal.decodeRule a)
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l))
                x) →
            Fin (Thermal.CA.q (Thermal.decodeRule a))))
        (Fin
          (Thermal.Algorithm.assignmentCount
            (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport (Thermal.decodeRule a)
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l))
              x) →
          Fin (Thermal.CA.q (Thermal.decodeRule a)))
        (@Equiv.instEquivLike.{1, 1}
          (Fin
            (Thermal.Algorithm.assignmentCount
              (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport (Thermal.decodeRule a)
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l))
                x) →
            Fin (Thermal.CA.q (Thermal.decodeRule a)))))
      (Thermal.inputAssignmentEquiv a l) n)
    (Thermal.inputAssignment a l
      (@Fin.val
        (Thermal.Algorithm.assignmentCount
          (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l))
        n)) := @_root_.Thermal.inputAssignmentEquiv_apply

theorem ComparatorCore.check_Thermal_evalAt_inputAssignment :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice) (n : Nat)
  (i :
    @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
          (@Finset.instSetLike.{0} Thermal.Lattice))
        (@List.toFinset.{0} Thermal.Lattice
          (fun (a b : Thermal.Lattice) =>
            @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
          l)
        x),
  @Eq.{1} Nat
    (Thermal.Algorithm.evalAt
      (@Prod.mk.{0, 0} Thermal.Algorithm.Code
        (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (Prod.{0, 0} Nat Thermal.Algorithm.Point)) a
        (@Prod.mk.{0, 0} (List.{0} Thermal.Algorithm.Point) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
          (Thermal.Algorithm.inputList (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l))
          (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n
            (@Subtype.val.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l)
                  x)
              i)))))
    (@Fin.val (Thermal.CA.q (Thermal.decodeRule a))
      (Thermal.blockMap (Thermal.decodeRule a)
        (@List.toFinset.{0} Thermal.Lattice
          (fun (a b : Thermal.Lattice) =>
            @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
          l)
        (Thermal.inputAssignment a l n) i)) := @_root_.Thermal.evalAt_inputAssignment

theorem ComparatorCore.check_Thermal_pairTerm_correct :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l) (n m : Nat),
  @Eq.{1} Int
    (Thermal.Algorithm.pairTerm
      (@Prod.mk.{0, 0} Thermal.Algorithm.FiniteInput (Prod.{0, 0} Nat Nat)
        (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l) (@Prod.mk.{0, 0} Nat Nat n m)))
    (@Finset.prod.{0, 0}
      (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (@List.toFinset.{0} Thermal.Lattice
            (fun (a b : Thermal.Lattice) =>
              @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
            l)
          x)
      Int Int.instCommMonoid
      (@Finset.univ.{0}
        (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            (@List.toFinset.{0} Thermal.Lattice
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              l)
            x)
        (@Finset.Subtype.fintype.{0} Thermal.Lattice
          (@List.toFinset.{0} Thermal.Lattice
            (fun (a b : Thermal.Lattice) =>
              @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
            l)))
      fun
        (i :
          @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (@List.toFinset.{0} Thermal.Lattice
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                l)
              x) =>
      Thermal.integerKernel (Thermal.CA.q (Thermal.decodeRule a))
        (Thermal.blockMap (Thermal.decodeRule a)
          (@List.toFinset.{0} Thermal.Lattice
            (fun (a b : Thermal.Lattice) =>
              @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
            l)
          (Thermal.inputAssignment a l n) i)
        (Thermal.blockMap (Thermal.decodeRule a)
          (@List.toFinset.{0} Thermal.Lattice
            (fun (a b : Thermal.Lattice) =>
              @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
            l)
          (Thermal.inputAssignment a l m) i)) := @_root_.Thermal.pairTerm_correct

theorem ComparatorCore.check_Thermal_foldr_range_sum :
    ∀ (N : Nat) (f : Nat → Int),
  @Eq.{1} Int
    (@List.foldr.{0, 0} Int Int
      (fun (x1 x2 : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x1 x2)
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.map.{0, 0} Nat Int f (List.range N)))
    (@Finset.sum.{0, 0} Nat Int Int.instAddCommMonoid (Finset.range N) fun (n : Nat) => f n) := @_root_.Thermal.foldr_range_sum

theorem ComparatorCore.check_Thermal_sum_inputAssignment :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice)
  (f :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            (Thermal.inputSupport (Thermal.decodeRule a)
              (@List.toFinset.{0} Thermal.Lattice
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                l))
            x) →
        Fin (Thermal.CA.q (Thermal.decodeRule a))) →
      Int),
  @Eq.{1} Int
    (@Finset.sum.{0, 0} Nat Int Int.instAddCommMonoid
      (Finset.range
        (Thermal.Algorithm.assignmentCount
          (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
      fun (n : Nat) => f (Thermal.inputAssignment a l n))
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            (Thermal.inputSupport (Thermal.decodeRule a)
              (@List.toFinset.{0} Thermal.Lattice
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                l))
            x) →
        Fin (Thermal.CA.q (Thermal.decodeRule a)))
      Int Int.instAddCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport (Thermal.decodeRule a)
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l))
              x) →
          Fin (Thermal.CA.q (Thermal.decodeRule a)))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport (Thermal.decodeRule a)
                (@List.toFinset.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  l))
              x)
          (fun
              (a_1 :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport (Thermal.decodeRule a)
                      (@List.toFinset.{0} Thermal.Lattice
                        (fun (a b : Thermal.Lattice) =>
                          @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                        l))
                    x) =>
            Fin (Thermal.CA.q (Thermal.decodeRule a)))
          (fun
              (a_1 b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport (Thermal.decodeRule a)
                      (@List.toFinset.{0} Thermal.Lattice
                        (fun (a b : Thermal.Lattice) =>
                          @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                        l))
                    x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport (Thermal.decodeRule a)
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l)))
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a_1 b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice
            (Thermal.inputSupport (Thermal.decodeRule a)
              (@List.toFinset.{0} Thermal.Lattice
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                l)))
          fun
            (a_1 :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport (Thermal.decodeRule a)
                    (@List.toFinset.{0} Thermal.Lattice
                      (fun (a b : Thermal.Lattice) =>
                        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                      l))
                  x) =>
          Fin.fintype (Thermal.CA.q (Thermal.decodeRule a))))
      fun
        (x :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport (Thermal.decodeRule a)
                  (@List.toFinset.{0} Thermal.Lattice
                    (fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    l))
                x) →
            Fin (Thermal.CA.q (Thermal.decodeRule a))) =>
      f x) := @_root_.Thermal.sum_inputAssignment

theorem ComparatorCore.check_Thermal_finiteNumerator_correct :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l),
  @Eq.{1} Int
    (Thermal.Algorithm.finiteNumerator (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l))
    (Thermal.collisionNumerator (Thermal.decodeRule a)
      (@List.toFinset.{0} Thermal.Lattice
        (fun (a b : Thermal.Lattice) => @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        l)) := @_root_.Thermal.finiteNumerator_correct

theorem ComparatorCore.check_Thermal_finiteNumerator_pos_iff :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l),
  Iff
    (@LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (Thermal.Algorithm.finiteNumerator
        (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l)))
    (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (Thermal.c (Thermal.decodeRule a)
        (@List.toFinset.{0} Thermal.Lattice
          (fun (a b : Thermal.Lattice) =>
            @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
          l))) := @_root_.Thermal.finiteNumerator_pos_iff

theorem ComparatorCore.check_Thermal_Algorithm_prim_shiftList :
    @Primrec.{0, 0} (Prod.{0, 0} Nat (List.{0} Nat)) (List.{0} Nat)
  (@Primcodable.prod.{0, 0} Nat (List.{0} Nat) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
    (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)) Thermal.Algorithm.shiftList := @_root_.Thermal.Algorithm.prim_shiftList

theorem ComparatorCore.check_Thermal_Algorithm_prim_raiseBase :
    @Primrec.{0, 0} (List.{0} Nat) (List.{0} Nat)
  (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)) Thermal.Algorithm.raiseBase := @_root_.Thermal.Algorithm.prim_raiseBase

theorem ComparatorCore.check_Thermal_Algorithm_prim_candidateList :
    @Primrec.{0, 0} Nat (List.{0} Thermal.Algorithm.Point) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  (@Primcodable.list.{0} Thermal.Algorithm.Point
    (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
      (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
  Thermal.Algorithm.candidateList := @_root_.Thermal.Algorithm.prim_candidateList

theorem ComparatorCore.check_Thermal_Algorithm_prim_maskSubset :
    @Primrec.{0, 0} (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) Nat) (List.{0} Thermal.Algorithm.Point)
  (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) Nat
    (@Primcodable.list.{0} Thermal.Algorithm.Point
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  (@Primcodable.list.{0} Thermal.Algorithm.Point
    (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
      (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
  Thermal.Algorithm.maskSubset := @_root_.Thermal.Algorithm.prim_maskSubset

theorem ComparatorCore.check_Thermal_Algorithm_prim_smallerPositive :
    @PrimrecRel.{0, 0} Nat Thermal.Algorithm.FiniteInput (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.list.{0} Thermal.Algorithm.Point
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  Thermal.Algorithm.smallerPositive := @_root_.Thermal.Algorithm.prim_smallerPositive

theorem ComparatorCore.check_Thermal_Algorithm_prim_minimalPositive :
    @PrimrecPred.{0} Thermal.Algorithm.FiniteInput
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.list.{0} Thermal.Algorithm.Point
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  Thermal.Algorithm.MinimalPositive := @_root_.Thermal.Algorithm.prim_minimalPositive

theorem ComparatorCore.check_Thermal_Algorithm_prim_searchProgram :
    @Primrec.{0, 0} (Prod.{0, 0} Thermal.Algorithm.Code Nat) (Option.{0} (Finset.{0} Thermal.Algorithm.Point))
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code Nat
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  (@Primcodable.option.{0} (Finset.{0} Thermal.Algorithm.Point)
    (@Primcodable.ofDenumerable.{0} (Finset.{0} Thermal.Algorithm.Point)
      (@Denumerable.finset.{0} Thermal.Algorithm.Point
        (@Denumerable.prod.{0, 0} Int Int Denumerable.int Denumerable.int))))
  Thermal.Algorithm.searchProgram := @_root_.Thermal.Algorithm.prim_searchProgram

theorem ComparatorCore.check_Thermal_global_extend_block :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (x :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (Thermal.inputSupport F T) x) →
      Fin (Thermal.CA.q F))
  (i :
    @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
          (@Finset.instSetLike.{0} Thermal.Lattice))
        T x),
  @Eq.{1} (Fin (Thermal.CA.q F))
    (Thermal.CA.global F (Thermal.extendPattern F (Thermal.inputSupport F T) x)
      (@Subtype.val.{1} Thermal.Lattice
        (fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x)
        i))
    (Thermal.blockMap F T x i) := @_root_.Thermal.global_extend_block

theorem ComparatorCore.check_Thermal_positive_output_has_preimage :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (a :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          T x) →
      Fin (Thermal.CA.q F))
  (hp :
    @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (Thermal.outputLaw F T a)),
  @Exists.{1}
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (Thermal.inputSupport F T) x) →
      Fin (Thermal.CA.q F))
    fun
      (x :
        (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x) →
          Fin (Thermal.CA.q F)) =>
    @Eq.{1}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F))
      (Thermal.blockMap F T x) a := @_root_.Thermal.positive_output_has_preimage

theorem ComparatorCore.check_Thermal_finite_block_surjective_onto :
    ∀ (F : Thermal.CA)
  (hf :
    ∀ (T : Finset.{0} Thermal.Lattice)
      (a :
        (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F)),
      @Exists.{1}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (Thermal.inputSupport F T) x) →
          Fin (Thermal.CA.q F))
        fun
          (x :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.inputSupport F T) x) →
              Fin (Thermal.CA.q F)) =>
        @Eq.{1}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (Thermal.blockMap F T x) a),
  Thermal.CA.Onto F := @_root_.Thermal.finite_block_surjective_onto

theorem ComparatorCore.check_Thermal_balanced_onto :
    ∀ (F : Thermal.CA) (hb : Thermal.Balanced F), Thermal.CA.Onto F := @_root_.Thermal.balanced_onto

theorem ComparatorCore.check_Thermal_nononto_positive_coefficient :
    ∀ (F : Thermal.CA) (hn : Not (Thermal.CA.Onto F)),
  @Exists.{1} (Finset.{0} Thermal.Lattice) fun (T : Finset.{0} Thermal.Lattice) =>
    And (@Finset.Nonempty.{0} Thermal.Lattice T)
      (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.c F T)) := @_root_.Thermal.nononto_positive_coefficient

theorem ComparatorCore.check_Thermal_average_cover_mul :
    ∀ {α : Type} [inst : DecidableEq.{1} α] (q : Nat)
  (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) (S T U : Finset.{0} α)
  (hs :
    @LE.le.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α) (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
      S U)
  (ht :
    @LE.le.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α) (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
      T U)
  (hd : @Disjoint.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α) (@Finset.instOrderBot.{0} α) S T)
  (hu : @Eq.{1} (Finset.{0} α) U (@Union.union.{0} (Finset.{0} α) (@Finset.instUnion.{0} α inst) S T))
  (f :
    ((@Subtype.{1} α fun (x : α) =>
          @Membership.mem.{0, 0} α (Finset.{0} α)
            (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
        Fin q) →
      Rat)
  (g :
    ((@Subtype.{1} α fun (x : α) =>
          @Membership.mem.{0, 0} α (Finset.{0} α)
            (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
        Fin q) →
      Rat),
  @Eq.{1} Rat
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} α fun (x : α) =>
            @Membership.mem.{0, 0} α (Finset.{0} α)
              (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x) →
          Fin q)
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x) →
            Fin q)
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x)
            (fun
                (a :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x) =>
              Fin q)
            (fun
                (a b :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x) =>
              @Subtype.instDecidableEq.{1} α
                (@Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U)
                inst a b)
            (@Finset.Subtype.fintype.{0} α U)
            fun
              (a :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x) =>
            Fin.fintype q))
        fun
          (x :
            (@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x) →
              Fin q) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (f
            fun
              (i :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
            x
              (@Subtype.mk.{1} α
                (fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x)
                (@Subtype.val.{1} α
                  (fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                  i)
                (@hs
                  (@Subtype.val.{1} α
                    (fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                    i)
                  (@Subtype.property.{1} α
                    (fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
                    i))))
          (g
            fun
              (i :
                @Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
            x
              (@Subtype.mk.{1} α
                (fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) U x)
                (@Subtype.val.{1} α
                  (fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
                  i)
                (@ht
                  (@Subtype.val.{1} α
                    (fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
                    i)
                  (@Subtype.property.{1} α
                    (fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
                    i)))))
      (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat) (@Nat.cast.{0} Rat Rat.instNatCast q)
        (@Finset.card.{0} α U)))
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@Finset.sum.{0, 0}
          ((@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
            Fin q)
          Rat Rat.addCommMonoid
          (@Finset.univ.{0}
            ((@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
              Fin q)
            (@Pi.instFintype.{0, 0}
              (@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x)
              (fun
                  (a :
                    @Subtype.{1} α fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
                Fin q)
              (fun
                  (a b :
                    @Subtype.{1} α fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
                @Subtype.instDecidableEq.{1} α
                  (@Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S)
                  inst a b)
              (@Finset.Subtype.fintype.{0} α S)
              fun
                (a :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) =>
              Fin.fintype q))
          fun
            (x :
              (@Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) S x) →
                Fin q) =>
          f x)
        (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
          (@Nat.cast.{0} Rat Rat.instNatCast q) (@Finset.card.{0} α S)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@Finset.sum.{0, 0}
          ((@Subtype.{1} α fun (x : α) =>
              @Membership.mem.{0, 0} α (Finset.{0} α)
                (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
            Fin q)
          Rat Rat.addCommMonoid
          (@Finset.univ.{0}
            ((@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
              Fin q)
            (@Pi.instFintype.{0, 0}
              (@Subtype.{1} α fun (x : α) =>
                @Membership.mem.{0, 0} α (Finset.{0} α)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x)
              (fun
                  (a :
                    @Subtype.{1} α fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
                Fin q)
              (fun
                  (a b :
                    @Subtype.{1} α fun (x : α) =>
                      @Membership.mem.{0, 0} α (Finset.{0} α)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
                @Subtype.instDecidableEq.{1} α
                  (@Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T)
                  inst a b)
              (@Finset.Subtype.fintype.{0} α T)
              fun
                (a :
                  @Subtype.{1} α fun (x : α) =>
                    @Membership.mem.{0, 0} α (Finset.{0} α)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) =>
              Fin.fintype q))
          fun
            (y :
              (@Subtype.{1} α fun (x : α) =>
                  @Membership.mem.{0, 0} α (Finset.{0} α)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} α) α (@Finset.instSetLike.{0} α)) T x) →
                Fin q) =>
          g y)
        (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
          (@Nat.cast.{0} Rat Rat.instNatCast q) (@Finset.card.{0} α T)))) := @_root_.Thermal.average_cover_mul

theorem ComparatorCore.check_Thermal_inputSupport_union :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice),
  @Eq.{1} (Finset.{0} Thermal.Lattice)
    (Thermal.inputSupport F
      (@Union.union.{0} (Finset.{0} Thermal.Lattice)
        (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
          @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        S T))
    (@Union.union.{0} (Finset.{0} Thermal.Lattice)
      (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
      (Thermal.inputSupport F S) (Thermal.inputSupport F T)) := @_root_.Thermal.inputSupport_union

theorem ComparatorCore.check_Thermal_disjoint_outputs_of_inputs :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hd :
    @Disjoint.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)
      (@Finset.instOrderBot.{0} Thermal.Lattice) (Thermal.inputSupport F S) (Thermal.inputSupport F T)),
  @Disjoint.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)
    (@Finset.instOrderBot.{0} Thermal.Lattice) S T := @_root_.Thermal.disjoint_outputs_of_inputs

theorem ComparatorCore.check_Thermal_outputLaw_independent :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hd :
    @Disjoint.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)
      (@Finset.instOrderBot.{0} Thermal.Lattice) (Thermal.inputSupport F S) (Thermal.inputSupport F T))
  (f :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            S x) →
        Fin (Thermal.CA.q F)) →
      Rat)
  (g :
    ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            T x) →
        Fin (Thermal.CA.q F)) →
      Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            (@Union.union.{0} (Finset.{0} Thermal.Lattice)
              (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              S T)
            x) →
        Fin (Thermal.CA.q F))
      Rat Rat.addCommMonoid
      (@Finset.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                S T)
              x) →
          Fin (Thermal.CA.q F))
        (@Pi.instFintype.{0, 0}
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                S T)
              x)
          (fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                      (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                      S T)
                    x) =>
            Fin (Thermal.CA.q F))
          (fun
              (a b :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                      (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                      S T)
                    x) =>
            @Subtype.instDecidableEq.{1} Thermal.Lattice
              (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                  (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  S T))
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              a b)
          (@Finset.Subtype.fintype.{0} Thermal.Lattice
            (@Union.union.{0} (Finset.{0} Thermal.Lattice)
              (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              S T))
          fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                    (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                      @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                    S T)
                  x) =>
          Fin.fintype (Thermal.CA.q F)))
      fun
        (b :
          (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                  (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  S T)
                x) →
            Fin (Thermal.CA.q F)) =>
      @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (Thermal.outputLaw F
          (@Union.union.{0} (Finset.{0} Thermal.Lattice)
            (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
              @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
            S T)
          b)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (f
            fun
              (i :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            b
              (@Subtype.mk.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                      (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                      S T)
                    x)
                (@Subtype.val.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x)
                  i)
                (@Finset.mem_union_left.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  S
                  (@Subtype.val.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i)
                  T
                  (@Subtype.property.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        S x)
                    i))))
          (g
            fun
              (i :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            b
              (@Subtype.mk.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                      (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                      S T)
                    x)
                (@Subtype.val.{1} Thermal.Lattice
                  (fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x)
                  i)
                (@Finset.mem_union_right.{0} Thermal.Lattice
                  (fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  T
                  (@Subtype.val.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        T x)
                    i)
                  S
                  (@Subtype.property.{1} Thermal.Lattice
                    (fun (x : Thermal.Lattice) =>
                      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                          (@Finset.instSetLike.{0} Thermal.Lattice))
                        T x)
                    i))))))
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              S x) →
          Fin (Thermal.CA.q F))
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      S x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S)
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice S)
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (a :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x) →
              Fin (Thermal.CA.q F)) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F S a) (f a))
      (@Finset.sum.{0, 0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              T x) →
          Fin (Thermal.CA.q F))
        Rat Rat.addCommMonoid
        (@Finset.univ.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (@Pi.instFintype.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              Fin (Thermal.CA.q F))
            (fun
                (a b :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              @Subtype.instDecidableEq.{1} Thermal.Lattice
                (@Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T)
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                a b)
            (@Finset.Subtype.fintype.{0} Thermal.Lattice T)
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Fin.fintype (Thermal.CA.q F)))
        fun
          (b :
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) →
              Fin (Thermal.CA.q F)) =>
        @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.outputLaw F T b) (g b))) := @_root_.Thermal.outputLaw_independent

theorem ComparatorCore.check_Thermal_outputLaw_factorization :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hd :
    @Disjoint.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)
      (@Finset.instOrderBot.{0} Thermal.Lattice) (Thermal.inputSupport F S) (Thermal.inputSupport F T))
  (a :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (@Union.union.{0} (Finset.{0} Thermal.Lattice)
            (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
              @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
            S T)
          x) →
      Fin (Thermal.CA.q F)),
  @Eq.{1} Rat
    (Thermal.outputLaw F
      (@Union.union.{0} (Finset.{0} Thermal.Lattice)
        (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
          @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        S T)
      a)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (Thermal.outputLaw F S
        fun
          (i :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                S x) =>
        a
          (@Subtype.mk.{1} Thermal.Lattice
            (fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                  (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  S T)
                x)
            (@Subtype.val.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  S x)
              i)
            (@Finset.mem_union_left.{0} Thermal.Lattice
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              S
              (@Subtype.val.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x)
                i)
              T
              (@Subtype.property.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    S x)
                i))))
      (Thermal.outputLaw F T
        fun
          (i :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) =>
        a
          (@Subtype.mk.{1} Thermal.Lattice
            (fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (@Union.union.{0} (Finset.{0} Thermal.Lattice)
                  (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
                    @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                  S T)
                x)
            (@Subtype.val.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x)
              i)
            (@Finset.mem_union_right.{0} Thermal.Lattice
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              T
              (@Subtype.val.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x)
                i)
              S
              (@Subtype.property.{1} Thermal.Lattice
                (fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x)
                i))))) := @_root_.Thermal.outputLaw_factorization

theorem ComparatorCore.check_Thermal_sum_two_equiv :
    ∀ {A B : Type} [inst : Fintype.{0} A] [inst_1 : Fintype.{0} B] (e : Equiv.{1, 1} A B) (f : B → B → Rat),
  @Eq.{1} Rat
    (@Finset.sum.{0, 0} A Rat Rat.addCommMonoid (@Finset.univ.{0} A inst) fun (x : A) =>
      @Finset.sum.{0, 0} A Rat Rat.addCommMonoid (@Finset.univ.{0} A inst) fun (y : A) =>
        f
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} A B) A (fun (x : A) => B)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} A B) A B (@Equiv.instEquivLike.{1, 1} A B)) e x)
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} A B) A (fun (x : A) => B)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} A B) A B (@Equiv.instEquivLike.{1, 1} A B)) e y))
    (@Finset.sum.{0, 0} B Rat Rat.addCommMonoid (@Finset.univ.{0} B inst_1) fun (x : B) =>
      @Finset.sum.{0, 0} B Rat Rat.addCommMonoid (@Finset.univ.{0} B inst_1) fun (y : B) => f x y) := @_root_.Thermal.sum_two_equiv

theorem ComparatorCore.check_Thermal_coefficient_factorization :
    ∀ (F : Thermal.CA) (S T : Finset.{0} Thermal.Lattice)
  (hd :
    @Disjoint.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)
      (@Finset.instOrderBot.{0} Thermal.Lattice) (Thermal.inputSupport F S) (Thermal.inputSupport F T)),
  @Eq.{1} Rat
    (Thermal.c F
      (@Union.union.{0} (Finset.{0} Thermal.Lattice)
        (@Finset.instUnion.{0} Thermal.Lattice fun (a b : Thermal.Lattice) =>
          @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        S T))
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (Thermal.c F S) (Thermal.c F T)) := @_root_.Thermal.coefficient_factorization

theorem ComparatorCore.check_Thermal_connected_witness :
    ∀ (F : Thermal.CA) (hn : Not (Thermal.CA.Onto F)),
  @Exists.{1} (Finset.{0} Thermal.Lattice) fun (P : Finset.{0} Thermal.Lattice) => Thermal.ConnectedWitness F P := @_root_.Thermal.connected_witness

theorem ComparatorCore.check_Thermal_uniform_finite :
    ∀ (q : Nat) (K : Finset.{0} Thermal.Lattice),
  @Eq.{1}
    (@MeasureTheory.Measure.{0}
      ((i :
          @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              K x) →
        Fin q)
      (@MeasurableSpace.pi.{0, 0}
        (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            K x)
        (fun
            (x :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  K x) =>
          Fin q)
        fun
          (i :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                K x) =>
        Thermal.symbolMeasurable q))
    (@MeasureTheory.Measure.pi.{0, 0}
      (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          K x)
      (fun
          (x :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                K x) =>
        Fin q)
      (@Finset.Subtype.fintype.{0} Thermal.Lattice K)
      (fun
          (i :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                K x) =>
        Thermal.symbolMeasurable q)
      fun
        (x :
          @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              K x) =>
      @ProbabilityTheory.uniformOn.{0} (Fin q) (Thermal.symbolMeasurable q) (@Set.univ.{0} (Fin q)))
    (@ProbabilityTheory.uniformOn.{0}
      ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            K x) →
        Fin q)
      (@MeasurableSpace.pi.{0, 0}
        (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
          @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
              (@Finset.instSetLike.{0} Thermal.Lattice))
            K x)
        (fun
            (a :
              @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  K x) =>
          Fin q)
        fun
          (a :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                K x) =>
        Thermal.symbolMeasurable q)
      (@Set.univ.{0}
        ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
            @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                (@Finset.instSetLike.{0} Thermal.Lattice))
              K x) →
          Fin q))) := @_root_.Thermal.uniform_finite

theorem ComparatorCore.check_Thermal_uniform_map_block_mass :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (a :
    (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
        @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          T x) →
      Fin (Thermal.CA.q F)),
  @Eq.{1} Real
    (ENNReal.toReal
      (@DFunLike.coe.{1, 1, 1}
        (@MeasureTheory.Measure.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (@MeasurableSpace.pi.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              Fin (Thermal.CA.q F))
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Thermal.symbolMeasurable (Thermal.CA.q F)))
        (Set.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F)))
        (fun
            (x :
              Set.{0}
                ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) →
                  Fin (Thermal.CA.q F))) =>
          ENNReal)
        (@MeasureTheory.Measure.instFunLike.{0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (@MeasurableSpace.pi.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              Fin (Thermal.CA.q F))
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Thermal.symbolMeasurable (Thermal.CA.q F)))
        (@MeasureTheory.Measure.map.{0, 0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x) →
            Fin (Thermal.CA.q F))
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (@MeasurableSpace.pi.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              Fin (Thermal.CA.q F))
            fun
              (i :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            Thermal.symbolMeasurable (Thermal.CA.q F))
          (@MeasurableSpace.pi.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      T x) =>
              Fin (Thermal.CA.q F))
            fun
              (a :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    T x) =>
            Thermal.symbolMeasurable (Thermal.CA.q F))
          (Thermal.blockMap F T)
          (@MeasureTheory.Measure.pi.{0, 0}
            (@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.inputSupport F T) x)
            (fun
                (a :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              Fin (Thermal.CA.q F))
            (@Finset.Subtype.fintype.{0} Thermal.Lattice (Thermal.inputSupport F T))
            (fun
                (i :
                  @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                    @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                        (@Finset.instSetLike.{0} Thermal.Lattice))
                      (Thermal.inputSupport F T) x) =>
              Thermal.symbolMeasurable (Thermal.CA.q F))
            fun
              (x :
                @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                  @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                      (@Finset.instSetLike.{0} Thermal.Lattice))
                    (Thermal.inputSupport F T) x) =>
            @ProbabilityTheory.uniformOn.{0} (Fin (Thermal.CA.q F)) (Thermal.symbolMeasurable (Thermal.CA.q F))
              (@Set.univ.{0} (Fin (Thermal.CA.q F)))))
        (@Singleton.singleton.{0, 0}
          ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                T x) →
            Fin (Thermal.CA.q F))
          (Set.{0}
            ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) →
              Fin (Thermal.CA.q F)))
          (@Set.instSingletonSet.{0}
            ((@Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  T x) →
              Fin (Thermal.CA.q F)))
          a)))
    (@Rat.cast.{0} Real Real.instRatCast (Thermal.outputLaw F T a)) := @_root_.Thermal.uniform_map_block_mass

theorem ComparatorCore.check_Thermal_balance :
    ∀ (H : PublishedCA.KariTaati_Corollary21) (F : Thermal.CA), Iff (Thermal.CA.Onto F) (Thermal.Balanced F) := @_root_.Thermal.balance

theorem ComparatorCore.check_Thermal_coefficient_detection :
    ∀ (H : PublishedCA.KariTaati_Corollary21) (F : Thermal.CA),
  Iff
    (∀ (T : Finset.{0} Thermal.Lattice),
      @Finset.Nonempty.{0} Thermal.Lattice T →
        @Eq.{1} Rat (Thermal.c F T) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
    (Thermal.CA.Onto F) := @_root_.Thermal.coefficient_detection

theorem ComparatorCore.check_Thermal_positive_coefficient_nononto :
    ∀ (H : PublishedCA.KariTaati_Corollary21) (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice)
  (ht : @Finset.Nonempty.{0} Thermal.Lattice T)
  (hp : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.c F T)),
  Not (Thermal.CA.Onto F) := @_root_.Thermal.positive_coefficient_nononto

theorem ComparatorCore.check_Thermal_onto_collision_core_published :
    ∀ (H : PublishedCA.KariTaati_Corollary21) (F : Thermal.CA) (ho : Thermal.CA.Onto F),
  And
    (∀ (T : Finset.{0} Thermal.Lattice),
      @Finset.Nonempty.{0} Thermal.Lattice T →
        @Eq.{1} Rat (Thermal.c F T) (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
    (∀ (ε : Rat) (C : Finset.{0} Thermal.Lattice),
      @Eq.{1} Rat (Thermal.W F ε C) (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) := @_root_.Thermal.onto_collision_core_published

theorem ComparatorCore.check_Thermal_list_map_identity_nat :
    ∀ (l : List.{0} Nat), @Eq.{1} (List.{0} Nat) (@List.map.{0, 0} Nat Nat (fun (m : Nat) => m) l) l := @_root_.Thermal.list_map_identity_nat

theorem ComparatorCore.check_Thermal_raiseBase_spec :
    ∀ (l : List.{0} Nat) (n : Nat),
  @Eq.{1} (List.{0} Nat) (Denumerable.raise' l n)
    (@List.map.{0, 0} Nat Nat (fun (m : Nat) => @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n)
      (Thermal.Algorithm.raiseBase l)) := @_root_.Thermal.raiseBase_spec

theorem ComparatorCore.check_Thermal_candidateList_set :
    ∀ (n : Nat),
  @Eq.{1} (Finset.{0} Thermal.Algorithm.Point)
    (@List.toFinset.{0} Thermal.Algorithm.Point
      (fun (a b : Thermal.Algorithm.Point) =>
        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
      (Thermal.Algorithm.candidateList n))
    (@Denumerable.ofNat.{0} (Finset.{0} Thermal.Lattice)
      (@Denumerable.finset.{0} Thermal.Lattice (@Denumerable.prod.{0, 0} Int Int Denumerable.int Denumerable.int)) n) := @_root_.Thermal.candidateList_set

theorem ComparatorCore.check_Thermal_candidateList_nodup :
    ∀ (n : Nat), @List.Nodup.{0} Thermal.Algorithm.Point (Thermal.Algorithm.candidateList n) := @_root_.Thermal.candidateList_nodup

theorem ComparatorCore.check_Thermal_candidateList_complete :
    ∀ (P : Finset.{0} Thermal.Lattice),
  @Exists.{1} Nat fun (n : Nat) =>
    @Eq.{1} (Finset.{0} Thermal.Algorithm.Point)
      (@List.toFinset.{0} Thermal.Algorithm.Point
        (fun (a b : Thermal.Algorithm.Point) =>
          @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        (Thermal.Algorithm.candidateList n))
      P := @_root_.Thermal.candidateList_complete

theorem ComparatorCore.check_Thermal_maskSubset_subset :
    ∀ (l : List.{0} Thermal.Lattice) (m : Nat),
  @LE.le.{0} (Finset.{0} Thermal.Algorithm.Point)
    (@Preorder.toLE.{0} (Finset.{0} Thermal.Algorithm.Point)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Algorithm.Point)
        (@Finset.instPartialOrder.{0} Thermal.Algorithm.Point)))
    (@List.toFinset.{0} Thermal.Algorithm.Point
      (fun (a b : Thermal.Algorithm.Point) =>
        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
      (Thermal.Algorithm.maskSubset (@Prod.mk.{0, 0} (List.{0} Thermal.Algorithm.Point) Nat l m)))
    (@List.toFinset.{0} Thermal.Lattice
      (fun (a b : Thermal.Lattice) => @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
      l) := @_root_.Thermal.maskSubset_subset

theorem ComparatorCore.check_Thermal_maskSubset_complete :
    ∀ (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l) (S : Finset.{0} Thermal.Lattice)
  (hS :
    @LE.le.{0} (Finset.{0} Thermal.Lattice)
      (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
      S
      (@List.toFinset.{0} Thermal.Lattice
        (fun (a b : Thermal.Lattice) => @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        l)),
  @Exists.{1} Nat fun (m : Nat) =>
    And
      (@LT.lt.{0} Nat instLTNat m
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Thermal.Lattice l)))
      (@Eq.{1} (Finset.{0} Thermal.Algorithm.Point)
        (@List.toFinset.{0} Thermal.Algorithm.Point
          (fun (a b : Thermal.Algorithm.Point) =>
            @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
          (Thermal.Algorithm.maskSubset (@Prod.mk.{0, 0} (List.{0} Thermal.Algorithm.Point) Nat l m)))
        S) := @_root_.Thermal.maskSubset_complete

theorem ComparatorCore.check_Thermal_maskSubset_nodup :
    ∀ (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l) (m : Nat),
  @List.Nodup.{0} Thermal.Algorithm.Point
    (Thermal.Algorithm.maskSubset (@Prod.mk.{0, 0} (List.{0} Thermal.Algorithm.Point) Nat l m)) := @_root_.Thermal.maskSubset_nodup

theorem ComparatorCore.check_Thermal_minimalPositive_iff :
    ∀ (a : Thermal.RuleCode) (l : List.{0} Thermal.Lattice) (hl : @List.Nodup.{0} Thermal.Lattice l),
  Iff
    (Thermal.Algorithm.MinimalPositive (@Prod.mk.{0, 0} Thermal.Algorithm.Code (List.{0} Thermal.Algorithm.Point) a l))
    (And
      (@Finset.Nonempty.{0} Thermal.Lattice
        (@List.toFinset.{0} Thermal.Lattice
          (fun (a b : Thermal.Lattice) =>
            @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
          l))
      (And
        (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (Thermal.c (Thermal.decodeRule a)
            (@List.toFinset.{0} Thermal.Lattice
              (fun (a b : Thermal.Lattice) =>
                @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
              l)))
        (∀ (S : Finset.{0} Thermal.Lattice),
          @LE.le.{0} (Finset.{0} Thermal.Lattice)
              (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
                (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice)
                  (@Finset.instPartialOrder.{0} Thermal.Lattice)))
              S
              (@List.toFinset.{0} Thermal.Lattice
                (fun (a b : Thermal.Lattice) =>
                  @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                l) →
            @Finset.Nonempty.{0} Thermal.Lattice S →
              @LT.lt.{0} Nat instLTNat (@Finset.card.{0} Thermal.Lattice S)
                  (@Finset.card.{0} Thermal.Lattice
                    (@List.toFinset.{0} Thermal.Lattice
                      (fun (a b : Thermal.Lattice) =>
                        @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
                      l)) →
                Not
                  (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                    (Thermal.c (Thermal.decodeRule a) S))))) := @_root_.Thermal.minimalPositive_iff

theorem ComparatorCore.check_Thermal_minimal_positive_connected :
    ∀ (F : Thermal.CA) (P : Finset.{0} Thermal.Lattice) (hne : @Finset.Nonempty.{0} Thermal.Lattice P)
  (hpos : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.c F P))
  (hmin :
    ∀ (S : Finset.{0} Thermal.Lattice),
      @LE.le.{0} (Finset.{0} Thermal.Lattice)
          (@Preorder.toLE.{0} (Finset.{0} Thermal.Lattice)
            (@PartialOrder.toPreorder.{0} (Finset.{0} Thermal.Lattice) (@Finset.instPartialOrder.{0} Thermal.Lattice)))
          S P →
        @Finset.Nonempty.{0} Thermal.Lattice S →
          @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.c F S) →
            @LE.le.{0} Nat instLENat (@Finset.card.{0} Thermal.Lattice P) (@Finset.card.{0} Thermal.Lattice S)),
  @SimpleGraph.Connected.{0}
    (@Set.Elem.{0} Thermal.Lattice
      (@SetLike.coe.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice (@Finset.instSetLike.{0} Thermal.Lattice) P))
    (@SimpleGraph.induce.{0} Thermal.Lattice
      (@SetLike.coe.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice (@Finset.instSetLike.{0} Thermal.Lattice) P)
      (Thermal.overlapGraph F)) := @_root_.Thermal.minimal_positive_connected

theorem ComparatorCore.check_Thermal_searchProgram_connected :
    ∀ (a : Thermal.RuleCode) (n : Nat) (P : Finset.{0} Thermal.Lattice)
  (h :
    @Eq.{1} (Option.{0} (Finset.{0} Thermal.Algorithm.Point))
      (Thermal.Algorithm.searchProgram (@Prod.mk.{0, 0} Thermal.Algorithm.Code Nat a n))
      (@Option.some.{0} (Finset.{0} Thermal.Lattice) P)),
  Thermal.ConnectedWitness (Thermal.decodeRule a) P := @_root_.Thermal.searchProgram_connected

theorem ComparatorCore.check_Thermal_searchProgram_complete :
    ∀ (a : Thermal.RuleCode) (hn : Not (Thermal.CA.Onto (Thermal.decodeRule a))),
  @Exists.{1} Nat fun (n : Nat) =>
    @Exists.{1} (Finset.{0} Thermal.Algorithm.Point) fun (P : Finset.{0} Thermal.Algorithm.Point) =>
      @Eq.{1} (Option.{0} (Finset.{0} Thermal.Algorithm.Point))
        (Thermal.Algorithm.searchProgram (@Prod.mk.{0, 0} Thermal.Algorithm.Code Nat a n))
        (@Option.some.{0} (Finset.{0} Thermal.Algorithm.Point) P) := @_root_.Thermal.searchProgram_complete

theorem ComparatorCore.check_Thermal_witness_search :
    @Exists.{1} (Prod.{0, 0} Thermal.RuleCode Nat → Option.{0} (Finset.{0} Thermal.Lattice))
  fun (search : Prod.{0, 0} Thermal.RuleCode Nat → Option.{0} (Finset.{0} Thermal.Lattice)) =>
  And
    (@Computable.{0, 0} (Prod.{0, 0} Thermal.RuleCode Nat) (Option.{0} (Finset.{0} Thermal.Lattice))
      (@Primcodable.prod.{0, 0} Thermal.RuleCode Nat
        (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat))
          (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
          (@Primcodable.prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat)
            (@Primcodable.list.{0} Thermal.Lattice
              (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
                (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
            (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
      (@Primcodable.option.{0} (Finset.{0} Thermal.Lattice)
        (@Primcodable.ofDenumerable.{0} (Finset.{0} Thermal.Lattice)
          (@Denumerable.finset.{0} Thermal.Lattice (@Denumerable.prod.{0, 0} Int Int Denumerable.int Denumerable.int))))
      search)
    (And
      (∀ (code : Thermal.RuleCode) (n : Nat) (P : Finset.{0} Thermal.Lattice),
        @Eq.{1} (Option.{0} (Finset.{0} Thermal.Lattice)) (search (@Prod.mk.{0, 0} Thermal.RuleCode Nat code n))
            (@Option.some.{0} (Finset.{0} Thermal.Lattice) P) →
          And (@Finset.Nonempty.{0} Thermal.Lattice P)
            (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (Thermal.c (Thermal.decodeRule code) P)))
      (∀ (code : Thermal.RuleCode),
        Not (Thermal.CA.Onto (Thermal.decodeRule code)) →
          @Exists.{1} Nat fun (n : Nat) =>
            @Exists.{1} (Finset.{0} Thermal.Lattice) fun (P : Finset.{0} Thermal.Lattice) =>
              @Eq.{1} (Option.{0} (Finset.{0} Thermal.Lattice)) (search (@Prod.mk.{0, 0} Thermal.RuleCode Nat code n))
                (@Option.some.{0} (Finset.{0} Thermal.Lattice) P))) := @_root_.Thermal.witness_search

theorem ComparatorCore.check_Thermal_searchProgram_exact :
    ∀ (H : PublishedCA.KariTaati_Corollary21) (a : Thermal.RuleCode),
  Iff
    (@Exists.{1} Nat fun (n : Nat) =>
      @Exists.{1} (Finset.{0} Thermal.Algorithm.Point) fun (P : Finset.{0} Thermal.Algorithm.Point) =>
        @Eq.{1} (Option.{0} (Finset.{0} Thermal.Algorithm.Point))
          (Thermal.Algorithm.searchProgram (@Prod.mk.{0, 0} Thermal.Algorithm.Code Nat a n))
          (@Option.some.{0} (Finset.{0} Thermal.Algorithm.Point) P))
    (Not (Thermal.CA.Onto (Thermal.decodeRule a))) := @_root_.Thermal.searchProgram_exact

theorem ComparatorCore.check_Thermal_Algorithm_prim_visibleDigit :
    @Primrec.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Thermal.Algorithm.Point)) Nat
  (@Primcodable.prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
    (@Primcodable.prod.{0, 0} Nat Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
    (@Primcodable.prod.{0, 0} Nat Thermal.Algorithm.Point (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Int Denumerable.int))))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.visibleDigit := @_root_.Thermal.Algorithm.prim_visibleDigit

theorem ComparatorCore.check_Thermal_Algorithm_prim_phase :
    @Primrec.{0, 0} Thermal.Algorithm.TableInput Bool
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code
    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
      (@Primcodable.fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  Primcodable.bool Thermal.Algorithm.phase := @_root_.Thermal.Algorithm.prim_phase

theorem ComparatorCore.check_Thermal_Algorithm_prim_tableDenom :
    @Primrec.{0, 0} Thermal.Algorithm.TableInput Nat
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code
    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
      (@Primcodable.fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Thermal.Algorithm.tableDenom := @_root_.Thermal.Algorithm.prim_tableDenom

theorem ComparatorCore.check_Thermal_Algorithm_prim_tableSame :
    @Primrec.{0, 0} Thermal.Algorithm.TableInput Bool
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code
    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
      (@Primcodable.fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  Primcodable.bool Thermal.Algorithm.tableSame := @_root_.Thermal.Algorithm.prim_tableSame

theorem ComparatorCore.check_Thermal_Algorithm_prim_tableRuleSame :
    @Primrec.{0, 0} Thermal.Algorithm.TableInput Bool
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code
    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
      (@Primcodable.fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  Primcodable.bool Thermal.Algorithm.tableRuleSame := @_root_.Thermal.Algorithm.prim_tableRuleSame

theorem ComparatorCore.check_Thermal_Algorithm_prim_tableProgram :
    @Primrec.{0, 0} Thermal.Algorithm.TableInput (Prod.{0, 0} Int Nat)
  (@Primcodable.prod.{0, 0} Thermal.Algorithm.Code
    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat)
    (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.prod.{0, 0} (List.{0} Thermal.Algorithm.Point) (List.{0} Nat)
        (@Primcodable.list.{0} Thermal.Algorithm.Point
          (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
            (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
    (@Primcodable.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
      (@Primcodable.fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
  (@Primcodable.prod.{0, 0} Int Nat (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
  Thermal.Algorithm.tableProgram := @_root_.Thermal.Algorithm.prim_tableProgram

theorem ComparatorCore.check_Thermal_algorithm_ncard :
    ∀ (a : Thermal.RuleCode),
  @Eq.{1} Nat (Thermal.Algorithm.ncard a) (@Finset.card.{0} Thermal.Lattice (Thermal.CA.N (Thermal.decodeRule a))) := @_root_.Thermal.algorithm_ncard

theorem ComparatorCore.check_Thermal_maximum_map_eq_sup :
    ∀ {α : Type} [inst : DecidableEq.{1} α] (l : List.{0} α) (f : α → Nat),
  @Eq.{1} Nat (Thermal.Algorithm.maximum (@List.map.{0, 0} α Nat f l))
    (@Finset.sup.{0, 0} Nat α (@Lattice.toSemilatticeSup.{0} Nat Nat.instLattice) Nat.instOrderBot
      (@List.toFinset.{0} α inst l) f) := @_root_.Thermal.maximum_map_eq_sup

theorem ComparatorCore.check_Thermal_algorithm_diameter :
    ∀ (l : List.{0} Thermal.Lattice),
  @Eq.{1} Nat (Thermal.Algorithm.diameter l)
    (Thermal.supportDiameter
      (@List.toFinset.{0} Thermal.Lattice
        (fun (a b : Thermal.Lattice) => @instDecidableEqProd.{0, 0} Int Int Int.instDecidableEq Int.instDecidableEq a b)
        l)) := @_root_.Thermal.algorithm_diameter

theorem ComparatorCore.check_Thermal_algorithm_radius :
    ∀ (a : Thermal.RuleCode), @Eq.{1} Nat (Thermal.Algorithm.ruleRadius a) (Thermal.radius (Thermal.decodeRule a)) := @_root_.Thermal.algorithm_radius

theorem ComparatorCore.check_Thermal_denominator_pos :
    ∀ (a : Thermal.RuleCode),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (Thermal.Algorithm.denominator a) := @_root_.Thermal.denominator_pos

theorem ComparatorCore.check_Thermal_algorithm_epsilon :
    ∀ (a : Thermal.RuleCode),
  @Eq.{1} Rat
    (Thermal.epsilon (Thermal.CA.q (Thermal.decodeRule a))
      (@Finset.card.{0} Thermal.Lattice (Thermal.CA.N (Thermal.decodeRule a))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
      (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.Algorithm.denominator a))) := @_root_.Thermal.algorithm_epsilon

theorem ComparatorCore.check_Thermal_algorithm_epsilonU :
    ∀ (a : Thermal.RuleCode),
  @Eq.{1} Rat (Thermal.epsilonU (Thermal.decodeRule a))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
      (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.Algorithm.uniqueDenominator a))) := @_root_.Thermal.algorithm_epsilonU

theorem ComparatorCore.check_Thermal_ruleDigit_correct :
    ∀ (a : Thermal.RuleCode) (Q : Nat)
  (hQ : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q) (n : Nat)
  (r : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Nat
    (Thermal.Algorithm.ruleDigit
      (@Prod.mk.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) a
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) Q
          (@Prod.mk.{0, 0} Nat Nat n (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) r)))))
    (@Fin.val (Thermal.CA.q (Thermal.decodeRule a))
      (Thermal.CA.rule (Thermal.decodeRule a)
        fun
          (i :
            @Subtype.{1} Thermal.Lattice fun (x : Thermal.Lattice) =>
              @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                  (@Finset.instSetLike.{0} Thermal.Lattice))
                (Thermal.CA.N (Thermal.decodeRule a)) x) =>
        @Prod.snd.{0, 0} (Fin Q)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin (Thermal.CA.q (Thermal.decodeRule a)))
          (Thermal.codedConfig (Thermal.decodeRule a) Q hQ n
            (@Subtype.val.{1} Thermal.Lattice
              (fun (x : Thermal.Lattice) =>
                @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
                    (@Finset.instSetLike.{0} Thermal.Lattice))
                  (Thermal.CA.N (Thermal.decodeRule a)) x)
              i))
          r)) := @_root_.Thermal.ruleDigit_correct

theorem ComparatorCore.check_Thermal_fraction_correct :
    ∀ (q D v k : Nat) (hD : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D)
  (hk : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k) (same equal : Bool),
  @Eq.{1} Rat
    (Thermal.ratDecode
      (Thermal.Algorithm.fraction
        (@Prod.mk.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool)))
          (@Prod.mk.{0, 0} Nat Nat q D)
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool)) v
            (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Bool Bool) k (@Prod.mk.{0, 0} Bool Bool same equal))))))
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) (@Nat.cast.{0} Rat Rat.instNatCast v)
          (@Nat.cast.{0} Rat Rat.instNatCast k))
        (@ite.{1} Rat (@Eq.{1} Bool same Bool.true) (instDecidableEqBool same Bool.true)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast.{0} Rat Rat.instNatCast k))
        (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
            (@HPow.hPow.{0, 0, 0} Rat Nat Rat
              (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid)))
              (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast.{0} Rat Rat.instNatCast D))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@ite.{1} Rat (@Eq.{1} Bool equal Bool.true) (instDecidableEqBool equal Bool.true)
              (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (@Nat.cast.{0} Rat Rat.instNatCast q)
                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
              (@Neg.neg.{0} Rat Rat.instNeg (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))))))) := @_root_.Thermal.fraction_correct

theorem ComparatorCore.check_Thermal_fraction_localWeight :
    ∀ (a : Thermal.RuleCode) (Q : Nat)
  (hQ : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q) (n : Nat) (r : Bool)
  (D v k : Nat) (hD : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D)
  (hk : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k),
  @Eq.{1} Rat
    (Thermal.ratDecode
      (Thermal.Algorithm.fraction
        (@Prod.mk.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool)))
          (@Prod.mk.{0, 0} Nat Nat (Thermal.Algorithm.qValue a) D)
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Bool Bool)) v
            (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Bool Bool) k
              (@Prod.mk.{0, 0} Bool Bool
                (@Decidable.decide
                  (@Eq.{1} Nat
                    (Thermal.Algorithm.visibleDigit
                      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} Nat Nat (Thermal.Algorithm.qValue a) Q)
                        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n
                          (@OfNat.ofNat.{0} Thermal.Algorithm.Point (nat_lit 0)
                            (@Zero.toOfNat0.{0} Thermal.Algorithm.Point
                              (@Prod.instZero.{0, 0} Int Int
                                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
                                (@MulZeroClass.toZero.{0} Int
                                  (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))))))))
                    (Thermal.Algorithm.visibleDigit
                      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} Nat Nat (Thermal.Algorithm.qValue a) Q)
                        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n (Thermal.Algorithm.direction r)))))
                  (instDecidableEqNat
                    (Thermal.Algorithm.visibleDigit
                      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} Nat Nat (Thermal.Algorithm.qValue a) Q)
                        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n
                          (@OfNat.ofNat.{0} Thermal.Algorithm.Point (nat_lit 0)
                            (@Zero.toOfNat0.{0} Thermal.Algorithm.Point
                              (@Prod.instZero.{0, 0} Int Int
                                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
                                (@MulZeroClass.toZero.{0} Int
                                  (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))))))))
                    (Thermal.Algorithm.visibleDigit
                      (@Prod.mk.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Thermal.Algorithm.Point)
                        (@Prod.mk.{0, 0} Nat Nat (Thermal.Algorithm.qValue a) Q)
                        (@Prod.mk.{0, 0} Nat Thermal.Algorithm.Point n (Thermal.Algorithm.direction r))))))
                (@Decidable.decide
                  (@Eq.{1} Nat
                    (Thermal.Algorithm.ruleDigit
                      (@Prod.mk.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) a
                        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) Q
                          (@Prod.mk.{0, 0} Nat Nat n (Thermal.Algorithm.layer r)))))
                    (Thermal.Algorithm.ruleDigit
                      (@Prod.mk.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) a
                        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) Q
                          (@Prod.mk.{0, 0} Nat Nat n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (Thermal.Algorithm.layer r)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (instDecidableEqNat
                    (Thermal.Algorithm.ruleDigit
                      (@Prod.mk.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) a
                        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) Q
                          (@Prod.mk.{0, 0} Nat Nat n (Thermal.Algorithm.layer r)))))
                    (Thermal.Algorithm.ruleDigit
                      (@Prod.mk.{0, 0} Thermal.Algorithm.Code (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) a
                        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) Q
                          (@Prod.mk.{0, 0} Nat Nat n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (Thermal.Algorithm.layer r)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))))))
    (@Thermal.localWeight Q (Thermal.decodeRule a)
      (@Thermal.Model.mk (Thermal.decodeRule a) Q
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast.{0} Rat Rat.instNatCast D))
        (fun (x : Bool) =>
          @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) (@Nat.cast.{0} Rat Rat.instNatCast v)
            (@Nat.cast.{0} Rat Rat.instNatCast k))
        fun (x : Bool) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast.{0} Rat Rat.instNatCast k))
      (Thermal.codedConfig (Thermal.decodeRule a) Q hQ n)
      (@Prod.mk.{0, 0} Thermal.Lattice Bool
        (@OfNat.ofNat.{0} Thermal.Lattice (nat_lit 0)
          (@Zero.toOfNat0.{0} Thermal.Lattice
            (@Prod.instZero.{0, 0} Int Int
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))))
        r)) := @_root_.Thermal.fraction_localWeight

theorem ComparatorCore.check_Thermal_tableProgram_correct :
    ∀ (a : Thermal.RuleCode) (tag : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (n : Nat),
  @Eq.{1} Rat
    (Thermal.ratDecode
      (Thermal.Algorithm.tableProgram
        (@Prod.mk.{0, 0} Thermal.Algorithm.Code
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat) a
          (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat tag n))))
    (Thermal.tableValue a tag n) := @_root_.Thermal.tableProgram_correct

theorem ComparatorCore.check_Thermal_weight_table_computable :
    @Exists.{1}
  (Prod.{0, 0} Thermal.RuleCode (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat) →
    Thermal.RatCode)
  fun
    (A :
      Prod.{0, 0} Thermal.RuleCode
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat) →
        Thermal.RatCode) =>
  And
    (@Computable.{0, 0}
      (Prod.{0, 0} Thermal.RuleCode
        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat))
      Thermal.RatCode
      (@Primcodable.prod.{0, 0} Thermal.RuleCode
        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat)
        (@Primcodable.prod.{0, 0} Nat (Prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat))
          (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
          (@Primcodable.prod.{0, 0} (List.{0} Thermal.Lattice) (List.{0} Nat)
            (@Primcodable.list.{0} Thermal.Lattice
              (@Primcodable.prod.{0, 0} Int Int (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
                (@Primcodable.ofDenumerable.{0} Int Denumerable.int)))
            (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))))
        (@Primcodable.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
          (@Primcodable.fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)))
      (@Primcodable.prod.{0, 0} Int Nat (@Primcodable.ofDenumerable.{0} Int Denumerable.int)
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
      A)
    (∀ (code : Thermal.RuleCode) (tag : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (n : Nat),
      @Eq.{1} Rat
        (Thermal.ratDecode
          (A
            (@Prod.mk.{0, 0} Thermal.RuleCode
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat) code
              (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat tag n))))
        (Thermal.tableValue code tag n)) := @_root_.Thermal.weight_table_computable

theorem ComparatorCore.check_Thermal_localWeight_congr :
    ∀ (F : Thermal.CA) (Q : Nat) (M : Thermal.Model F Q) (r : Bool) (ξ η : Thermal.Config (Thermal.CA.q F) Q)
  (he :
    ∀ (i : Thermal.Lattice),
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (Thermal.support F r) i →
        @Eq.{1} (Thermal.Site (Thermal.CA.q F) Q) (ξ i) (η i)),
  @Eq.{1} Rat
    (@Thermal.localWeight Q F M ξ
      (@Prod.mk.{0, 0} Thermal.Lattice Bool
        (@OfNat.ofNat.{0} Thermal.Lattice (nat_lit 0)
          (@Zero.toOfNat0.{0} Thermal.Lattice
            (@Prod.instZero.{0, 0} Int Int
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))))
        r))
    (@Thermal.localWeight Q F M η
      (@Prod.mk.{0, 0} Thermal.Lattice Bool
        (@OfNat.ofNat.{0} Thermal.Lattice (nat_lit 0)
          (@Zero.toOfNat0.{0} Thermal.Lattice
            (@Prod.instZero.{0, 0} Int Int
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))))
        r)) := @_root_.Thermal.localWeight_congr

theorem ComparatorCore.check_Thermal_weight_table_enumeration :
    ∀ (F : Thermal.CA) (Q : Nat) (M : Thermal.Model F Q) (r : Bool),
  @Exists.{1} (List.{0} Rat) fun (table : List.{0} Rat) =>
    ∀ (ξ : Thermal.Config (Thermal.CA.q F) Q),
      @Membership.mem.{0, 0} Rat (List.{0} Rat) (@List.instMembership.{0} Rat) table
        (@Thermal.localWeight Q F M ξ
          (@Prod.mk.{0, 0} Thermal.Lattice Bool
            (@OfNat.ofNat.{0} Thermal.Lattice (nat_lit 0)
              (@Zero.toOfNat0.{0} Thermal.Lattice
                (@Prod.instZero.{0, 0} Int Int
                  (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
                  (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))))
            r)) := @_root_.Thermal.weight_table_enumeration

theorem ComparatorCore.check_Thermal_fin_digits_spec :
    ∀ {b n : Nat} (d : Fin n → Fin b) (i : Fin n),
  @Eq.{1} Nat
    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@Fin.val
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b n)
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (Fin n → Fin b)
              (Fin
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b n)))
            (Fin n → Fin b)
            (fun (x : Fin n → Fin b) =>
              Fin
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b n))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (Fin n → Fin b)
                (Fin
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b n)))
              (Fin n → Fin b)
              (Fin
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b n))
              (@Equiv.instEquivLike.{1, 1} (Fin n → Fin b)
                (Fin
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b n))))
            (@finFunctionFinEquiv b n) d))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b (@Fin.val n i)))
      b)
    (@Fin.val b (d i)) := @_root_.Thermal.fin_digits_spec

theorem ComparatorCore.check_Thermal_decode_siteDigit :
    ∀ (q Q : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (hQ : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q)
  (s : Thermal.Site q Q),
  @Eq.{1} (Thermal.Site q Q)
    (Thermal.decodeSite q Q hq hQ
      (@Fin.val
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Q
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        (Thermal.siteDigit q Q s)))
    s := @_root_.Thermal.decode_siteDigit

theorem ComparatorCore.check_Thermal_decodeSite_mod :
    ∀ (q Q : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (hQ : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q) (n : Nat),
  @Eq.{1} (Thermal.Site q Q)
    (Thermal.decodeSite q Q hq hQ
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Q
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (Thermal.decodeSite q Q hq hQ n) := @_root_.Thermal.decodeSite_mod

theorem ComparatorCore.check_Thermal_finite_digit_coding_complete :
    ∀ (q Q : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (hQ : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q)
  (K : Finset.{0} Thermal.Lattice) (ξ : Thermal.Config q Q),
  @Exists.{1} Nat fun (n : Nat) =>
    ∀ (i : Thermal.Lattice),
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          K i →
        @Eq.{1} (Thermal.Site q Q)
          (Thermal.decodeSite q Q hq hQ
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Q
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                (@Encodable.encode.{0} Thermal.Lattice
                  (@Encodable.Prod.encodable.{0, 0} Int Int Int.encodable Int.encodable) i))))
          (ξ i) := @_root_.Thermal.finite_digit_coding_complete

theorem ComparatorCore.check_Thermal_table_coding_complete :
    ∀ (F : Thermal.CA) (Q : Nat)
  (hQ : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q) (r : Bool)
  (ξ : Thermal.Config (Thermal.CA.q F) Q),
  @Exists.{1} Nat fun (n : Nat) =>
    ∀ (i : Thermal.Lattice),
      @Membership.mem.{0, 0} Thermal.Lattice (Finset.{0} Thermal.Lattice)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Thermal.Lattice) Thermal.Lattice
            (@Finset.instSetLike.{0} Thermal.Lattice))
          (Thermal.support F r) i →
        @Eq.{1} (Thermal.Site (Thermal.CA.q F) Q) (Thermal.codedConfig F Q hQ n i) (ξ i) := @_root_.Thermal.table_coding_complete

theorem ComparatorCore.check_Thermal_z_nonneg :
    ∀ (F : Thermal.CA) (ε : Rat) (T : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (Thermal.z F ε T) := @_root_.Thermal.z_nonneg

theorem ComparatorCore.check_Thermal_W_sum_z :
    ∀ (F : Thermal.CA) (ε : Rat) (C : Finset.{0} Thermal.Lattice),
  @Eq.{1} Rat (Thermal.W F ε C)
    (@Finset.sum.{0, 0} (Finset.{0} Thermal.Lattice) Rat Rat.addCommMonoid (@Finset.powerset.{0} Thermal.Lattice C)
      fun (T : Finset.{0} Thermal.Lattice) => Thermal.z F ε T) := @_root_.Thermal.W_sum_z

theorem ComparatorCore.check_Thermal_W_ge_one :
    ∀ (F : Thermal.CA) (ε : Rat) (C : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (Thermal.W F ε C) := @_root_.Thermal.W_ge_one

theorem ComparatorCore.check_Thermal_coefficient_den_divides :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @Dvd.dvd.{0} Nat Nat.instDvd (Rat.den (Thermal.c F T))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Thermal.CA.q F)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Finset.card.{0} Thermal.Lattice (Thermal.inputSupport F T)))) := @_root_.Thermal.coefficient_den_divides

theorem ComparatorCore.check_Thermal_coefficient_empty :
    ∀ (F : Thermal.CA),
  @Eq.{1} Rat
    (Thermal.c F
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} Thermal.Lattice)
        (@Finset.instEmptyCollection.{0} Thermal.Lattice)))
    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) := @_root_.Thermal.coefficient_empty

theorem ComparatorCore.check_Thermal_coefficient_upper :
    ∀ (F : Thermal.CA) (T : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Rat Rat.instLE (Thermal.c F T)
    (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@Nat.cast.{0} Rat Rat.instNatCast (Thermal.CA.q F))
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@Finset.card.{0} Thermal.Lattice T)) := @_root_.Thermal.coefficient_upper

theorem ComparatorCore.check_Thermal_overlap_card :
    ∀ (F : Thermal.CA) (P : Finset.{0} Thermal.Lattice),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} Thermal.Lattice (Thermal.D F P))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Finset.card.{0} Thermal.Lattice (Thermal.CA.N F))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Finset.card.{0} Thermal.Lattice P)) := @_root_.Thermal.overlap_card

theorem ComparatorCore.check_Thermal_positive_model :
    ∀ (F : Thermal.CA) (Q : Nat) (M : Thermal.Model F Q)
  (he :
    And
      (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Thermal.Model.ε F Q M))
      (@LT.lt.{0} Rat Rat.instLT (@Thermal.Model.ε F Q M)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
  (ho :
    ∀ (r : Bool),
      @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Thermal.Model.openWeight F Q M r))
  (hc :
    ∀ (r : Bool),
      @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Thermal.Model.closedScale F Q M r))
  (ξ : Thermal.Config (Thermal.CA.q F) Q) (e : Thermal.Edge),
  @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    (@Thermal.localWeight Q F M ξ e) := @_root_.Thermal.positive_model

