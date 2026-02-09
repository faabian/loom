import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic

/- Ordered Monad Algebra instance for StateT -/
instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (StateT σ m) (σ -> l) where
  μ := (MAlgOrdered.μ $ (fun fs => fs.1 fs.2) <$> · ·)
  μ_ord_pure := by intro f; ext s₁; simp [pure, StateT.pure, MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe]; intros le x s
    have leM := @inst.μ_ord_bind (α × σ) (fun as => (fun fs => fs.1 fs.2) <$> f as.1 as.2) (fun as => (fun fs => fs.1 fs.2) <$> g as.1 as.2)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; intro; apply le

instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] [inst': MAlgDet m l]
   : MAlgDet (StateT σ m) (σ -> l) where
    angelic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, StateT.map]
      have h := inst'.angelic (α := α × σ) (c := c s) (ι := ι) (p := fun i x => p i x.1 x.2)
      simp [MAlg.lift, MAlg.μ] at h
      apply h
    demonic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, StateT.map]
      have h := inst'.demonic (α := α × σ) (c := c s) (ι := ι) (p := fun i x => p i x.1 x.2)
      simp [MAlg.lift, MAlg.μ] at h
      apply h

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (StateT ε m α) := by
  unfold StateT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (StateT ε m) where
  bind_mono_left h₁₂ _ := by
    simp [bind, StateT.bind]
    apply Lean.Order.MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ _ := by
    simp [bind, StateT.bind]
    apply Lean.Order.MonoBind.bind_mono_right (m := m)
    intro x; apply h₁₂

instance [Monad m] [CCPOBot m] : CCPOBot (StateT σ m) where
  compBot := fun _ => CCPOBot.compBot

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (StateT σ m) where
  prop := by
    intro α
    simp only [Lean.Order.bot]
    rw [← Lean.Order.fun_csup_eq]
    funext x
    simp only [Lean.Order.fun_csup, instCCPOBotStateTOfMonad]
    rw [CCPOBotLawful.prop]
    simp only [Lean.Order.bot]
    congr 1
    ext y
    simp [Lean.Order.empty_chain]


lemma MAlg.lift_StateT [Monad m] [LawfulMonad m] [CompleteLattice l] [inst: MAlgOrdered m l] (x : StateT σ m α) :
  MAlg.lift x post = fun s => MAlg.lift (x s) (fun xs => post xs.1 xs.2) := by
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ, StateT.map]

open Lean.Order
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (StateT σ m) where
  csup_lift {α} chain := by
    intro post hchain
    rw [show CCPO.csup hchain = fun_csup chain hchain from (fun_csup_eq chain hchain).symm]
    simp only [MAlg.lift_StateT]
    rw [@Pi.le_def]; intro s; simp only [fun_csup, iInf_apply]
    apply le_trans'
    apply MAlgPartial.csup_lift (m := m)
    simp only [le_iInf_iff]
    intro x ⟨f, hf, hx⟩
    rw [← hx]
    exact iInf_le_of_le f (iInf_le_of_le hf (le_refl _))



attribute [-simp] le_bot_iff in
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)]  [MonoBind m]
  [MAlgTotal m] : MAlgTotal (StateT σ m) where
  bot_lift := by
    intro α post
    simp only [MAlg.lift_StateT]
    rw [@Pi.le_def]; intro s; simp
    conv_lhs => rw [show (Lean.Order.bot : StateT σ m α) s = Lean.Order.bot from by
      simp only [Lean.Order.bot]; rw [← Lean.Order.fun_csup_eq]
      unfold Lean.Order.fun_csup; simp [Lean.Order.empty_chain]]
    apply MAlgTotal.bot_lift (m := m)

instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [inst': NoFailure m] : NoFailure (StateT σ m) where
  noFailure := by
    intro _ _; simp [MAlg.lift_StateT, inst'.noFailure]; rfl

/- Monad Transformer Algebra instance for StateT -/
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l] :
  MAlgLift m l (StateT σ m) (σ -> l) where
    μ_lift := by
      intros; simp [MAlg.lift_StateT]; ext;
      simp [liftM, instMonadLiftTOfMonadLift, MonadLift.monadLift]
      simp [StateT.lift, MAlg.lift]; rfl
