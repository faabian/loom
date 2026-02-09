import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic

/- Ordered Monad Algebra instance for ReaderT -/
instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (ReaderT σ m) (σ -> l) where
  μ := fun rp r => inst.μ $ (· r) <$> rp r
  μ_ord_pure := by
    intros l; simp [pure, ReaderT.pure]; ext r
    solve_by_elim [MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe]; intros le x r
    have leM := @inst.μ_ord_bind (α) (fun a => (· r) <$> f a r) (fun a => (· r) <$> g a r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; intro; apply le


instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] [inst': MAlgDet m l]
   : MAlgDet (ReaderT σ m) (σ -> l) where
    angelic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map]
      have h := inst'.angelic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MAlg.lift, MAlg.μ] at h
      apply h
    demonic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map]
      have h := inst'.demonic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MAlg.lift, MAlg.μ] at h
      apply h


instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (ReaderT ε m α) := by
  unfold ReaderT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (ReaderT ε m) where
  bind_mono_left h₁₂ _ := by
    simp [bind, ReaderT.bind]
    apply Lean.Order.MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ _ := by
    simp [bind]
    apply Lean.Order.MonoBind.bind_mono_right (m := m)
    intro x; apply h₁₂

instance [Monad m] [CCPOBot m] : CCPOBot (ReaderT σ m) where
  compBot := fun _ => CCPOBot.compBot

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (ReaderT σ m) where
  prop := by
    intro α
    simp only [Lean.Order.bot]
    rw [← Lean.Order.fun_csup_eq]
    funext x
    simp only [Lean.Order.fun_csup, instCCPOBotReaderTOfMonad]
    rw [CCPOBotLawful.prop]
    simp only [Lean.Order.bot]
    congr 1
    ext y
    simp [Lean.Order.empty_chain]

lemma MAlg.lift_ReaderT [Monad m] [LawfulMonad m] [CompleteLattice l] [inst: MAlgOrdered m l] (x : ReaderT σ m α) :
  MAlg.lift x post = fun s => MAlg.lift (x s) (fun xs => post xs s) := by
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ]

open Lean.Order
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (ReaderT σ m) where
  csup_lift {α} chain := by
    intro post hchain
    rw [show CCPO.csup hchain = fun_csup chain hchain from (fun_csup_eq chain hchain).symm]
    simp only [MAlg.lift_ReaderT]
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
  [MAlgTotal m] : MAlgTotal (ReaderT σ m) where
  bot_lift := by
    intro α post
    simp only [MAlg.lift_ReaderT]
    rw [@Pi.le_def]; intro s; simp
    conv_lhs => rw [show (Lean.Order.bot : ReaderT σ m α) s = Lean.Order.bot from by
      simp only [Lean.Order.bot]; rw [← Lean.Order.fun_csup_eq]
      unfold Lean.Order.fun_csup; simp [Lean.Order.empty_chain]]
    apply MAlgTotal.bot_lift (m := m)

instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [inst': NoFailure m] : NoFailure (ReaderT σ m) where
  noFailure := by
    intro _ _; simp [MAlg.lift_ReaderT, inst'.noFailure]; rfl

/- Monad Transformer Algebra instance for ReaderT -/
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l] :
  MAlgLift m l (ReaderT σ m) (σ -> l) where
    μ_lift := by
      intros; simp [MAlg.lift_ReaderT]; ext;
      simp [liftM, instMonadLiftTOfMonadLift, MonadLift.monadLift]; rfl
