module kr2018 where
open import Data.Empty
open import Data.List
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary using (yes; no; Dec)

data Obj : Set where
  a b c : Obj

data A : Set where
  handEmpty : A
  onTable : Obj → A
  clear : Obj → A
  holding : Obj → A
  on : Obj → Obj → A

_≡o?_ : Decidable (_≡_ {A = Obj})
a ≡o? a = yes refl
a ≡o? b = no (λ ())
a ≡o? c = no (λ ())
b ≡o? a = no (λ ())
b ≡o? b = yes refl
b ≡o? c = no (λ ())
c ≡o? a = no (λ ())
c ≡o? b = no (λ ())
c ≡o? c = yes refl

_≡?_ : Decidable (_≡_ {A = A})
handEmpty ≡? handEmpty = yes refl
handEmpty ≡? onTable x = no (λ ())
handEmpty ≡? clear x = no (λ ())
handEmpty ≡? holding x = no (λ ())
handEmpty ≡? on x x₁ = no (λ ())
onTable x ≡? handEmpty = no (λ ())
onTable x ≡? onTable x' with x ≡o? x'
onTable x ≡? onTable .x | yes refl = yes refl
onTable x ≡? onTable x' | no x≢x' = no λ {refl → x≢x' refl}
onTable x ≡? clear x' = no (λ ())
onTable x ≡? holding x' = no (λ ())
onTable x ≡? on x' x'' = no (λ ())
clear x ≡? handEmpty = no (λ ())
clear x ≡? onTable x₁ = no (λ ())
clear x ≡? clear x' with x ≡o? x'
clear x ≡? clear .x | yes refl = yes refl
clear x ≡? clear x' | no x≢x' = no λ {refl → x≢x' refl}
clear x ≡? holding x₁ = no (λ ())
clear x ≡? on x₁ x₂ = no (λ ())
holding x ≡? handEmpty = no (λ ())
holding x ≡? onTable x₁ = no (λ ())
holding x ≡? clear x₁ = no (λ ())
holding x ≡? holding x' with x ≡o? x'
holding x ≡? holding .x | yes refl = yes refl
holding x ≡? holding x' | no x≢x' = no λ {refl → x≢x' refl}
holding x ≡? on x₁ x₂ = no (λ ())
on x x₁ ≡? handEmpty = no (λ ())
on x x₁ ≡? onTable x₂ = no (λ ())
on x x₁ ≡? clear x₂ = no (λ ())
on x x₁ ≡? holding x₂ = no (λ ())
on x x₁ ≡? on x' x₁' with x ≡o? x' | x₁ ≡o? x₁'
on x x₁ ≡? on .x .x₁ | yes refl | yes refl = yes refl
on x x₁ ≡? on .x x₁' | yes refl | no x₁≢x₁' = no λ {refl → x₁≢x₁' refl}
on x x₁ ≡? on x' .x₁ | no x≢x' | yes refl = no λ {refl → x≢x' refl}
on x x₁ ≡? on x' x₁' | no x≢x' | no x₁≢x₁' = no λ {refl → x₁≢x₁' refl}

data Pred : Set where
  _∧_ : Pred → Pred → Pred
  ¬_ : Pred → Pred
  atom : A → Pred
infixl 4 _∧_
infixl 5 ¬_

World : Set
World = List A

data Polarity : Set where
  + - : Polarity
neg : Polarity → Polarity
neg + = -
neg - = +

infix 3 _⊨[_]_
data _⊨[_]_ : World → Polarity → Pred → Set where
  flip : ∀{w t P} → w ⊨[ neg t ] P → w ⊨[ t ] ¬ P
  both : ∀{w t P Q} → w ⊨[ t ] P → w ⊨[ t ] Q → w ⊨[ t ] P ∧ Q
  somewhere : ∀{w a} → a ∈ w → w ⊨[ + ] atom a
  nowhere : ∀{w a} → a ∉ w → w ⊨[ - ] atom a

NPred : Set
NPred = List (Polarity × A)

_∈⟨_⟩ : World → NPred → Set
w ∈⟨ N ⟩ = (∀ a → (+ , a) ∈ N → a ∈ w) × (∀ a → (- , a) ∈ N → a ∉ w)

infixr 3 _↓[_]_
_↓[_]_ : Pred → Polarity → NPred → NPred
P ∧ Q ↓[ t ] N = Q ↓[ t ] P ↓[ t ] N
¬ P ↓[ t ] N = P ↓[ neg t ] N
atom x ↓[ t ] N = (t , x) ∷ N

infix 3 _<:_
data _<:_ : NPred → NPred → Set where
  []<:_ : ∀ N → [] <: N
  atom<: : ∀{t x N M} → (t , x) ∈ M → N <: M → (t , x) ∷ N <: M

data Action : Set where
  pickup_from_table_b : Action
  pickup_from_table_a : Action
  putdown_on_stack_b_c : Action
  putdown_on_stack_a_b : Action

Ctx : Set
Ctx = Action → NPred × NPred

data Plan : Set where
  do : Action → Plan → Plan
  halt : Plan

del : A → NPred → NPred
del x [] = []
del x ((t' , x') ∷ M) with x ≡? x'
del x ((t' , .x) ∷ M) | yes refl = del x M
del x ((t' , x') ∷ M) | no x≢x' = (t' , x') ∷ del x M

del-spec : ∀ t x N → (t , x) ∉ del x N
del-spec t x [] ()
del-spec t x ((t' , y) ∷ N) tx∈N' with x ≡? y
del-spec t x ((t' , .x) ∷ N) tx∈N' | yes refl = del-spec t x N tx∈N'
del-spec t x ((.t , .x) ∷ N) (here refl)  | no x≢y = x≢y refl
del-spec t x ((t' , y) ∷ N) (there tx∈N') | no x≢y = del-spec t x N tx∈N'

del-∈ : ∀{M y x} → x ∈ del y M → x ∈ M
del-∈ {[]}             ()
del-∈ {(t , z) ∷ M}{y} x∈ with y ≡? z
del-∈ {(t , z) ∷ M}{y} x∈ | yes refl = there (del-∈ x∈)
del-∈ {(t , z) ∷ M}{y} (here refl) | no z≢y = here refl
del-∈ {(t , z) ∷ M}{y} (there x∈)  | no z≢y = there (del-∈ x∈)

_⊔_ : NPred → NPred → NPred
M ⊔ [] = M
M ⊔ ((t , x) ∷ N) = (t , x) ∷ del x M ⊔ N

⊔-right-bias : ∀{N x M} → x ∈ N → x ∈ M ⊔ N
⊔-right-bias {[]}    ()
⊔-right-bias {y ∷ N} (here refl) = here refl
⊔-right-bias {y ∷ N}{x}{M} (there x∈N) = there (⊔-right-bias x∈N)

⊔-union : ∀{N t x M} → (t , x) ∈ M ⊔ N → (t , x) ∈ M × (neg t , x) ∉ N ⊎ (t , x) ∈ N
⊔-union {[]} x∈M = inj₁ (x∈M , λ ())
⊔-union {x ∷ N} (here refl)   = inj₂ (here refl)
⊔-union {x ∷ N}{t}{y}{M} (there x∈M⊔N) = h (⊔-union {N}{t}{y} x∈M⊔N)
  where h : (t , y) ∈ del (proj₂ x) M × (neg t , y) ∉ N ⊎ (t , y) ∈ N → (t , y) ∈ M × (neg t , y) ∉ x ∷ N ⊎ (t , y) ∈ x ∷ N
        h (inj₁ (ty∈ , -ty∉N)) = inj₁ (del-∈ ty∈ , h') where
          h' : (neg t , y) ∉ x ∷ N
          h' (here refl) = del-spec t y M ty∈
          h' (there -ty∈N) = -ty∉N -ty∈N
        h (inj₂ pf) = inj₂ (there pf)

data _⊢_∶_↝_ : Ctx → Plan → NPred → NPred → Set where
  halt : ∀{Γ M' M} → M' <: M → Γ ⊢ halt ∶ M ↝ M'
  seq : ∀{α M₁' M₁ M₂ M₃ Γ f}
      → M₁' <: M₁
      → Γ α ≡ (M₁' , M₂)
      → Γ ⊢ f ∶ M₁ ⊔ M₂ ↝ M₃
      → Γ ⊢ do α f ∶ M₁ ↝ M₃

ActionHandler : Set
ActionHandler = Action → World → World

⟦_⟧ : Plan → ActionHandler → World → World
⟦ do α f ⟧ σ w = ⟦ f ⟧ σ (σ α w)
⟦ halt ⟧ σ w = w

WfHandler : Ctx → ActionHandler → Set
WfHandler Γ σ =
  ∀{α M M' N} → Γ α ≡ (M' , N) → M' <: M → ∀{w} → w ∈⟨ M ⟩ → σ α w ∈⟨ M ⊔ N ⟩

remove : A → World → World
remove x [] = []
remove x (y ∷ w) with x ≡? y
remove x (.x ∷ w) | yes refl = remove x w
remove x (y ∷ w)  | no x≢y = y ∷ remove x w

remove-other : ∀{w x} → x ∈ w → ∀{y} → x ≢ y → x ∈ remove y w
remove-other {[]}    x∈w x≢y = x∈w
remove-other {z ∷ w} x∈w {y} x≢z with y ≡? z
remove-other {z ∷ w} (here refl) {.z} x≢x | yes refl = ⊥-elim (x≢x refl)
remove-other {z ∷ w} (there x∈w) {.z} x≢z | yes refl = remove-other x∈w x≢z
remove-other {z ∷ w} (here refl) {y} x≢z | no y≢x = here refl
remove-other {z ∷ w} (there x∈w) {y} x≢z | no y≢x = there (remove-other x∈w x≢z)

remove-spec : (x : A) (w : World) → x ∉ remove x w
remove-spec x [] = λ ()
remove-spec x (y ∷ w) with x ≡? y
remove-spec x (.x ∷ w) | yes refl = remove-spec x w
remove-spec x (y ∷ w)  | no x≢y = contr where
  contr : x ∉ y ∷ remove x w
  contr (here x≡y) = x≢y x≡y
  contr (there x∈) = remove-spec x w x∈

∉-tail : {A : Set} {xs : List A} {x y : A} → x ∉ y ∷ xs → x ∉ xs
∉-tail x∉y∷ys x∈ys = x∉y∷ys (there x∈ys)

remove-resp-∈ : ∀{N x y} → x ∈ remove y N → x ∈ N
remove-resp-∈ {[]}    x∈ = x∈
remove-resp-∈ {z ∷ N}{x}{y} x∈ with y ≡? z
remove-resp-∈ {z ∷ N}{x}{y} x∈ | yes refl = there (remove-resp-∈ {N} x∈)
remove-resp-∈ {z ∷ N} {x} {y} (here refl) | no y≢x = here refl
remove-resp-∈ {z ∷ N} {x} {y} (there x∈)  | no y≢x = there (remove-resp-∈ x∈)

remove-resp-∉ : ∀{N x} → x ∉ N → ∀{y} → x ∉ remove y N
remove-resp-∉ {[]}    x∉N x∈N' = x∉N x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} x∈N' with y ≡? x
remove-resp-∉ {x ∷ N} x∉N {.x} x∈N' | yes refl = remove-resp-∉ (∉-tail x∉N) x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} (here refl)  | no x≢y = x∉N (here refl)
remove-resp-∉ {x ∷ N} x∉N {y} (there x∈N') | no x≢y = remove-resp-∉ (∉-tail x∉N) x∈N'

σα : NPred → World → World
σα [] w = w
σα ((+ , x) ∷ N) w = x ∷ σα N w
σα ((- , x) ∷ N) w = remove x (σα N w)

canonical-σ : Ctx → ActionHandler
canonical-σ Γ α = σα (proj₂ (Γ α))

sym≢ : {A : Set} → {x y : A} → x ≢ y → y ≢ x
sym≢ x≢y refl = x≢y refl

postulate
  implicit-consistency-assumption : (t : Polarity) (x : A) → ∀ N → (t , x) ∈ N → (neg t , x) ∉ N

σα-insert : ∀{N x} → (+ , x) ∈ N → ∀ w → x ∈ σα N w
σα-insert {.(_ ∷ _)} (here refl) w = here refl
σα-insert {(- , y) ∷ N}{x} (there +x∈N) w with y ≡? x
σα-insert {(- , y) ∷ N}{.y} (there +y∈N) w | yes refl = ⊥-elim (implicit-consistency-assumption - y ((- , y) ∷ N) (here refl) (there +y∈N))
σα-insert {(- , y) ∷ N}{x} (there +x∈N)  w | no y≢x = remove-other (σα-insert +x∈N w) (sym≢ y≢x)
σα-insert {(+ , y) ∷ N}{x} (there +x∈N) w with y ≡? x
σα-insert {(+ , y) ∷ N}{.y} (there +x∈N) w | yes refl = here refl
σα-insert {(+ , y) ∷ N}{x} (there +x∈N)  w | no y≢x = there (σα-insert +x∈N w)

σα-keep : ∀{x w} → x ∈ w → ∀{N} → (- , x) ∉ N → x ∈ σα N w
σα-keep     x∈w {[]}          -x∉N  = x∈w
σα-keep {x} x∈w {(+ , y) ∷ N} -ty∉N = there (σα-keep x∈w (∉-tail -ty∉N))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N with x ≡? y
σα-keep {x} x∈w {(- , .x) ∷ N} -ty∉N | yes refl = ⊥-elim (-ty∉N (here refl))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N  | no x≢y = remove-other (σα-keep x∈w (∉-tail -ty∉N)) x≢y

σα-delete : ∀{x N} → (- , x) ∈ N → ∀ w → x ∉ σα N w
σα-delete {x}{[]}    () w
σα-delete {x}{y ∷ N} (here refl) w = remove-spec x (σα N w)
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w with y ≡? x
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w | yes refl = ⊥-elim (implicit-consistency-assumption + y ((+ , y) ∷ N) (here refl) (there -x∈N))
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w | no y≢x = contr where
  contr : x ∉ y ∷ σα N w
  contr (here x≡y) = y≢x (sym x≡y)
  contr (there x∈) = σα-delete -x∈N w x∈
σα-delete {x} {(- , y) ∷ N} (there -x∈N) w = remove-resp-∉ (σα-delete -x∈N w) {y}

σα-source : ∀{N x w} → x ∈ σα N w → (+ , x) ∈ N ⊎ x ∈ w
σα-source {[]}          {x} x∈ = inj₂ x∈
σα-source {(+ , y) ∷ N} {x} x∈ with x ≡? y
σα-source {(+ , .x) ∷ N} {x}{w} x∈ | yes refl = inj₁ (here refl)
σα-source {(+ , y) ∷ N}  {x}{w} (here refl) | no y≢y = ⊥-elim (y≢y refl)
σα-source {(+ , y) ∷ N}  {x}{w} (there x∈)  | no x≢y = h (σα-source x∈) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (+ , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w) = inj₂ x∈w
σα-source {(- ,  y) ∷ N} {x} x∈ with x ≡? y
σα-source {(- , .x) ∷ N} {x}{w} x∈ | yes refl = ⊥-elim (remove-spec x (σα N w) x∈)
σα-source {(- ,  y) ∷ N} {x}{w} x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (- , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w)  = inj₂ x∈w

σα-keep-∉ : ∀{x w} → x ∉ w → ∀{N} → (+ , x) ∉ N → x ∉ σα N w
σα-keep-∉        x∉w {[]}          +x∉N x∈w = x∉w x∈w
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (here refl) = +x∉N (here refl)
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (there x∈) = σα-keep-∉ x∉w (∉-tail +x∉N) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N} +x∉N x∈ with x ≡? y
σα-keep-∉ {x}{w} x∉w {(- , .x) ∷ N} +x∉N x∈ | yes refl = remove-spec x (σα N w) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N}  +x∉N x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → ⊥
  h (inj₁ +x∈N) = +x∉N (there +x∈N)
  h (inj₂ x∈w)  = x∉w x∈w

wf-canonical-σ : ∀ Γ → WfHandler Γ (canonical-σ Γ)
wf-canonical-σ Γ {α} {M} {.(proj₁ (Γ α))} {.(proj₂ (Γ α))} refl M'<:M {w} w∈⟨M⟩ =
  (λ a +a∈M → lt a (⊔-union +a∈M)) ,
  λ a -a∈M a∈w → rt a (⊔-union -a∈M) a∈w
  where lt : ∀ x → (+x∈M⊎N : (+ , x) ∈ M × (- , x) ∉ proj₂ (Γ α) ⊎ (+ , x) ∈ proj₂ (Γ α)) → x ∈ canonical-σ Γ α w
        lt x (inj₁ (+x∈M , -x∉N)) = σα-keep (proj₁ w∈⟨M⟩ x +x∈M) -x∉N
        lt x (inj₂ +x∈N) = σα-insert +x∈N w

        rt : ∀ x → (+x∈M⊎N : (- , x) ∈ M × (+ , x) ∉ proj₂ (Γ α) ⊎ (- , x) ∈ proj₂ (Γ α)) → x ∉ canonical-σ Γ α w
        rt x (inj₁ (-x∈M , +x∉N)) = σα-keep-∉ (proj₂ w∈⟨M⟩ x -x∈M) +x∉N
        rt x (inj₂ -x∈N) = σα-delete -x∈N w

<:-resp-∈ : ∀{N M} → N <: M → ∀{w} → w ∈⟨ M ⟩ → w ∈⟨ N ⟩
<:-resp-∈ ([]<: N) w∈⟨M⟩ = (λ _ ()) , λ _ ()
<:-resp-∈ (atom<: {t}{x}{N}{M} tx∈M N<:M) {w} w∈⟨M⟩ = lt , rt where
  ih : w ∈⟨ N ⟩
  ih = <:-resp-∈ N<:M w∈⟨M⟩

  lt : ∀ a' → (+ , a') ∈ (t , x) ∷ N → a' ∈ w
  lt a' (here px) = proj₁ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (sym px) tx∈M)
  lt a' (there +a'∈N) = proj₁ ih a' +a'∈N

  rt : ∀ a' → (- , a') ∈ (t , x) ∷ N → a' ∉ w
  rt a' (here px) a'∈w =
    proj₂ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (sym px) tx∈M) a'∈w
  rt a' (there -a'∈N) a'∈w = proj₂ ih a' -a'∈N a'∈w

sound : ∀{w σ M Γ f N}
      → WfHandler Γ σ
      → Γ ⊢ f ∶ M ↝ N
      → w ∈⟨ M ⟩
      → ⟦ f ⟧ σ w ∈⟨ N ⟩
sound wfσ (halt N<:M) w∈⟨M⟩ = <:-resp-∈ N<:M w∈⟨M⟩
sound {w}{σ}{M} wfσ (seq {α}{M₁'}{M₁}{M₂} M₁'<:M Γα≡M₁',M₂ Γ⊢f∶M⊔M₂↝N) w∈⟨M⟩ =
  sound wfσ Γ⊢f∶M⊔M₂↝N σαw∈⟨M⊔M₂⟩
  where σαw∈⟨M⊔M₂⟩ : σ α w ∈⟨ M ⊔ M₂ ⟩
        σαw∈⟨M⊔M₂⟩ = wfσ {M = M} Γα≡M₁',M₂ M₁'<:M w∈⟨M⟩

_↓₊ : Pred → NPred
P ↓₊ = P ↓[ + ] []

postulate
  ↓-complete : ∀{w t P} → w ⊨[ t ] P → w ∈⟨ P ↓[ t ] [] ⟩
  ↓-sound : ∀{w t P} → w ∈⟨ P ↓[ t ] [] ⟩ → w ⊨[ t ] P

sound' : ∀{Γ f P Q σ}
       → WfHandler Γ σ
       → Γ ⊢ f ∶ (P ↓₊) ↝ (Q ↓₊)
       → ∀{w} → w ⊨[ + ] P
       → ⟦ f ⟧ σ w ⊨[ + ] Q
sound' {Γ}{f}{P}{Q}{σ} wfσ Γ⊢f∶P↓₊↝Q↓₊ {w} w⊨₊P = ↓-sound h
  where h : ⟦ f ⟧ σ w ∈⟨ Q ↓₊ ⟩
        h = sound wfσ Γ⊢f∶P↓₊↝Q↓₊ (↓-complete w⊨₊P)

Γ₁ : Ctx
Γ₁ pickup_from_table_b  =
  (atom handEmpty ∧ atom (onTable b) ∧ atom (clear b)) ↓₊ ,
  ((¬ atom handEmpty ∧ ¬ atom (onTable b) ∧ atom (holding b)) ↓₊)
Γ₁ pickup_from_table_a  =
  (atom handEmpty ∧ atom (onTable a) ∧ atom (clear a)) ↓₊ ,
  ((¬ atom handEmpty ∧ ¬ atom (onTable a) ∧ atom (holding a)) ↓₊)
Γ₁ putdown_on_stack_b_c =
  (atom (holding b) ∧ atom (clear c)) ↓₊ ,
  (¬ atom (holding b) ∧ ¬ atom (clear c) ∧ atom (on b c) ∧ atom handEmpty) ↓₊
Γ₁ putdown_on_stack_a_b =
  (atom (holding a) ∧ atom (clear b)) ↓₊ ,
  (¬ atom (holding a) ∧ ¬ atom (clear b) ∧ atom (on a b) ∧ atom handEmpty) ↓₊

plan₁ : Plan
plan₁ = do pickup_from_table_b
        (do putdown_on_stack_b_c
        (do pickup_from_table_a
        (do putdown_on_stack_a_b
         halt)))

P₀ : Pred
P₀ = atom (onTable a) ∧ atom (onTable b) ∧ atom (onTable c) ∧ atom (clear a) ∧ atom (clear b) ∧ atom (clear c) ∧ atom handEmpty

Q₀ : Pred
Q₀ = atom (on a b) ∧ atom (on b c)

Γ₁⊢plan₁∶P₀↓₊↝Q₀↓₊ : Γ₁ ⊢ plan₁ ∶ (P₀ ↓₊) ↝ (Q₀ ↓₊)
Γ₁⊢plan₁∶P₀↓₊↝Q₀↓₊ =
  seq (atom<: (there (there (here refl)))
      (atom<: (there (there (there (there (there (here refl))))))
      (atom<: (here refl)
      ([]<: ((+ , handEmpty) ∷
             (+ , clear c) ∷
             (+ , clear b) ∷
             (+ , clear a) ∷
             (+ , onTable c) ∷ (+ , onTable b) ∷ (+ , onTable a) ∷ [])))))
      refl
  (seq (atom<: (there (there (there (here refl))))
       (atom<: (here refl)
       ([]<: ((+ , holding b) ∷
              (- , onTable b) ∷
              (- , handEmpty) ∷
              (+ , clear c) ∷
              (+ , clear b) ∷
              (+ , clear a) ∷ (+ , onTable c) ∷ (+ , onTable a) ∷ []))))
       refl
  (seq (atom<: (there (there (there (there (there (there (here refl)))))))
       (atom<: (there (there (there (there (there (there (there (there (here refl)))))))))
       (atom<: (here refl)
       ([]<: ((+ , handEmpty) ∷
              (+ , on b c) ∷
              (- , clear c) ∷
              (- , holding b) ∷
              (- , onTable b) ∷
              (+ , clear b) ∷
              (+ , clear a) ∷ (+ , onTable c) ∷ (+ , onTable a) ∷ [])))))
       refl
  (seq (atom<: (there (there (there (there (there (there (there (here refl))))))))
       (atom<: (here refl)
       ([]<: ((+ , holding a) ∷
              (- , onTable a) ∷
              (- , handEmpty) ∷
              (+ , on b c) ∷
              (- , clear c) ∷
              (- , holding b) ∷
              (- , onTable b) ∷
              (+ , clear b) ∷ (+ , clear a) ∷ (+ , onTable c) ∷ []))))
       refl
  (halt (atom<: (there (there (there (there (there (here refl))))))
        (atom<: (there (here refl))
        ([]<: ((+ , handEmpty) ∷
               (+ , on a b) ∷
               (- , clear b) ∷
               (- , holding a) ∷
               (- , onTable a) ∷
               (+ , on b c) ∷
               (- , clear c) ∷
               (- , holding b) ∷
               (- , onTable b) ∷ (+ , clear a) ∷ (+ , onTable c) ∷ []))))))))
