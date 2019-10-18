module Lecture1 where

-- comment lol

-- "X is of type Y" -- X : Y
-- same as X :: Y in haskell

-- типове == твърдения
-- докажеш твърдение X == стойност от типа X

-- One == истина
-- винаги можеш да построиш стойност от него много лесно
data One : Set where
  <> : One

-- Zero == лъжа
-- не можеш да построиш стойности от него
data Zero : Set where

-- data Bool = Tt | Ff

-- пример за дефиниция с алтернативи
data Bool : Set where
  tt : Bool
  ff : Bool

-- пример за писане на функции
not : Bool -> Bool
not tt = ff
not ff = tt

-- пеанови естествени числа/унарно кодиране на естествените числа
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

-- прагма която ни позволява да пишем числени литерали за естествени числа
{-# BUILTIN NATURAL Nat #-}
-- например
-- 3 == suc (suc (suc zero))
-- 5 == suc (suc (suc (suc (suc zero))))

-- събиране на числа, пример за функция
_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

-- умножение на числа
_*_ : Nat -> Nat -> Nat
zero * m = zero
suc n * m = m + (n * m)

-- функция над естествени числа, която връща с тип
-- с тази функция(предикат) изразяваме какво означава
-- "число да е четно"
Even : Nat -> Set
Even zero = One -- 0
Even (suc zero) = Zero -- 1
Even (suc (suc n)) = Even n -- 2 + n

-- пример за полза и стъпки на редукция
-- Even 2
-- Even (suc (suc zero))
-- Even zero
-- One
2-is-even : Even 2
2-is-even = <>

-- пример за нещо което не можем да докажем, щото не е вярно
-- Even 3
-- Even (suc (suc (suc zero)))
-- Even (suc zero)
-- Zero
--3-is-even : Even 3
--3-is-even = {!!}

-- равенство на естествени числа
-- отново функция която взима естествени числа и връща тип
_=N=_ : Nat -> Nat -> Set
zero =N= zero = One
zero =N= suc m = Zero
suc n =N= zero = Zero
suc n =N= suc m = n =N= m

-- доказателство че 4 == 1 + 3
-- нещата тук са константи и agda може да ги сметне сама
5-equals-1+3 : 4 =N= (1 + 3)
5-equals-1+3 = <>


-- наредени двойки, параметризирани по типовете които държат
-- същото като
-- data Pair x y = Pair x y
-- на хаскел
data Pair (X Y : Set) : Set where
  _,_ : X -> Y -> Pair X Y

-- наредени двойки от естествено число и предикат,
-- който е верен за даденото естествено число
-- параметризирани са по предикатите които ще задоволяваме
data SuchThat (P : Nat -> Set) : Set where
  _,_ : (n : Nat) -> P n -> SuchThat P

-- пример за наредената двойка 2 и доказателство че 2 е четно
2-example : SuchThat Even
2-example = 2 , <>

-- финалната сигнатура на функцията ни, гарнатираща коректност
div2 : (n : Nat) -> Even n -> SuchThat \m -> (2 * m) =N= n
div2 zero <> = zero , <>
div2 (suc zero) ()
div2 (suc (suc n')) evenn' = {!!} , {!!}
--Thanks for coming to my ted talk



-- Извън лекцията:
-- довършване на доказателството и имплементацията на div2
-- ще ни трябват няколко инструменти

-- рефлексивност на равенството
=N=-refl : (n : Nat) -> n =N= n
=N=-refl zero = <>
=N=-refl (suc n) = =N=-refl n

-- централна лема която помага за комутативност на събирането
+-suc-commut : (n m : Nat) -> (n + (suc m)) =N= suc (n + m)
+-suc-commut zero m = =N=-refl m
+-suc-commut (suc n) m = +-suc-commut n m

-- транзитивност на равенството
=N=-trans : (n m k : Nat) -> n =N= m -> m =N= k -> n =N= k
=N=-trans zero zero zero n==m m==k = <>
=N=-trans (suc n) (suc m) (suc k) n==m m==k = =N=-trans n m k n==m m==k

-- with ни позволява да правим рекурсивно извикване
-- което също така влияе на типовете на вече match-нати неща
-- не е наистина нужно в този случай но е по-просто така,
-- оптималното нещо би било да се дефинира SuchThat като
-- record тип, за да можем да достъпваме полетата му директно,
-- без патърн мачове

-- of note че голямото доказателство помолих agda да го генерира
-- освен това много от аргументите биха били "имплицитни"
-- и не би било толкова грозно попринцип
div2' : (n : Nat) -> Even n -> SuchThat \m -> (2 * m) =N= n
div2' zero <> = zero , <>
div2' (suc zero) ()
div2' (suc (suc n')) evenn' with div2' n' evenn'
div2' (suc (suc n')) evenn' | m , Pm
  = suc m , =N=-trans (m + suc (m + zero))
                      (suc (m + (m + zero)))
                      (suc n')
                      (+-suc-commut m (m + zero))
                      Pm
