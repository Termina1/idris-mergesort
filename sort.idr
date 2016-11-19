module Main

-- [02:09] <{AS}> terminal: also instead of ListSum you can define a more general Permutation predicate
-- [02:09] <{AS}> And then write Pemutation (xs ++ ys) zs
-- [02:11] <{AS}> SmallestElem could probably be simplified or dropped totally
-- [02:12] <{AS}> I think you can just do this by induction over the IsSorted predicate and perhaps the Permutation/ListSum predicate
-- [02:13] <terminal> ok, permtuation and subset would be good additions, but what about with patterns, I see how I can make totalorder to work with patterns, but I don't see how can I remove lets with it
-- [02:13] <{AS}> terminal: I meant mergeHole
-- [02:14] <{AS}> It will look nicer with with patterns
-- [02:14] <{AS}> Although I guess that's not really that important here
-- [02:15] <{AS}> terminal: anyway, I have to go, but I hope my suggestions do help :)
-- [02:16] <terminal> {AS}: yes, thanks a lot, I  really like the idea of erasure, and I probably should remove SmallestElem to reduce proof size
import Data.Vect
import Data.Vect.Views

data Total : {a : Type} -> (a -> a -> Type) -> (x : a) -> (y : a) -> Type where
  LR : x `order` y -> Total order x y
  RL : y `order` x -> Total order x y

interface TotalOrder a (order : a -> a -> Type) | order where
  orderRefl : x `order` x
  orderTrans : x `order` y -> y `order` z -> x `order` z
  orderAntiSym : x `order` y -> y `order` x -> x = y
  orderTotal : (x : a) -> (y : a) -> Total {a} order x y

TotalOrder Nat LTE where
  orderRefl = lteRefl
  orderTrans = lteTransitive

  orderAntiSym LTEZero LTEZero = Refl
  orderAntiSym (LTESucc p) (LTESucc q) = rewrite orderAntiSym p q in Refl

  orderTotal Z _ = LR LTEZero
  orderTotal _ Z = RL LTEZero
  orderTotal (S n) (S m) with (orderTotal {order=LTE} n m)
    orderTotal (S n) (S m) | (LR p) = LR (LTESucc p)
    orderTotal (S n) (S m) | (RL p) = RL (LTESucc p)

mutual
  data IsSorted : (xs : Vect n Nat) -> Type where
      IsSortedZero  : IsSorted Nil
      IsSortedOne   : (x : Nat) -> IsSorted (x :: Nil)
      IsSortedMerge : (x : Nat) ->
                      IsSorted (x :: xs) -> IsSorted (y :: ys) ->
                      IsSorted zs -> LTE x y -> ListSum xs (y :: ys) zs ->
                      IsSorted (x :: zs)

  data ListSum : (xs : Vect n Nat) -> (ys : Vect m Nat) -> (zs : Vect c Nat) -> Type where
       ZeroSum : ListSum [] [] []
       ZeroRight : (right : Vect n Nat) -> ListSum [] right right
       ZeroLeft : (left : Vect n Nat) -> ListSum left [] left
       SumLeft : (x : Nat) -> ListSum xs ys zs -> ListSum (x :: xs) ys (x :: zs)
       SumRight : (y : Nat) -> ListSum xs ys zs -> ListSum xs (y :: ys) (y :: zs)
       SumCommutative : ListSum xs ys zs -> ListSum ys xs zs

tailSorted : IsSorted (x :: xs) -> IsSorted xs
tailSorted (IsSortedOne x) = IsSortedZero
tailSorted (IsSortedMerge _ x z w s t) = w

makeStepProof : (x : Nat) -> IsSorted (x :: xs)
                -> IsSorted (y :: ys) -> IsSorted zs
                -> LTE x y -> ListSum xs (y :: ys) zs -> IsSorted (x :: zs)
makeStepProof x prfXs prfYs prfZs prfLte prfSum =
  IsSortedMerge x prfXs prfYs prfZs prfLte prfSum

merge : {n : Nat} -> {c : Nat} ->
            (xs : Vect n Nat) -> (ys : Vect c Nat) ->
            IsSorted xs -> IsSorted ys ->
            Subset (Vect (n + c) Nat) (\zs => (IsSorted zs, ListSum xs ys zs))
merge [] [] x y = Element [] (IsSortedZero, ZeroSum)
merge [] ys x y = Element ys (y, ZeroRight ys)
merge {n} xs [] x y = rewrite (plusZeroRightNeutral n) in Element xs (x, ZeroLeft xs)
merge {n = S k} {c = S k1} (x :: xs) (y :: ys) prfX prfY = case orderTotal {order = LTE} x y of
  (LR prf) => let pairProof = merge xs (y :: ys) (tailSorted prfX) prfY in
              let (sortPrf, sumPrf) = getProof pairProof in
              let stepPrf = makeStepProof x prfX prfY sortPrf prf sumPrf in
                Element (x :: (getWitness pairProof)) (stepPrf, SumLeft x sumPrf)
  (RL prf) => rewrite sym (plusSuccRightSucc k k1) in
              let pairProof = merge (x :: xs) ys prfX (tailSorted prfY) in
              let (sortPrf, sumPrf) = getProof pairProof in
              let stepPrf = makeStepProof y prfY prfX sortPrf prf (SumCommutative sumPrf) in
                  Element (y :: (getWitness pairProof)) (stepPrf, SumRight y sumPrf)

mergeSort : Vect n Nat ->Subset (Vect n Nat) (\zs => IsSorted zs)
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = Element [] IsSortedZero
  mergeSort [x] | SplitRecOne = Element [x] (IsSortedOne x)
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec) =
    let leftPrf = (mergeSort ys | lrec) in
    let rightPrf = (mergeSort zs | rrec) in
    let xs = getWitness leftPrf in
    let xsPrf = getProof leftPrf in
    let ys = getWitness rightPrf in
    let ysPrf = getProof rightPrf in
    let resultPrf = merge xs ys xsPrf ysPrf in
    let (sortPrf, sumPrf) = getProof resultPrf in
        Element (getWitness resultPrf) sortPrf

main : IO ()
main with (mergeSort([3, 1, 3, 2]))
  main | (Element x pf) = putStrLn (show x)
