module FingerTrees where

data FingerTree a = Empty
                  | Single a
                  | Deep (Digit a) (FingerTree (Node a)) (Digit a)

{-data Digit a = One a | Two a a | Three a a a | Four a a a a-}
type Digit a = [a]
data Node a = Node2 a a | Node3 a a a

class Reduce f where
  reducer :: (a -> b -> b) -> (f a -> b -> b)
  reducel :: (b -> a -> b) -> (b -> f a -> b)

instance Reduce [] where
  reducer (-<) x z = foldr (-<) z x
  reducel (>-) x z = foldl (>-) x z

toList :: (Reduce f) => f a -> [a]
{-
  toList s = s :' [] where (:') = reducer (:)
-}
toList s = s `conser` [] where conser = reducer (:)

data Tree a = Zero a | Succ (Tree (Node a))

instance Reduce Node where
  reducer (-<) (Node2 a b) z = a -< (b -< z)
  reducer (-<) (Node3 a b c) z = a -< (b -< (c -< z))
  reducel (>-) z (Node2 a b) = (z >- b) >- a
  reducel (>-) z (Node3 a b c) = ((z >- c) >- b) >- a

instance Reduce FingerTree where
  reducer (-<) Empty z = z
  reducer (-<) (Single x) z = x -< z
  reducer (-<) (Deep pr m sf) z = pr -<^ (m -<^^ (sf -<^ z))
    where (-<^) = reducer (-<)
          (-<^^) = reducer (reducer (-<))
  reducel (>-) z Empty = z
  reducel (>-) z (Single x) = z >- x
  reducel (>-) z (Deep pr m sf) = ((z >-^ pr) >-^^ m) >-^ sf
    where (>-^) = reducel (>-)
          (>-^^) = reducel (reducel (>-))
  {- This is how it was originally presented, but `-<'` isn't valid:
  reducer (-<) (Deep pr m sf) z = pr `reducer'` (m `reducer''` (sf `reducer'` z))
    where reducer' = reducer (-<)
          reducer'' = reducer (reducer (-<))
  -}
  {-
    Valid ASCII symbols in Haskell operators:
    !#$%&*+./<=>?@\^|-~
  -}

infixr 5 <|
(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty = Single a
a <| Single b = Deep [a] Empty [b]
a <| Deep [b, c, d, e] m sf = Deep [a, b] (Node3 c d e <| m) sf
a <| Deep pr m sf = Deep ([a] ++ pr) m sf

infixl 5 |>
(|>) :: FingerTree a -> a -> FingerTree a
Empty |> a = Single a
Single b |> a = Deep [b] Empty [a]
Deep pr m [e, d, c, b] |> a = Deep pr (m |> Node3 e d c) [b, a]
Deep pr m sf |> a = Deep pr m (sf ++ [a])

(<|^) :: (Reduce f) => f a -> FingerTree a -> FingerTree a
(<|^) = reducer (<|)
(|>^) :: (Reduce f) => FingerTree a -> f a -> FingerTree a
(|>^) = reducel (|>)

toTree :: (Reduce f) => f a -> FingerTree a
toTree s = s <|^ Empty

data ViewL s a = NilL | ConsL a (s a)

viewL :: FingerTree a -> ViewL FingerTree a
viewL Empty = NilL
viewL (Single x) = ConsL x Empty
viewL (Deep pr m sf) = ConsL (head pr) (deepL (tail pr) m sf)

deepL :: [a] -> FingerTree (Node a) -> Digit a -> FingerTree a
deepL [] m sf = case viewL m of
                  NilL -> toTree sf
                  ConsL a m' -> Deep (toList a) m' sf
deepL pr m sf = Deep pr m sf

-- DeepR and ViewR "exercise for the reader" (argh)
data ViewR s a = NilR | ConsR (s a) a
viewR :: FingerTree a -> ViewR FingerTree a
viewR Empty = NilR
viewR (Single x) = ConsR Empty x
viewR (Deep pr m sf) = ConsR (deepR pr m (init sf)) (last sf)

deepR :: Digit a -> FingerTree (Node a) -> [a] -> FingerTree a
deepR pr m [] = case viewR m of
                  NilR -> toTree pr
                  ConsR m' a -> Deep pr m' (toList a)
deepR pr m sf = Deep pr m sf

{-
-- viewR (Deep pr m sf) = ConsR (head pr) (deepL (tail pr) m sf)
viewR (Deep pr m sf) = ConsR (head pr) (deepL (tail pr) m sf)
deepL :: [a] -> FingerTree (Node a) -> Digit a -> FingerTree a
deepL [] m sf = case viewL m of
                  NilL -> toTree sf
                  ConsL a m' -> Deep (toList a) m' sf
deepL pr m sf = Deep pr m sf
-}

isEmpty :: FingerTree a -> Bool
isEmpty x = case viewL x of
              NilL -> True
              ConsL _ _ -> False

headL :: FingerTree a -> a
headL x = case viewL x of ConsL a _ -> a
tailL :: FingerTree a -> FingerTree a
tailL x = case viewL x of ConsL _ x' -> x'
headR :: FingerTree a -> a
headR x = case viewR x of ConsR _ a -> a
tailR :: FingerTree a -> FingerTree a
tailR x = case viewR x of ConsR x' _ -> x'

app3 :: FingerTree a -> [a] -> FingerTree a -> FingerTree a
app3 Empty ts xs = ts <|^ xs
app3 xs ts Empty = xs |>^ ts
app3 (Single x) ts xs = x <| (ts <|^ xs)
app3 xs ts (Single x) = (xs |>^ ts) |> x
app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) =
  Deep pr1 (app3 m1 (nodes (sf1 ++ ts ++ pr2)) m2) sf2

nodes :: [a] -> [Node a]
nodes [a, b] = [Node2 a b]
nodes [a, b, c] = [Node3 a b c]
nodes [a, b, c, d] = [Node2 a b, Node2 c d]
nodes (a:b:c:xs) = Node3 a b c : nodes xs

(|><|) :: FingerTree a -> FingerTree a -> FingerTree a
xs |><| ys = app3 xs [] ys
