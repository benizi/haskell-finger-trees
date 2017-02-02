{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

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

class (Monoid v) => Measured a v where
  {-||.|| :: a -> v-}
  measure :: a -> v

data NodeM v a = NodeM2 v a a | NodeM3 v a a a

node2 :: (Measured a v) => a -> a -> NodeM v a
node2 a b = NodeM2 ((measure a) `mappend` (measure b)) a b
node3 :: (Measured a v) => a -> a -> a -> NodeM v a
node3 a b c = NodeM3 ((measure a) `mappend` (measure b) `mappend` (measure c)) a b c

nodesM :: (Measured a v) => [a] -> [NodeM v a]
nodesM [a, b] = [node2 a b]
nodesM [a, b, c] = [node3 a b c]
nodesM [a, b, c, d] = [node2 a b, node2 c d]
nodesM (a:b:c:xs) = node3 a b c : nodesM xs

app3M :: (Measured a v) =>
  FingerTreeM v a -> [a] -> FingerTreeM v a -> FingerTreeM v a
app3M EmptyM ts xs = ts <||^ xs
app3M xs ts EmptyM = xs ||>^ ts
app3M (SingleM x) ts xs = x <|| (ts <||^ xs)
app3M xs ts (SingleM x) = (xs ||>^ ts) ||> x
app3M (DeepM _ pr1 m1 sf1) ts (DeepM _ pr2 m2 sf2) =
  deepM pr1 (app3M m1 (nodesM (sf1 ++ ts ++ pr2)) m2) sf2

instance (Monoid v) => Measured (NodeM v a) v where
  measure (NodeM2 v _ _) = v
  measure (NodeM3 v _ _ _) = v

instance (Measured a v) => Measured (Digit a) v where
  measure xs = reducel (\i a -> mappend i (measure a)) mempty xs

data FingerTreeM v a = EmptyM
                     | SingleM a
                     | DeepM v (Digit a) (FingerTreeM v (NodeM v a)) (Digit a)

deepM :: (Measured a v) =>
  Digit a -> FingerTreeM v (NodeM v a) -> Digit a -> FingerTreeM v a
deepM pr m sf = DeepM annotation pr m sf
  where annotation = (measure pr) `mappend` (measure m) `mappend` (measure sf)

instance (Measured a v) => Measured (FingerTreeM v a) v where
  measure EmptyM = mempty
  measure (SingleM x) = measure x
  measure (DeepM v _ _ _) = v

instance Reduce (NodeM a) where
  reducer f (NodeM2 _ a b) z = f a $ f b z
  reducer f (NodeM3 _ a b c) z = f a $ f b $ f c z
  reducel f z (NodeM2 _ a b) = f (f z b) a
  reducel f z (NodeM3 _ a b c) = f (f (f z c) b) a

instance Reduce (FingerTreeM a) where
  reducer f EmptyM z = z
  reducer f (SingleM x) z = f x z
  reducer f (DeepM _ pr m sf) z = rf pr (rrf m (rf sf z))
    where rf = reducer f
          rrf = reducer (reducer f)
  reducel f z EmptyM = z
  reducel f z (SingleM x) = f z x
  reducel f z (DeepM _ pr m sf) = rf (rrf (rf z pr) m) sf
    where rf = reducel f
          rrf = reducel (reducel f)

infixr 5 <||
(<||) :: (Measured a v) => a -> FingerTreeM v a -> FingerTreeM v a
a <|| EmptyM = SingleM a
a <|| SingleM b = deepM [a] EmptyM [b]
a <|| DeepM _ [b, c, d, e] m sf = deepM [a, b] (node3 c d e <|| m) sf
a <|| DeepM _ pr m sf = deepM ([a] ++ pr) m sf

-- Handwavy stuff follows
infixl 5 ||>
(||>) :: (Measured a v) => FingerTreeM v a -> a -> FingerTreeM v a
EmptyM ||> a = SingleM a
SingleM b ||> a = deepM [b] EmptyM [a]
DeepM _ pr m [e, d, c, b] ||> a = deepM pr (m ||> node3 e d c) [b, a]
DeepM _ pr m sf ||> a = deepM pr m (sf ++ [a])

(<||^) :: (Measured a v, Reduce f) => f a -> FingerTreeM v a -> FingerTreeM v a
(<||^) = reducer (<||)
(||>^) :: (Measured a v, Reduce f) => FingerTreeM v a -> f a -> FingerTreeM v a
(||>^) = reducel (||>)

toListM :: (Reduce f) => f a -> [a]
toListM s = s `conser` [] where conser = reducer (:)

toTreeM :: (Measured a v, Reduce f) => f a -> FingerTreeM v a
toTreeM s = s <||^ EmptyM

data ViewLM s a = NilLM | ConsLM a (s a)

viewLM :: (Measured a v) => FingerTreeM v a -> ViewLM (FingerTreeM v) a
viewLM EmptyM = NilLM
viewLM (SingleM x) = ConsLM x EmptyM
viewLM (DeepM _ pr m sf) = ConsLM (head pr) (deepLM (tail pr) m sf)

deepLM :: (Measured a v) => [a] -> FingerTreeM v (NodeM v a) -> Digit a -> FingerTreeM v a
deepLM [] m sf = case viewLM m of
                   NilLM -> toTreeM sf
                   ConsLM a m' -> deepM (toListM a) m' sf
deepLM pr m sf = deepM pr m sf

data ViewRM s a = NilRM | ConsRM (s a) a
viewRM :: (Measured a v) => FingerTreeM v a -> ViewRM (FingerTreeM v) a
viewRM EmptyM = NilRM
viewRM (SingleM x) = ConsRM EmptyM x
viewRM (DeepM _ pr m sf) = ConsRM (deepRM pr m (init sf)) (last sf)

deepRM :: (Measured a v) =>
  Digit a -> FingerTreeM v (NodeM v a) -> [a] -> FingerTreeM v a
deepRM pr m [] = case viewRM m of
                   NilRM -> toTreeM pr
                   ConsRM m' a -> deepM pr m' (toListM a)
deepRM pr m sf = deepM pr m sf

isEmptyM :: (Measured a v) => FingerTreeM v a -> Bool
isEmptyM x = case viewLM x of
               NilLM -> True
               ConsLM _ _ -> False

headLM :: (Measured a v) => FingerTreeM v a -> a
headLM x = case viewLM x of ConsLM a _ -> a
tailLM :: (Measured a v) => FingerTreeM v a -> FingerTreeM v a
tailLM x = case viewLM x of ConsLM _ x' -> x'
headRM :: (Measured a v) => FingerTreeM v a -> a
headRM x = case viewRM x of ConsRM _ a -> a
tailRM :: (Measured a v) => FingerTreeM v a -> FingerTreeM v a
tailRM x = case viewRM x of ConsRM x' _ -> x'

data Split f a = Split (f a) a (f a)

splitDigit :: (Measured a v) => (v -> Bool) -> v -> Digit a -> Split [] a
splitDigit p i [a] = Split [] a []
splitDigit p i (a:as)
  | p i' = Split [] a as
  | otherwise = let Split l x r = splitDigit p i' as in Split (a:l) x r
  where i' = mappend i (measure a)

splitTree :: (Measured a v) =>
  (v -> Bool) -> v -> FingerTreeM v a -> Split (FingerTreeM v) a
splitTree p i (SingleM x) = Split EmptyM x EmptyM
splitTree p i (DeepM _ pr m sf)
  | p vpr = let Split l x r = splitDigit p i pr
             in Split (toTreeM l) x (deepLM r m sf)
  | p vm = let Split ml xs mr = splitTree p vpr m
               Split l x r = splitDigit p (mappend vpr (measure ml)) (toListM xs)
            in Split (deepRM pr ml l) x (deepLM r mr sf)
  | otherwise = let Split l x r = splitDigit p vm sf
                 in Split (deepRM pr m l) x (toTreeM r)
  where vpr = mappend i (measure pr)
        vm = mappend vpr (measure m)

split :: (Measured a v) =>
  (v -> Bool) -> FingerTreeM v a -> (FingerTreeM v a, FingerTreeM v a)
split p EmptyM = (EmptyM, EmptyM)
split p xs
  | p (measure xs) = (l, x <|| r)
  | otherwise = (xs, EmptyM)
  where Split l x r = splitTree p mempty xs

takeUntil, dropUntil :: (Measured a v) =>
  (v -> Bool) -> FingerTreeM v a -> FingerTreeM v a
takeUntil p = fst . split p
dropUntil p = snd . split p

newtype Size = Size { getSize :: Int }
  deriving (Eq, Ord)

instance Monoid Size where
  mempty = Size 0
  Size m `mappend` Size n = Size (m + n)

newtype Elem a = Elem { getElem :: a }

newtype Seq a = Seq (FingerTreeM Size (Elem a))

instance Measured (Elem a) Size where
  measure (Elem _) = Size 1

length :: Seq a -> Int
length (Seq xs) = getSize (measure xs)

splitAt :: Int -> Seq a -> (Seq a, Seq a)
splitAt i (Seq xs) = (Seq l, Seq r)
  where (l, r) = split (Size i <) xs

(!) :: Seq a -> Int -> a
Seq xs ! i = getElem x
  where Split _ x _ = splitTree (Size i <) (Size 0) xs

instance (Show v, Show a) => Show (NodeM v a) where
  show (NodeM2 _ a b) = "<" ++ (show a) ++ " " ++ (show b) ++ ">"
  show (NodeM3 _ a b c) = "<" ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c) ++ ">"

instance (Show a, Show v) => Show (FingerTreeM v a) where
  show EmptyM = ""
  show (SingleM a) = show a
  show (DeepM _ pr EmptyM sf) = "{(pr " ++ (show pr) ++ ") (m) (sf "++(show sf)++")}"
  show (DeepM _ pr m sf) = "{(pr " ++ (show pr) ++ ") (m "++(show m)++") (sf "++(show sf)++")}"

instance Show Size where
  show (Size i) = "|" ++ (show i) ++ "|"

instance (Show a) => Show (Elem a) where
  show (Elem x) = "\"" ++ (show x) ++ "\""

instance (Show a) => Show (Seq a) where
  showsPrec p (Seq s) = showParen (p >= 11) ((.) (showString "Seq ") (showsPrec 11 s))
  showList = showsPrec 0

main :: IO ()
main = do
  let s = (Seq $ app3M EmptyM (Elem <$> [1..100]) EmptyM) :: (Seq Int)
      Seq t = s
  putStrLn $ show t
