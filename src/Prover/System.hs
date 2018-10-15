{-# LANGUAGE TemplateHaskell #-}

module Prover.System where

import Prover.Property
import Control.Lens
import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Sequence as S
import Data.List (foldl, intercalate)
import Data.Sequence (Seq ( (:|>) ), empty)
import qualified Data.HashMap.Strict as HM
import qualified Data.Tree as Tree
import Data.Maybe (catMaybes)

data Obj a = Obj { _geom :: Geom
                 , _ident :: Id
                 , _props :: Seq (Property a) }
instance (Show a) => Show (Obj a) where
  show (Obj g i ps) = (show i) ++ ": " ++ (show g) ++ " " ++ (show $ toList ps)
makeLenses ''Obj

newObj :: Geom -> Id -> Obj a
newObj g i = Obj g i S.empty

data System a = System { _nextId :: Id
                       , _objs :: Seq (Obj a) }
instance (Show a) => Show (System a) where
  show (System i os) = intercalate "\n" (toList $ show <$> os)
makeLenses ''System

empty :: System a
empty = System 0 S.empty

insert :: Geom -> System a -> System a
insert g (System nid os) = System (nid + 1) (os :|> (newObj g nid))

addProperty :: Id -> Property a -> System a -> System a
addProperty i p s = foldr addPropertyAlone' s ips
  where ips = (i, p) : (requireds (i, p))

addPropertyAlone' :: (Id, Property a) -> System a -> System a
addPropertyAlone' (i, p) = over (objs.(ix i).props) (:|> p)

addPropertyGeom :: Id -> PropertyG Geom a -> System a -> System a
addPropertyGeom i p s = (addProperty i newp) news
  where geoms = references p
        newp  = replaceRefsEnum p (view nextId s)
        news  = foldl (flip insert) s geoms

insertWithProps :: Geom -> [Property a] -> System a -> System a
insertWithProps g ps s = ((compose $ addProperty i <$> ps).(insert g)) s
  where i = view nextId s

-- Insertion Helper Methods --

compose :: [a -> a] -> a -> a
compose = foldr (.) id

lookupProperty :: PType -> Obj a -> Seq (Property a)
lookupProperty pt o = S.filter ((==pt).ptypeOf) $ view props o

insertSegBetween :: Id -> Id -> System a -> System a
insertSegBetween a b s = ((addProperty i $ Endpoint a).(addProperty i $ Endpoint b).(insert Segment)) s
  where i = view nextId s

insertPointBetween :: Id -> Id -> System a -> System a
insertPointBetween a b s = ((addProperty a $ Endpoint i).(addProperty b $ Endpoint i).(insert Point)) s
  where i = view nextId s

insertPolygon :: Int -> System a -> System a
insertPolygon n s = compose ((uncurry insertPointBetween) <$> lins) $ s'
  where i    = view nextId s
        s'   = ((addPropertyGeom i $ Bounded $ replicate n Line).(insert Polygon)) s
        lins = zip [(i+1)..(i+n)] ((i+n) : [(i+1)..(i+n-1)])

-- Matching --

type Mapping = HM.HashMap Id Id
type State a = (System a, System a, Mapping, [Id])

systemMatch :: System a -> System a -> [Mapping]
systemMatch a b = (catMaybes . concat . Tree.levels) tree
  where tree = Tree.unfoldTree expand (a, b, HM.empty, [0..((a ^. nextId) - 1)])

expand :: State a -> (Maybe Mapping, [State a])
expand (a, b, m, (u:us))
  | HM.member u m = (Nothing, (\m -> (a, b, m, us)) <$> (objectMatch m uobj ((b ^. objs) `S.index` (m HM.! u))))
  | otherwise     = (Nothing, (\m -> (a, b, m, us)) <$> maps)
  where uobj = (toList $ a ^. objs) !! u
        maps = (concat.toList) $ (objectMatch m uobj) <$> (b ^. objs)
expand (_, _, m, []) = (Just m, [])

unmatched :: Mapping -> Id -> Id -> Bool
unmatched m a b = ((HM.member a m) && ((m HM.! a) /= b)) || ((not $ HM.member a m) && (elem b (HM.elems m)))

objectMatch :: Mapping -> Obj a -> Obj a -> [Mapping]
objectMatch m a b
  | a ^. geom /= b ^. geom = []
  | unmatched m (a ^. ident) (b ^. ident) = []
  | otherwise = (HM.insert (a ^. ident) (b ^. ident)) <$> (match (toList $ a ^. props) (toList $ b ^. props) m)
  where match (x:xs) b m = concat $ match xs b <$> (concat $ (propertyMatch m x) <$> b)
        match _ b m = [m]

propertyMatch' :: Property a -> Property a -> [Mapping]
propertyMatch' (Length a) (Length b) = [HM.fromList [(a, b)]]
propertyMatch' (Radius a) (Radius b) = [HM.fromList [(a, b)]]
propertyMatch' (Degree a) (Degree b) = [HM.fromList [(a, b)]]
propertyMatch' (Intersect a b) (Intersect c d) = [HM.fromList [(a, c), (b, d)]]
propertyMatch' (Equals a) (Equals b)      = [HM.fromList [(a, b)]]
propertyMatch' (Congruent a) (Congruent b)   = [HM.fromList [(a, b)]]
propertyMatch' (Contains a) (Contains b)   = [HM.fromList [(a, b)]]
propertyMatch' (Endpoint a) (Endpoint b)    = [HM.fromList [(a, b)]]
propertyMatch' (Bounded xs) (Bounded ys)    = if length xs /= length ys then [] else HM.fromList <$> (zip xs <$> opts)
  where opts = (take $ length ys) <$> ((flip drop $ cycle ys) <$> [1..length ys])
propertyMatch' _ _ = []

connectMapping :: Mapping -> Mapping -> Maybe Mapping
connectMapping a b = if go (HM.toList a) b then Just (mappend a b) else Nothing
  where go ((x, y):a) b = (not $ unmatched b x y) && (go a b)
        go _ b = True

propertyMatch :: Mapping -> Property a -> Property a -> [Mapping]
propertyMatch m a b = catMaybes $ (connectMapping m) <$> (propertyMatch' a b)

propertyMatch'' :: Mapping -> Property a -> Property a -> Maybe Mapping
propertyMatch'' m a b = if (ptypeOf a) /= (ptypeOf b) then Nothing else match m (references a) (references b)
  where match m (x:xs) (y:ys)
          | HM.member x m = if m HM.! x /= y then Nothing else match m xs ys
          | elem y (HM.elems m) = Nothing
          | otherwise = match (HM.insert x y m) xs ys
        match m _ _ = Just m

-- Testing --
b = insertPolygon 3 Prover.System.empty
c = insertPolygon 3 (insert Point Prover.System.empty)
