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

data Obj a = Obj { _geom  :: Geom
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
  where ips = (i, p) : (additionalProps (i, p))

addPropertyAlone' :: (Id, Property a) -> System a -> System a
addPropertyAlone' (i, p) = over (objs.(ix i).props) (:|> p)

addPropertyGeom :: Id -> PropertyG Geom a -> System a -> System a
addPropertyGeom i (Relation pt g _) s = (addProperty i p') s'
  where p'  = mkRel pt (s ^. nextId)
        s'  = insert g s

insertWithProps :: Geom -> [Property a] -> System a -> System a
insertWithProps g ps s = ((compose $ addProperty i <$> ps).(insert g)) s
  where i = s ^. nextId

-- Insertion Helper Methods --

compose :: [a -> a] -> a -> a
compose = foldr (.) id

lookupProperty :: PType -> Obj a -> Seq (Property a)
lookupProperty pt o = S.filter ((==pt).ptype) $ S.filter inconcrete $ view props o

insertSegBetween :: Id -> Id -> System a -> System a
insertSegBetween a b s = ((addProperty i $ mkRel Endpoint a).(addProperty i $ mkRel Endpoint b).(insert Segment)) s
  where i = s ^. nextId

insertPointBetween :: Id -> Id -> System a -> System a
insertPointBetween a b s = ((addProperty a $ mkRel Endpoint i).(addProperty b $ mkRel Endpoint i).(insert Point)) s
  where i = s ^. nextId

insertPolygon :: Int -> System a -> System a
insertPolygon n s = compose ((uncurry insertPointBetween) <$> lins) $ s'
  where i    = s ^. nextId
        s'   = (compose.(replicate n)) (addPropertyGeom i (mkRel Bounded Line)) $ (insert Polygon) s
        lins = zip [(i+1)..(i+n)] ((i+n) : [(i+1)..(i+n-1)])

-- Matching --

type Mapping = HM.HashMap Id Id
type State a = (System a, System a, Mapping, [Id])

systemMatch :: System a -> System a -> [Mapping]
systemMatch a b = (catMaybes . concat . Tree.levels) tree
  where tree = Tree.unfoldTree expand (a, b, HM.empty, [0..((a ^. nextId) - 1)])

expand :: State a -> (Maybe Mapping, [State a])
expand (a, b, m, (u:us))
  | HM.member u m = let lobj = (b ^. objs) `S.index` (m HM.! u) in
                    (Nothing, (\m -> (a, b, m, us)) <$> (catMaybes $ connectWhile linked m <$> objectMatch uobj lobj))
  | otherwise     = (Nothing, (\m -> (a, b, m, us)) <$> maps)
  where uobj = (toList $ a ^. objs) !! u
        maps = (concat.toList) $ (catMaybes.(fmap $ connectWhile linked m).(objectMatch uobj)) <$> (b ^. objs)
expand (_, _, m, []) = (Just m, [])

linked :: Mapping -> Id -> Id -> Bool
linked m a b = not $ ((HM.member a m) && ((m HM.! a) /= b))

linkedHarsh :: Mapping -> Id -> Id -> Bool
linkedHarsh m a b = not $ ((HM.member a m) && ((m HM.! a) /= b)) || ((not $ HM.member a m) && (elem b (HM.elems m)))

connectWhile :: (Mapping -> Id -> Id -> Bool) -> Mapping -> Mapping -> Maybe Mapping
connectWhile f a b = if go (HM.toList a) b then Just (mappend a b) else Nothing
  where go ((x, y):a) b = (f b x y) && (go a b)
        go _ b = True

objectMatch :: Obj a -> Obj a -> [Mapping]
objectMatch a b
  | a ^. geom /= b ^. geom = []
  | otherwise = HM.insert (a ^. ident) (b ^. ident) <$> (match (toList $ a ^. props) (toList $ b ^. props) HM.empty)
  where match (x:xs) b m
          | isImplication $ ptype x = match xs b m
          | otherwise = concat $ match xs b <$> (catMaybes $ ((>>= connectWhile linkedHarsh m).(propertyMatch x)) <$> b)
        match _ b m = [m]

propertyMatch :: Property a -> Property a -> Maybe Mapping
propertyMatch (Relation r i (as, bs)) (Relation s j (cs, ds)) = if predicate then Just result else Nothing
  where predicate = (r == s) && (length as == length cs) && (length bs == length ds)
        result    = HM.fromList $ zip (i : as ++ bs) (j : cs ++ ds)
