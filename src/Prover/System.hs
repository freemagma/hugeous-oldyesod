{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}

module Prover.System where

import Prover.Property
import Control.Lens
import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Sequence as S
import Data.List (foldl, intercalate)
import Data.Sequence (Seq ( (:|>) ), empty)
import qualified Data.HashMap.Strict as HM
import qualified Data.IntSet as I
import qualified Data.Tree as Tree
import qualified Data.Text as T
import Data.Maybe (catMaybes)
import Data.Bits (xor)
import Data.Hashable

-- Types and Typeclass Instances

type Name = T.Text

instance Hashable (Ref Id) where
  hashWithSalt salt None     = hashWithSalt salt salt
  hashWithSalt salt (Ref x)  = hashWithSalt salt x
  hashWithSalt salt (Cyc xs) = hashWithSalt salt ((0 :: Int), cycStandard xs)
  hashWithSalt salt (Ord xs) = hashWithSalt salt ((1 :: Int), xs)

data Obj a = Obj { _geom  :: Geom
                 , _ident :: Id
                 , _props :: Seq (Property a) }
makeLenses ''Obj
instance (Show a) => Show (Obj a) where
  show (Obj g i ps) = (show i) ++ ": " ++ (show g) ++ " " ++ (show $ toList ps)

data System a = System { _nextId :: Id
                       , _objs :: Seq (Obj a)
                       , _referencedBy :: HM.HashMap (Geom, Ref Id) Id
                       , _nameId :: HM.HashMap Name Id}
makeLenses ''System
instance (Show a) => Show (System a) where
  show s = intercalate "\n" (toList $ show <$> (s ^. objs))

-- Basic Methods --

newObj :: Geom -> Id -> Obj a
newObj g i = Obj g i S.empty

empty :: System a
empty = System 0 S.empty HM.empty HM.empty

insert :: Geom -> System a -> System a
insert g s = (nextId %~ (+1)) $ (objs %~ (:|> (newObj g $ s ^. nextId))) s

addProperty :: Id -> Property a -> System a -> System a
addProperty i p s = foldr addPropertyAlone' s ips
  where ips = (i, p) : (additionalProps (i, p))

addPropertyAlone' :: (Id, Property a) -> System a -> System a
addPropertyAlone' (i, p) = over (objs.(ix i).props) (:|> p)

addPropertyGeom :: Id -> PropertyG Geom a -> System a -> System a
addPropertyGeom i (Relation pt g _) s = (addProperty i p') s'
  where p'  = mkRel pt (s ^. nextId)
        s'  = (compose $ insert <$> toList g) s

insertWithProps :: Geom -> [Property a] -> System a -> System a
insertWithProps g ps s = ((compose $ addProperty i <$> ps).(insert g)) s
  where i = s ^. nextId

nameObj :: Id -> Name -> System a -> System a
nameObj i n = nameId %~ (HM.insert n i)

addReference :: Id -> Ref Id -> System a -> System a
addReference i r s = referencedBy %~ (HM.insert (s ^. (objs.(ix i).geom), r) i) $ s

-- Insertion Helper Methods --

compose :: [a -> a] -> a -> a
compose = foldr (.) id

lookupProperty :: PType -> Obj a -> Seq (Property a)
lookupProperty pt o = S.filter ((==pt).ptype) $ S.filter inconcrete $ view props o

insertSegBetween :: Id -> Id -> System a -> System a
insertSegBetween a b s = ((addProperty i $ mkRelR Bounded (Cyc [a, b])).(insert Segment)) s
  where i = s ^. nextId

insertPolygon :: Int -> System a -> System a
insertPolygon n s = ((compose $ (uncurry insertSegBetween) <$> tups).
                    (addProperty i $ mkRelR Bounded $ Cyc [(i+1)..(i+n)]).
                    (compose $ replicate n $ insert Point).
                    (insert Polygon)) s
  where i    = s ^. nextId
        tups = zip [(i+1)..(i+n)] ((i+n) : [(i+1)..(i+n-1)])


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
          | otherwise = concat $ fmap (match xs b) $ concat $ fmap (catMaybes.(fmap $ connectWhile linkedHarsh m).(propertyMatch x)) b
        match _ b m = [m]

propertyMatch :: Property a -> Property a -> [Mapping]
propertyMatch (Relation r i spa) (Relation s j spb) = if r /= s then [] else result
  where result = HM.union <$> (refMatch i j) <*> (specMatch spa spb)

specMatch :: Spec Id -> Spec Id -> [Mapping]
specMatch (Spec (Cyc a) (Cyc b)) (Spec (Cyc c) (Cyc d)) =
  if (length a == length c) && (length b == length d) then
  fmap (HM.fromList . (zip (c ++ d))) $ zipWith (++) (cycPermute a) (cycPermute b) else []
specMatch (Spec a b) (Spec c d) = HM.union <$> (refMatch a c) <*> (refMatch b d)

refMatch :: Ref Id -> Ref Id -> [Mapping]
refMatch None None = [HM.empty]
refMatch (Ref a) (Ref b) = [HM.singleton a b]
refMatch (Ord as) (Ord bs) =
  if length as == length bs then [HM.fromList $ zip as bs] else []
refMatch (Cyc as) (Cyc bs) =
  if length as == length bs then fmap (HM.fromList . (zip as)) $ cycPermute bs else []
refMatch _ _ = []
