{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE UndecidableInstances #-}

module VRDT.TwoPMap where

instance (Ord k, Ord (Operation v), VRDT v) => VRDT (TwoPMap k v) where
  type Operation (TwoPMap k v) = TwoPMapOp k v
  apply x op = applyTwoPMap x op
  compatible x y = compatibleTwoPMap x y
  compatibleState x y = compatibleStateTwoPMap x y
  lawCommutativity x op1 op2 = VRDT.TwoPMap.Types.lawCommutativity x op1 op2
  lawCompatibilityCommutativity op1 op2 = ()

-- {-@ ple lawNonCausal @-}
-- {-@ lawNonCausal :: (Ord k, VRDT v) => x : TwoPMap k v -> {op1 : TwoPMapOp k v | enabledTwoPMap x op1} -> {op2 : TwoPMapOp k v | enabledTwoPMap x op2} -> {enabledTwoPMap (applyTwoPMap x op1) op2 <=> enabledTwoPMap (applyTwoPMap x op2) op1} @-}
-- lawNonCausal :: (Ord k, VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
-- lawNonCausal x (TwoPMapDelete k) op2 = ()
-- lawNonCausal x op1 op2 = ()

--{-@ ple lawCompatTwoPMap @-}
--{-@ lawCompatTwoPMap :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2) => } @-}

{-@ ple lawCommutativity @-}
{-@ lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)  => ((applyTwoPMap (applyTwoPMap x op1) op2 == applyTwoPMap (applyTwoPMap x op2) op1) && compatibleStateTwoPMap (applyTwoPMap x op1) op2)} @-}
lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()

-- incompatible (obvious)

-- ok
-- lawCommutativity x op1 op2
--   | not (compatibleTwoPMap op1 op2) || not (compatibleStateTwoPMap x op2) || not (compatibleStateTwoPMap x op1)
--   = ()


-- insert/any incompatible

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2
--   | compatibleStateTwoPMap x op1
--   , isJust (Map.lookup k m)
--   = ()

--ok
-- lawCommutativity x@(TwoPMap m p t) op1 op2@(TwoPMapInsert k' v')
--   | compatibleStateTwoPMap x op2
--   , isJust (Map.lookup k' m)
--   = ()

-- delete/delete

-- ok
-- lawCommutativity (TwoPMap m p t) (TwoPMapDelete k) (TwoPMapDelete k') =
--     lemmaDelete k k' m
--   ? lemmaDelete k k' p
--   ? (Set.insert k' (Set.insert k t) === Set.insert k (Set.insert k' t))

-- apply/any apply in tombstone

-- ok
-- lawCommutativity x@(TwoPMap m p t) (TwoPMapApply k op) op2
--   | Set.member k t
--   = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) `cast` ()



-- apply/apply, k == k'


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Just vv <- Map.lookup k m
--   = let vv_vop = apply vv vop
--         vv_vop' = apply vv vop' in
--       VRDT.Class.lawCommutativity vv vop vop' `cast`
--       lemmaInsertTwice k (apply vv_vop vop') vv_vop m `cast`
--       lemmaInsertTwice k (apply vv_vop' vop) vv_vop' m `cast`
--       lemmaLookupInsert m k vv_vop `cast`
--       lemmaLookupInsert m k vv_vop' `cast`
--       ()


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   = lemmaInsertPendingTwice k vop vop' p

-- apply/apply, k /= k'
-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   , Nothing <- Map.lookup k' m
--   = lemmaInsert k l0 k' l1 p
--   ? lemmaLookupInsert2 p k k' l1
--   ? lemmaLookupInsert2 p k' k l0
--   where l0 = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops
--         l1 = case Map.lookup k' p of
--                Nothing -> [vop']
--                Just ops -> insertList vop' ops

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   , Just v2 <- Map.lookup k' m
--   = lemmaInsert k (apply v1 vop) k' (apply v2 vop') m
--   ? lemmaLookupInsert2 m k k' (apply v2 vop')
--   ? lemmaLookupInsert2 m k' k (apply v1 vop)


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   , Nothing <- Map.lookup k' m
--   = lemmaLookupInsert2 m k' k (apply v1 vop)


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   , Just v2 <- Map.lookup k' m
--   = lemmaLookupInsert2 m k k' (apply v2 vop')



-- delete/apply tombstone
-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | Set.member k t
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (Set.member k (Set.insert k' t))

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | Set.member k t
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert ((Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert ( (Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

--ok
-- lawCommutativity x@(TwoPMap m p t)  op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop)
--   | (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Nothing <- Map.lookup k m
--   = lemmaDeleteInsert k l p
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap m (Map.insert k l p) t) op2
--     ==. (TwoPMap (Map.delete k m) (Map.delete k (Map.insert k l p)) (Set.insert k t)) 

--     ==. applyTwoPMap (TwoPMap m (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED)
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops  

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k')  op1@(TwoPMapApply k vop)
--   | Set.member k t
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap (Map.insert k (apply v1 vop) m) p t) op2
--     ==. (TwoPMap (Map.delete k (Map.insert k (apply v1 vop) m)) (Map.delete k p) (Set.insert k t))
--     -- ==. (TwoPMap m (Map.delete k p) (Set.insert k t))

--     ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED) &&&
--     (   compatibleStateTwoPMap (applyTwoPMap x op2) op1
--     ==. compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) (TwoPMapApply k vop)
--     *** QED )

-- apply/delete k/=k'

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (not (Set.member k (Set.insert k' t)))

-- flipped/ok 
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (not (Set.member k (Set.insert k' t)))



-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert (not (Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert (not (Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops



-- apply/delete k==k'

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   = lemmaDeleteInsert k l p
--   ? assert (Set.member k (Set.insert k' t))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t)  op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop)
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Nothing <- Map.lookup k m
--   = lemmaDeleteInsert k l p
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap m (Map.insert k l p) t) op2
--     ==. (TwoPMap (Map.delete k m) (Map.delete k (Map.insert k l p)) (Set.insert k t)) 

--     ==. applyTwoPMap (TwoPMap m (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED)
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops  

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? assert (Set.member k (Set.insert k' t))

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k')  op1@(TwoPMapApply k vop)
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap (Map.insert k (apply v1 vop) m) p t) op2
--     ==. (TwoPMap (Map.delete k (Map.insert k (apply v1 vop) m)) (Map.delete k p) (Set.insert k t))
--     -- ==. (TwoPMap m (Map.delete k p) (Set.insert k t))

--     ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED) &&&
--     (   compatibleStateTwoPMap (applyTwoPMap x op2) op1
--     ==. compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) (TwoPMapApply k vop)
--     *** QED )

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2
--   | Set.member k t
--   = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) `cast` ()

-- delete/insert tombstone

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | (Set.member k t)
--   , k == k'
--   , Nothing <- Map.lookup k p
--   = lemmaDeleteInsert k v' m
--   ? lemmaDeleteTwice k p
--   ? lemmaDeleteTwice k m
--   &&& lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2
--    ==. applyTwoPMap (TwoPMap (Map.insert k v' m) p t) op2
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) (Map.delete k p) (Set.insert k t)
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) p (Set.insert k t)
--    ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--    ==. applyTwoPMap (applyTwoPMap x op2) op1
--    *** QED)
--   &&& (compatibleStateTwoPMap (applyTwoPMap x op2) op1
--   === compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--   *** QED)
--   where v' = maybe v (foldr (flip apply) v) Nothing


-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | (Set.member k t)
--   , k == k'
--   , Just xx <- Map.lookup k p
--   = ()
--   ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
--   ? Map.delete k m


-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | Set.member k t
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , compatibleStateTwoPMap x op1
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v) 
--   | (Set.member k t)
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))



-- insert/delete k==k'

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , Nothing <- Map.lookup k p
--   = lemmaDeleteInsert k v' m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   where v' = maybe v (foldr (flip apply) v) Nothing


-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , k == k'
--   , Nothing <- Map.lookup k p
--   = lemmaDeleteInsert k v' m
--   ? lemmaDeleteTwice k p
--   ? lemmaDeleteTwice k m
--   &&& lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2
--    ==. applyTwoPMap (TwoPMap (Map.insert k v' m) p t) op2
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) (Map.delete k p) (Set.insert k t)
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) p (Set.insert k t)
--    ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--    ==. applyTwoPMap (applyTwoPMap x op2) op1
--    *** QED)
--   &&& (compatibleStateTwoPMap (applyTwoPMap x op2) op1
--   === compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--   *** QED)
--   where v' = maybe v (foldr (flip apply) v) Nothing

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , Just xx <- Map.lookup k p
--   = ()
--   ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , k == k'
--   , Just xx <- Map.lookup k p
--   = ()
--   ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
--   ? Map.delete k m



-- insert/delete k/=k'


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
--   &&& lemmaDelete k k' p
--   &&& assert (not (Set.member k (Set.insert k' t)))

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , compatibleStateTwoPMap x op1
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))



-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
--   &&& lemmaDelete k k' p
--   &&& assert (not (Set.member k (Set.insert k' t)))

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v) 
--   | not (Set.member k t)
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))


-- insert/insert

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , Nothing <- Map.lookup k p
--   , Nothing <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = maybe v' (foldr (flip apply) v') Nothing in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))
    
-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , Just vv1 <- Map.lookup k p
--   , Just vv2 <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
--           v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , Just vv1 <- Map.lookup k p
--   , Nothing <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
--           v2 = maybe v' (foldr (flip apply) v') Nothing in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k p
--   , Just vv2 <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))

-- insert/apply

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops 
--           -- Nothing = Map.lookup k (Map.insert k' l2 p)
--           -- Nothing = Map.lookup k' (Map.insert k v1 m) 
--     in
--         (   applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)
--         *** QED
--         )
--         &&& lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapApply k' vop') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops 
--           -- Nothing = Map.lookup k (Map.insert k' l2 p)
--           -- Nothing = Map.lookup k' (Map.insert k v1 m) 
--     in
--         (   applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)
--         *** QED
--         )
--         &&& lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops  in
--             lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )


-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapApply k' vop') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops  in
--             lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m

--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )


-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapApply k' vop')  op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m

--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )
--         ?  (not (Map.member k m))
--         ?  (not (Map.member k (Map.insert k' v2 m)))

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m
--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t)  op2@(TwoPMapApply k' vop') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m
--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )
--         ?  (not (Map.member k m))
--         ?  (not (Map.member k (Map.insert k' v2 m)))

lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
  | not (Set.member k t)
  , not (Set.member k' t)
  , compatibleTwoPMap op1 op2
  , compatibleStateTwoPMap x op1
  , k == k'
  , Nothing <- Map.lookup k p
  =  ( Map.lookup k m === Nothing *** QED) 
   
  ? lemmaNotMemberLookupNothing k m

   &&&( let v1 = maybe v (foldr (flip apply) v) Nothing
          -- Just vv = Map.lookup k (Map.insert k v1 m)
            -- Just vvv = Map.lookup k  (Map.insert k [vop'] p)
            l2 = case Map.lookup k p of
                   Nothing -> [vop']
                   Just ops -> insertList vop' ops  in
           (maybe v (foldr (flip apply) v) (Just [vop'])
        ==.  foldr (flip apply) v [vop']
        ==.  (flip apply) vop' (foldr (flip apply) v [])
        ==.  (flip apply) vop' v
        ==.  apply v vop'
        ***  QED  )
        -- -- &&& lemmaLookupInsert2 p k k' l2
        -- -- &&& lemmaLookupDelete2 p k' k
        -- -- &&& lemmaInsert k v1 k' v2 m
        -- -- &&& lemmaInsertDelete k' l2 k p
        &&& (l2 ==. [vop']  *** QED)
        &&& (Map.lookup k (Map.insert k [vop'] p) ==. Just [vop'] *** QED)
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
            ? lemmaLookupInsert m k v1
            ? lemmaLookupInsert p k l2
            ? (Map.lookup k m ==. Nothing *** QED)
            ? lemmaDeleteInsert k [vop'] p
            ? lemmaInsertTwice k (apply v1 vop') v1 m
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k vop')
        ==.  TwoPMap (Map.insert k (apply v1 vop') (Map.insert k v1 m)) p t
            ? ((Map.insert k (apply v1 vop') (Map.insert k v1 m)) ==. Map.insert k (apply v1 vop')  m *** QED)
        ==.  TwoPMap (Map.insert k (apply v1 vop') m) p t
              ? assert (not (Map.member k p))
            ? (Map.delete k p ==. p *** QED)
        ==.  TwoPMap (Map.insert k (apply v1 vop') m) (Map.delete k p) t
        -- ==.  TwoPMap (Map.insert k v1 m) p  t
        === TwoPMap (Map.insert k (apply v1 vop') m) -- here
              (Map.delete k p) t
        ==.  TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) (Just [vop'])) m)
              (Map.delete k (Map.insert k [vop'] p)) t
        ===  applyTwoPMap (TwoPMap m (Map.insert k [vop'] p) t) op1 -- here
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        ) -- &&&
        -- ( applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2 === applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1 *** QED)
      ) 



-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , k == k'
--   , Nothing <- Map.lookup k p
--   , Just vv <- Map.lookup k m
--   =  assert (not (isJust (Map.lookup k m))) -- let v1 = maybe v (foldr (flip apply) v) Nothing
      --     -- Just vv = Map.lookup k (Map.insert k v1 m)
      --     Just vvv = Map.lookup k  (Map.insert k [vop'] p)
      --     l2 = case Map.lookup k p of
      --            Nothing -> [vop']
      --            Just ops -> insertList vop' ops
      --     v2 = apply vv vop' in
      --       lemmaLookupInsert m k v1
      --   &&& lemmaLookupInsert p k l2
      --   &&& lemmaDeleteInsert k [vop'] p
      --   &&& lemmaInsertTwice k (apply v1 vop') v1 m
      --   &&& (maybe v (foldr (flip apply) v) (Just [vop'])
      --   ==.  foldr (flip apply) v [vop']
      --   ==.  (flip apply) vop' (foldr (flip apply) v [])
      --   ==.  (flip apply) vop' v
      --   ==.  apply v vop'
      --   ***  QED  )
      --   -- &&& lemmaLookupInsert2 p k k' l2
      --   -- &&& lemmaLookupDelete2 p k' k
      --   -- &&& lemmaInsert k v1 k' v2 m
      --   -- &&& lemmaInsertDelete k' l2 k p
      --   &&& (l2 ==. [vop'] ==. vvv *** QED)
      --   &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
      --   ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
      --   ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
      --   ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k vop')
      --   ==.  TwoPMap (Map.insert k (apply v1 vop') (Map.insert k v1 m)) p t
      --   -- ==.  TwoPMap (Map.insert k v1 m) p  t
      --   ==. TwoPMap (Map.insert k (apply v1 vop') m)
      --         (Map.delete k p) t
      --   ==.  TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) Nothing) m)
      --         p t
      --   ==.  applyTwoPMap (TwoPMap (Map.insert k v2 m) p t) op1
      --   ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
      --   *** QED
      --   )

lawCommutativity _ _ _
  = undefined

-- upgraded version
  -- ?  (m0' === m1')
  -- ?  (p0' === p1')
  -- ?  (t0' === t1')
  -- where TwoPMap m0 p0 t0 = applyTwoPMap x op1
  --       TwoPMap m1 p1 t1 = applyTwoPMap x op2
  --       TwoPMap m0' p0' t0' = applyTwoPMap (applyTwoPMap x op1) op2
  --       TwoPMap m1' p1' t1' = applyTwoPMap (applyTwoPMap x op2) op1

-- copy paste the following when needed
        -- TwoPMap m0 p0 t0 = applyTwoPMap x op1
        -- TwoPMap m1 p1 t1 = applyTwoPMap x op2
        -- TwoPMap m0' p0' t0' = applyTwoPMap (applyTwoPMap x op1) op2
        -- TwoPMap m1' p1' t1' = applyTwoPMap (applyTwoPMap x op2) op1


