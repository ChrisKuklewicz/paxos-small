{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- Synod basic protocol
module Paxos1 where

import Prelude hiding (maximum,foldr,all)
import Data.List(find,tails,nub,sort)
import Data.Set as Set hiding (toList,map,null)
import qualified Data.Set as Set(map,null)
import Data.Foldable(Foldable,toList,foldMap,maximum,foldr,all)
import Data.Function
import Data.Monoid

-- Express non-empty set in a way that is correct by construction
newtype NonEmptySet a = NES (a,Set a)
   deriving (Eq,Ord,Show)

mmax :: (Foldable t, Ord a, Monoid a) => t a -> a
mmax = foldr max mempty

-- Only introduce and eliminate NES with mkNES and nes
mkNES :: Set a -> Maybe (NonEmptySet a)
mkNES = fmap NES . minView

nes :: Ord a => NonEmptySet a -> Set a
nes (NES x) = uncurry Set.insert x

-- Types of things mentioned in the Paper

newtype BallotNumber = BallotNumber Integer deriving (Eq,Ord,Enum)
newtype Decree = Decree String deriving (Eq,Ord) -- should not be ""
newtype Priest = Priest String deriving (Eq,Ord) -- should not be ""

instance Show BallotNumber where show (BallotNumber n) = show n
instance Show Decree where show (Decree s) = s
instance Show Priest where show (Priest s) = s

instance Num BallotNumber where
  (+) = undefined; (*) = undefined; abs = undefined; signum = undefined
  fromInteger = BallotNumber

data Ballot = Ballot { bal :: BallotNumber
                     , dec :: Decree
                     , qrm :: NonEmptySet Priest
                     , vot :: Set Priest
                     }
  deriving (Show)

-- prop'ballots'1 asserts all ballots have a unique bal :: BallotNumber
-- Encode this in the Eq and Ord instance for Ballot, thus any (Set Ballot)
-- must obey prop'ballots'1 by construction.  I include 'flip' so that
-- toList produce the list in decreasing order of the Integer in BallotNumber
-- instead of ascending.
instance Eq Ballot where (==) = (==) `on` bal
instance Ord Ballot where compare = flip compare `on` bal

overlap b1 b2 = not . Set.null $ intersection b1 b2

prop'ballots'2 :: Set Ballot -> Bool
prop'ballots'2 bs = and [ overlap (nes $ qrm b1) (nes $ qrm b2) |
                          (b1:b2s) <- tails (toList bs)
                        , b2 <- b2s ]

prop'ballots'3 :: Set Ballot -> Bool
prop'ballots'3 = all valid . tails . toList where
  valid [] = True
  valid (b1:b2s) = maybe True (((==) `on` dec) b1) . find voted $ b2s
    where voted = overlap (nes $ qrm b1) . vot

priests = map Priest [ "A", "B", "Γ", "∆", "E" ]
alpha = Decree "α"
beta = Decree "β"

ballots = let mkB x y = let vs = (Set.fromList $ map Priest y)
                            Just qs = mkNES vs
                        in x qs vs
          in Set.fromList [ mkB (Ballot  2 alpha) [ "A", "B", "Γ", "∆"      ]
                          , mkB (Ballot  5 alpha) [ "A", "B", "Γ",      "E" ]
                          , mkB (Ballot 14 alpha) [      "B",      "∆", "E" ]
                          , mkB (Ballot 27 alpha) [ "A",      "Γ", "∆"      ]
                          , mkB (Ballot 29 alpha) [      "B", "Γ", "∆"      ]
                          ]

-- important: VNull is less than all (Vote _ _ _) in the derived Ord instance
data Vote = VNull | Vote BallotNumber Decree Priest deriving (Eq,Ord,Show)

instance Monoid Vote where
  mempty = VNull
  mappend VNull v = v
  mappend v _ = v

v'bal :: Vote -> Maybe BallotNumber
v'bal VNull = Nothing
v'bal (Vote b _ _) = Just b

v'dec :: Vote -> Maybe Decree
v'dec VNull = Nothing
v'dec (Vote _ d _) = Just d

v'pst :: Vote -> Maybe Priest
v'pst VNull = Nothing
v'pst (Vote _ _ p) = Just p

votes :: Set Ballot -> Set Vote
votes = foldMap ballotToVotes

ballotToVotes :: Ballot -> Set Vote
ballotToVotes b = Set.map (Vote (bal b) (dec b)) (vot b)

maxVote1 :: BallotNumber -> Priest -> Set Ballot -> Vote
maxVote1 n p = foldMap bToV where
  bToV b | bal b < n && member p (vot b) = Vote (bal b) (dec b) p
         | otherwise = VNull

maxVotes1 :: BallotNumber -> NonEmptySet Priest -> Set Ballot -> Vote
maxVotes1 n ps = foldMap bToV where
  pset = nes ps
  bToV b | bal b < n && overlap pset (vot b) = 
             Vote (bal b) (dec b) (Set.findMax (intersection pset (vot b)))
         | otherwise = VNull

maxVote2 :: BallotNumber -> Priest -> Set Ballot -> Vote
maxVote2 n p bs = mmax vs where
  vs = [ v |
         v@(Vote vn _ vp) <- toList (votes bs)
       , vp == p
       , vn < n ]

maxVotes2 :: BallotNumber -> NonEmptySet Priest -> Set Ballot -> Vote
maxVotes2 n ps bs = mmax vs where
  pset = nes ps
  vs = [ v | 
         v@(Vote vn _ vp) <- toList (votes bs)
       , Set.member vp pset
       , vn < n ]

test'maxVote = let ns1 = fmap bal (toList ballots)
                   ns = nub . sort . concat $ [ns1, map succ ns1]
               in and [ maxVote1 n p ballots == maxVote2 n p ballots |
                        n <- ns
                      , p <- priests ]

test'maxVotes = let ns1 = fmap bal (toList ballots)
                    ns = nub . sort . concat $ [ns1, map succ ns1]
                    pss = map qrm (toList ballots)
                in and [ maxVotes1 n ps ballots == maxVotes2 n ps ballots |
                         n <- ns
                       , ps <- pss ]

prop'B3 :: Set Ballot -> Bool
prop'B3 bs = all test bs where
  test b = maybe True ((==) (dec b)) $ v'dec $ maxVotes1 (bal b) (qrm b) bs
