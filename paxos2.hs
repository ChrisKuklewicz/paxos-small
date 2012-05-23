{-# LANGUAGE GeneralizedNewtypeDeriving, RecordWildCards #-}
-- Synod basic protocol
module Paxos1 where

import Prelude hiding            (maximum,foldr,all,map)

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad             (when,forever)
import Data.Foldable             (Foldable,toList,foldMap,maximum,foldr,all)
import Data.Function             (on)
import Data.List                 (find,tails,nub,sort,null)
import Data.Map as Map           (Map,fromList,keys,lookup)
import Data.Maybe                (mapMaybe)
import Data.Monoid               (mempty)
import Data.Set as Set           (Set,insert,minView,member,fromList
                                 ,intersection,findMax)
import qualified Data.Set as Set (map,null)
import System.Random             (randomRIO)

map :: Functor f => (a->b) -> (f a -> f b)
map = fmap

-- Express non-empty set in a way that is correct by construction
newtype NonEmptySet a = NES (a,Set a)
   deriving (Eq,Ord,Show)

mmax :: (Foldable t, Ord a) => a -> t a -> a
mmax e = foldr max e

-- Only introduce and eliminate NES with mkNES and nes
mkNES :: Set a -> Maybe (NonEmptySet a)
mkNES = fmap NES . Set.minView

nes :: Ord a => NonEmptySet a -> Set a
nes (NES x) = uncurry Set.insert x

-- Types of things mentioned in the Paper

newtype BallotNumber = BallotNumber (Integer,Priest) deriving (Eq,Ord)
newtype Decree = Decree String deriving (Eq,Ord) -- should not be ""
newtype Priest = Priest String deriving (Eq,Ord) -- should not be ""

instance Show BallotNumber where show (BallotNumber (n,Priest s)) = show n ++ (';': s)
instance Show Decree where show (Decree s) = s
instance Show Priest where show (Priest s) = s

incB :: BallotNumber -> BallotNumber
incB (BallotNumber (i,p)) = BallotNumber (succ i,p)

instance Num BallotNumber where
  (+) = undefined; (*) = undefined; abs = undefined; signum = undefined
  fromInteger i = BallotNumber (i,Priest "Num")

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

overlap b1 b2 = not . Set.null $ Set.intersection b1 b2

a'ok = and ok

ok = map ($ ballots) [ prop'ballots'2
                     , prop'ballots'3
                     , test'maxVote
                     , test'maxVotes
                     , prop'B3
                     ]

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

ballots = let mkB n dec q v = let Just qs = mkNES (Set.fromList $ map Priest q)
                                  vs =  Set.fromList $ map Priest v
                              in Ballot n dec qs vs
          in Set.fromList [ mkB  2 alpha [ "A", "B", "Γ", "∆"      ] [                "∆"      ]
                          , mkB  5 beta  [ "A", "B", "Γ",      "E" ] [           "Γ"           ]
                          , mkB 14 alpha [      "B",      "∆", "E" ] [      "B",           "E" ]
                          , mkB 27 beta  [ "A",      "Γ", "∆"      ] [ "A",      "Γ", "∆"      ]
                          , mkB 29 beta  [      "B", "Γ", "∆"      ] [      "B"                ]
                          ]

-- important: VNull is less than all (Vote _ _ _) in the derived Ord instance
data Vote = VNull Priest | Vote BallotNumber Decree Priest deriving (Eq,Ord,Show)

v'bal :: Vote -> Maybe BallotNumber
v'bal (VNull _) = Nothing
v'bal (Vote b _ _) = Just b

v'dec :: Vote -> Maybe Decree
v'dec (VNull _) = Nothing
v'dec (Vote _ d _) = Just d

v'pst :: Vote -> Priest
v'pst (VNull p) = p
v'pst (Vote _ _ p) = p

votes :: Set Ballot -> Set Vote
votes = foldMap ballotToVotes

ballotToVotes :: Ballot -> Set Vote
ballotToVotes b = Set.map (Vote (bal b) (dec b)) (vot b)

maxVote1 :: BallotNumber -> Priest -> Set Ballot -> Vote
maxVote1 n p = head'p . mapMaybe bToV . toList where
  head'p [] = VNull p
  head'p (v:_) = v
  bToV b | bal b < n && Set.member p (vot b) = Just (Vote (bal b) (dec b) p)
         | otherwise = Nothing

maxVotes1 :: BallotNumber -> NonEmptySet Priest -> Set Ballot -> Vote
maxVotes1 n ps = head'p . mapMaybe bToV . toList  where
  pset = nes ps
  head'p [] = VNull (Set.findMax pset)
  head'p (v:_) = v
  bToV b | bal b < n && overlap pset (vot b) = Just $
             Vote (bal b) (dec b) (Set.findMax (Set.intersection pset (vot b)))
         | otherwise = Nothing

maxVote2 :: BallotNumber -> Priest -> Set Ballot -> Vote
maxVote2 n p bs = mmax (VNull p) vs where
  vs = [ v |
         v@(Vote vn _ vp) <- toList (votes bs)
       , vp == p
       , vn < n ]

maxVotes2 :: BallotNumber -> NonEmptySet Priest -> Set Ballot -> Vote
maxVotes2 n ps bs = mmax nullP vs where
  pset = nes ps
  nullP = VNull (Set.findMax pset)
  vs = [ v | 
         v@(Vote vn _ vp) <- toList (votes bs)
       , Set.member vp pset
       , vn < n ]

test'maxVote :: Set Ballot -> Bool
test'maxVote bs =
   let ns1 = fmap bal (toList bs)
       ns = nub . sort . concat $ [ns1, map incB ns1]
   in and [ maxVote1 n p bs == maxVote2 n p bs |
            n <- ns
          , p <- priests ]

test'maxVotes :: Set Ballot -> Bool
test'maxVotes bs =
  let ns1 = fmap bal (toList bs)
      ns = nub . sort . concat $ [ns1, map incB ns1]
      pss = map qrm (toList bs)
  in and [ maxVotes1 n ps bs == maxVotes2 n ps bs |
           n <- ns
         , ps <- pss ]

prop'B3 :: Set Ballot -> Bool
prop'B3 bs = all test bs where
  test b = maybe True ((==) (dec b)) $ v'dec $ maxVotes1 (bal b) (qrm b) bs


data Ledger = Ledger { owner :: Priest
                     , decrees :: Set (BallotNumber,Decree)
                     , lastNumber :: Integer
                     , avoid :: Set (BallotNumber,BallotNumber)
                     , myVotes :: Set Vote
                     }

-- For all (lo,hi) in avoid the owner has promised not to vote on a any new ballot with BallotNumber
-- n such that lo<n<hi. This preserves prop'B3 because the owner has responsed with LastBallot(hi,v)
-- with Just lo = v'bal v to a NextBallot(hi) message from another priest or the owner.

data Message = NextBallot BallotNumber
             | LastVote BallotNumber Vote
--             | BeginBallot B D
  deriving Show

data Missive = Missive { from :: Priest
                       , to :: Priest
                       , message :: Message }
  deriving Show

data PriestAgent = PA { name :: Priest
                      , inbox :: TChan Missive
                      , ledger :: TVar Ledger
                      }

subsets [] = []:[]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)

quorums = let count = length priests
              need = 1 + quot count 2
          in filter ((need <=) . length) (subsets priests)

makePA :: Priest -> IO PriestAgent
makePA name = do
  inbox <- newTChanIO
  ledger <- newTVarIO (Ledger { owner = name
                              , decrees = mempty
                              , lastNumber = 0    -- magic number
                              , avoid = mempty
                              , myVotes = mempty } )
  return (PA {..})

type MS = Map Priest (Missive -> IO ())

data Parliament = Parliament { pas :: [PriestAgent]
                             , majority :: Int
                             , messageService :: MS
                             , logger :: String -> IO ()
                             }

makeParliment :: IO Parliament
makeParliment = do
  pas <- mapM makePA priests
  let messageService = Map.fromList . map makeMS $ pas
        where makeMS (PA {..}) = (name,\m -> do ok <- randomRIO (1,4::Int)
                                                when (1/=ok) (atomically (writeTChan inbox m)))
      logger = putStrLn
      majority = 1 + quot (length priests) 2
  return (Parliament {..})

-- Microseconds
proposeDelay :: Int
proposeDelay = 10^6

data StatePA = Idle
             | Proposing BallotNumber [(Priest,Vote)]

data ActPA = Send Priest Message
           | Log String
           | Announce Message
           | Pass

runPA :: Parliament -> PriestAgent -> IO ()
runPA p (PA {..})  = forever loop where
  loop :: IO ()
  loop = do bored <- registerDelay =<< randomRIO (0,proposeDelay)
            todo <- atomically $ handleMail `orElse` proposeBallot bored
            case todo of
              Send to msg -> sendTo to msg
              Log s -> logger p (show name ++ ": " ++ s)
              Announce msg -> mapM_ (\whom -> sendTo whom msg) (Map.keys (messageService p))
              Pass -> return ()

  sendTo to msg | to == name = return ()
                | otherwise =
    let m = Missive { from=name, to=to, message=msg }
    in case Map.lookup to (messageService p) of
         Nothing -> logger p $ show name ++": could not send " ++ show msg ++ " to unrecognized priest " ++ show to
         Just giveToMessenger -> giveToMessenger m

  handleMail :: STM ActPA
  handleMail = do
    m <- readTChan inbox
    if to m /= name
      then return (Log $ "ignoring missent " ++ show m)
      else do
        case message m of
          LastVote {} -> return (Log $ "ignoring "++ show m)
          NextBallot n -> do
            l <- readTVar ledger
            let v = mmax (VNull name) 
                         [v | v@(Vote vn _ _) <- toList (myVotes l), vn < n ]
                lo = case v of 
                       VNull p -> (-1)  -- magic number
                       Vote vn _ _ -> vn
                l' = l { avoid = Set.insert (lo,n) (avoid l) }
            writeTVar ledger l'
            return (Send (from m) (LastVote n v))

  proposeBallot :: TVar Bool -> STM ActPA
  proposeBallot bored = do
    ideaReady <- readTVar bored
    when (not ideaReady) retry
    return undefined
