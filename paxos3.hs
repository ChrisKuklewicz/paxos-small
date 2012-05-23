{-# LANGUAGE GeneralizedNewtypeDeriving, RecordWildCards #-}
-- Synod basic protocol
module Paxos3 where

import Prelude hiding            (maximum,foldr,any,all,map,log)

import Control.Concurrent.STM    (STM,atomically,orElse,retry,registerDelay
                                 ,TChan,newTChanIO,writeTChan,readTChan
                                 ,TVar,newTVarIO,writeTVar,readTVar)
import Control.Monad             (when,forever,forM_,void)
import Data.Foldable             (Foldable,toList,foldMap,foldr,all,any)
import Data.Function             (on)
import Data.List                 (find,tails,nub,sort,delete)
import Data.Map as Map           (Map,fromList,keys,lookup,insert,size,findMax,keysSet,elems)
import Data.Maybe                (fromMaybe,mapMaybe)
import Data.Monoid               (mempty)
import Data.Set as Set           (Set,insert,minView,member,fromList
                                 ,intersection,findMax,isSubsetOf)
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

getNumber :: BallotNumber -> Integer
getNumber (BallotNumber (i,_)) = i

incB :: BallotNumber -> BallotNumber
incB (BallotNumber (i,p)) = BallotNumber (succ i,p)

instance Num BallotNumber where
  (+) = undefined; (*) = undefined; abs = undefined; signum = undefined
  fromInteger i = BallotNumber (i,Priest "Num")

type Quorum = NonEmptySet Priest

data Ballot = Ballot { bal :: BallotNumber
                     , dec :: Decree
                     , qrm :: Quorum
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

a'ok = and tests'ok

tests'ok = map ($ ballots)
  [ prop'ballots'2
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


data Ledger = Ledger { owner      :: !Priest
                     , decrees    :: !(Set Decree)
                     , lastNumber :: !Integer
                     , avoid      :: !(Set (BallotNumber,BallotNumber))
                     , myVotes    :: !(Set Vote)
                     }

-- For all (lo,hi) in avoid the owner has promised not to vote on a any new ballot with BallotNumber
-- n such that lo<n<hi. This preserves prop'B3 because the owner has responsed with LastBallot(hi,v)
-- with Just lo = v'bal v to a NextBallot(hi) message from another priest or the owner.

data Missive = Missive { from :: Priest
                       , message :: Message }
  deriving (Eq,Show)

data Message = NextBallot BallotNumber
             | LastVote BallotNumber Vote
             | BeginBallot BallotNumber Decree
             | Voted BallotNumber Priest
             | Success Decree
  deriving (Eq,Show)

data TaskPA = Idle
            | Researching BallotNumber (Map Priest Vote)
            | Balloting Ballot
            | OutOfOffice
  deriving (Eq,Show)

data ActPA = Send Priest Message
           | Log String
           | Announce Message
  deriving (Eq,Show)

pass :: STM [ActPA]
pass = return []
reply p m = return [Send p m]
log s = return [Log s]
announce m = return [Announce m]

data PriestAgent = PA { name :: Priest
                      , inbox :: TChan Missive
                      , ledger :: TVar Ledger
                      , task :: TVar TaskPA
                      }

type MS = Map Priest (Missive -> IO ())

data Parliament = Parliament { pas :: [PriestAgent]
                             , majority :: Int
                             , messageService :: MS
                             , logger :: String -> IO ()
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
  task <- newTVarIO OutOfOffice
  return (PA {..})

makeParliment :: IO Parliament
makeParliment = do
  pas <- mapM makePA priests
  let messageService = Map.fromList . map makeMS $ pas
        where makeMS (PA {..}) = (name,sendTo)
                where sendTo m = do 
                        ok <- if name==from m
                                then return True -- always works to send to oneself
                                else fmap (1/=) (randomRIO (1,4::Int))
                        when ok (atomically (writeTChan inbox m))
      logger = putStrLn
      majority = 1 + quot (length priests) 2
  return (Parliament {..})

-- Microseconds
attentionSpan :: Int
attentionSpan = 10^(6::Int)

runPA :: Parliament -> PriestAgent -> IO ()
runPA (Parliament {..}) (PA {..})  = forever loop where
  loop :: IO ()
  loop = do bored <- registerDelay =<< randomRIO (0,attentionSpan)
            coin <- randomRIO (1,2::Int)
            todos <- atomically $ handleMail `orElse` changeTask bored coin
            forM_ todos $ \ todo ->
              case todo of
                Send to msg -> sendTo to msg
                Log s -> logger (show name ++ ": " ++ s)
                Announce msg -> mapM_ (`sendTo` msg) (delete name $ Map.keys messageService)
    where sendTo to msg =
            case Map.lookup to messageService of
              Nothing -> logger $ show name ++": could not send " ++ show msg ++ " to unrecognized priest " ++ show to
              Just giveToMessenger -> giveToMessenger (Missive { from=name, message=msg })

  changeTask :: TVar Bool -> Int -> STM [ActPA]
  changeTask bored coin = do
    amBored <- readTVar bored
    when (not amBored) retry
    t <- readTVar task
    case (t,coin) of
      (Idle,1) -> startBallot
      (Idle,_) -> writeTVar task OutOfOffice >> pass
      (Researching {},1) -> writeTVar task OutOfOffice >> pass
      (Researching {},_) -> writeTVar task Idle >> pass
      (OutOfOffice,1) -> writeTVar task Idle >> pass
      (OutOfOffice,_) -> startBallot
      (Balloting {},1) -> writeTVar task OutOfOffice >> pass
      (Balloting {},_) -> writeTVar task Idle >> pass

-- handleMail implements a state machine, based on current Message and Task
  handleMail :: STM [ActPA]
  handleMail = do
    (Missive {from=p,message=m}) <- readTChan inbox
    t <- readTVar task
    case (t,m) of
      (OutOfOffice      , _ )                   -> pass
      (_                , NextBallot n )        -> replyBallot p n
      (_                , BeginBallot n d )     -> perhapsVote p n d
      (Researching b lvs, LastVote n v ) | b==n -> noteLastVote b lvs p v
      (_                , LastVote {} )         -> pass
      (Balloting b      , Voted n q) | bal b==n -> noteVoted b q
      (_                , Voted {})             -> pass
      (_                , Success d)            -> noteSuccess d

  startBallot = do
    l <- readTVar ledger
    let lastNumber' = succ (lastNumber l)
        n = BallotNumber (lastNumber',name)
    writeTVar ledger (l { lastNumber = lastNumber' })
    writeTVar task (Researching n mempty)
    void $ replyBallot name n
    announce (NextBallot n)

  replyBallot p b = do
    l <- readTVar ledger
    let vote = mmax (VNull name) 
                 [v | v@(Vote vn _ _) <- toList (myVotes l), vn < b ]
        lo = case vote of 
               VNull _ -> (-1)  -- magic number
               Vote vn _ _ -> vn
        l' = l { avoid = Set.insert (lo,b) (avoid l)
               , lastNumber = max (lastNumber l) (getNumber b) }
    writeTVar ledger  $! l'
    reply p (LastVote b vote)

  noteLastVote b lvsIn p v = do
    let lvs = Map.insert p v lvsIn
    if Map.size lvs < majority
       then do
         writeTVar task $! Researching b lvs
         pass
       else do
         let Just quorum = mkNES $ Map.keysSet lvs -- safe
             d = fromMaybe (Decree $ "Decree "++show b) (v'dec vote)
               where vote = mmax nullP (Map.elems lvs)
                       where nullP = VNull (fst $ Map.findMax lvs)
         writeTVar task $! Balloting (Ballot { bal=b,qrm=quorum,dec=d,vot=mempty})
         void $ perhapsVote name b d
         announce (BeginBallot b d)

  perhapsVote p b d = do
    l <- readTVar ledger
    if any (\(lo,hi) -> lo < b && b < hi) (avoid l) then pass
      else do
        writeTVar ledger $! l { myVotes = Set.insert (Vote b d name) (myVotes l) }
        reply p (Voted b name)

  noteVoted bIn p = do
    let b = bIn { vot = Set.insert p (vot bIn) }
    if nes (qrm b) `isSubsetOf` vot b
      then do
        void $ noteSuccess (dec b)
        announce (Success (dec b))
      else writeTVar task (Balloting b) >> pass

  noteSuccess d = do
    l <- readTVar ledger
    let decrees' = Set.insert d (decrees l)
    writeTVar ledger $! l { decrees = decrees' }
    pass
