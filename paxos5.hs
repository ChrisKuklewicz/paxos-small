{-# LANGUAGE GeneralizedNewtypeDeriving, RecordWildCards #-}
-- Converging on basic protocol
module Main where

import Prelude hiding            (maximum,foldr,any,all,map,log)

import Control.Concurrent        (forkIO,myThreadId,killThread
                                 ,MVar,newEmptyMVar,tryPutMVar,readMVar)
import Control.Exception         (mask,finally)
import Control.Concurrent.STM    (STM,atomically,orElse,retry,registerDelay
                                 ,TChan,newTChanIO,writeTChan,readTChan
                                 ,TVar,newTVarIO,writeTVar,readTVar)
import Control.Monad             (when,forever,forM_,void)
import Control.Monad.Writer      (WriterT,execWriterT,tell,lift)
import Data.Foldable             (Foldable,toList,foldMap,foldr,all,maximum)
import Data.Function             (on)
import Data.List                 (find,tails,nub,sort,delete,partition)
import Data.Map as Map           (Map,fromList,keys,lookup,insert,size,findMax,keysSet,elems)
import Data.Maybe                (fromMaybe,mapMaybe)
import Data.Monoid               (Monoid(..),Endo(..))
import Data.Set as Set           (Set,insert,minView,member,fromList
                                 ,intersection,findMax,isSubsetOf)
import qualified Data.Set as Set (map,null)
import System.Random             (randomRIO,randomRs,newStdGen)

-- Generalize map properly
map :: Functor f => (a->b) -> (f a -> f b)
map = fmap

-- Maximum with a default element
mmax :: (Foldable t, Ord a) => a -> t a -> a
mmax e = foldr max e

-- Express non-empty set in a way that is correct by construction
newtype NonEmptySet a = NES (a,Set a)
   deriving (Eq,Ord,Show)

mkNES :: Set a -> Maybe (NonEmptySet a)
mkNES = fmap NES . Set.minView

nes :: Ord a => NonEmptySet a -> Set a
nes (NES x) = uncurry Set.insert x

-- Types of things mentioned in the Paper on the Synod protocol

newtype BallotNumber = BallotNumber (Integer,Priest) deriving (Eq,Ord)
newtype Decree = Decree String deriving (Eq,Ord)
newtype Priest = Priest String deriving (Eq,Ord)

instance Show BallotNumber where show (BallotNumber (n,Priest s)) = show n ++ (';': s)
instance Show Decree where show (Decree s) = s
instance Show Priest where show (Priest s) = s

getNumber :: BallotNumber -> Integer
getNumber (BallotNumber (i,_)) = i

incB :: BallotNumber -> BallotNumber
incB (BallotNumber (i,p)) = BallotNumber (succ i,p)

type Quorum = NonEmptySet Priest

data Ballot = Ballot { bal :: BallotNumber
                     , dec :: Decree
                     , qrm :: Quorum
                     , vot :: Set Priest
                     }
  deriving (Show)

-- prop'ballots'1 would assert all ballots have a unique bal :: BallotNumber
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
                              in Ballot (BallotNumber (n,Priest "")) dec qs vs
          in Set.fromList [ mkB  2 alpha [ "A", "B", "Γ", "∆"      ] [                "∆"      ]
                          , mkB  5 beta  [ "A", "B", "Γ",      "E" ] [           "Γ"           ]
                          , mkB 14 alpha [      "B",      "∆", "E" ] [      "B",           "E" ]
                          , mkB 27 beta  [ "A",      "Γ", "∆"      ] [ "A",      "Γ", "∆"      ]
                          , mkB 29 beta  [      "B", "Γ", "∆"      ] [      "B"                ]
                          ]

-- important: VNull is less than all (Vote _ _ _) in the derived Ord instance
data MVote = VNull Priest | V AVote deriving (Eq,Ord,Show)
data AVote = Vote { a'bal :: BallotNumber
                  , a'dec :: Decree
                  , a'pst :: Priest }
  deriving (Eq,Ord,Show)

v'dec :: MVote -> Maybe Decree
v'dec (VNull _) = Nothing
v'dec (V v) = Just (a'dec v)

votes :: Set Ballot -> Set AVote
votes = foldMap ballotToVotes

ballotToVotes :: Ballot -> Set AVote
ballotToVotes b = Set.map (Vote (bal b) (dec b)) (vot b)

maxVote1 :: BallotNumber -> Priest -> Set Ballot -> MVote
maxVote1 n p = head'p . mapMaybe bToV . toList where
  head'p [] = VNull p
  head'p (v:_) = v
  bToV b | bal b < n && Set.member p (vot b) = Just (V (Vote (bal b) (dec b) p))
         | otherwise = Nothing

maxVotes1 :: BallotNumber -> NonEmptySet Priest -> Set Ballot -> MVote
maxVotes1 n ps = head'p . mapMaybe bToV . toList  where
  pset = nes ps
  head'p [] = VNull (Set.findMax pset)
  head'p (v:_) = V v
  bToV b | bal b < n && overlap pset (vot b) = Just $
             Vote (bal b) (dec b) (Set.findMax (Set.intersection pset (vot b)))
         | otherwise = Nothing

maxVote2 :: BallotNumber -> Priest -> Set Ballot -> MVote
maxVote2 n p bs = mmax (VNull p) vs where
  vs = [ V v |
         v@(Vote vn _ vp) <- toList (votes bs)
       , vp == p
       , vn < n ]

maxVotes2 :: BallotNumber -> NonEmptySet Priest -> Set Ballot -> MVote
maxVotes2 n ps bs = mmax nullP vs where
  pset = nes ps
  nullP = VNull (Set.findMax pset)
  vs = [ V v | 
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

-- -- Simulate the basic protocol -- --

data Ledger = Ledger { owner      :: !Priest
                     , decrees    :: !(Set Decree)
                     , lastTried  :: !(Maybe BallotNumber)
                     -- ^ The number of the last ballot that p tried to initiate, or Nothing
                     , prevVote   :: !MVote
                     -- ^ The vote cast by p in the highest-numbered ballot in which he voted
                     , nextBallot :: !(Maybe BallotNumber)
                     -- ^ The largest value of b for which p has sent a LastVote(b, v) message
                     , myVotes    :: !(Set AVote)
                     }

blankLedger = Ledger { owner = Priest "blankLedger"
                     , decrees    = mempty
                     , lastTried  = Nothing
                     , prevVote   = VNull (owner blankLedger)
                     , nextBallot = Nothing
                     , myVotes    = mempty }

-- For all (lo,hi) in avoid the owner has promised not to vote on a any new ballot with BallotNumber
-- n such that lo<n<hi. This preserves prop'B3 because the owner has responsed with LastBallot(hi,v)
-- with Just lo = v'bal v to a NextBallot(hi) message from another priest or the owner.

data Missive = Missive { from :: Priest
                       , message :: Message }
  deriving (Eq,Show)

data Message = NextBallot BallotNumber         | LastVote BallotNumber MVote
             | BeginBallot BallotNumber Decree | Voted BallotNumber Priest
             | Success Decree
  deriving (Eq,Show)

-- ideal life cycle is OutOfOffice -> Idle -> Researching -> Balloting -> _retired_
-- in practice the parliamentarian may go Idle or OutOfOffice at any time

data TaskPA = Idle
            | Researching (Map Priest MVote)
            | Balloting Ballot
            | OutOfOffice
  deriving (Eq,Show)

data ActPA = Send Priest Message
           | Log String
           | Announce Message
           | Retire
  deriving (Eq,Show)


-- Small language of functions for writing in monad M

type M a = WriterT (Endo [ActPA]) STM a

runM :: M () -> STM [ActPA]
runM = fmap (($ []) . appEndo) . execWriterT

-- Work in WriterT wrapped STM, so lift the needed actions
retryM = lift retry
readTVarM = lift . readTVar
readTChanM = lift . readTChan
writeTVarM var = lift . writeTVar var

todo ls = tell (Endo (ls ++))

pass = return ()

reply source destination m | source == destination = return ()
                           | otherwise =
  todo [ Log $ "Send to "++show destination ++ " : "++show m 
       , Send destination m ]

log s = todo [ Log s ]

announce m = todo [ Log $ "Announce "++show m
                  , Announce m ]

succeed p m = todo [ Log $ "Announce "++show m
                   , Announce m
                   , Log $ "Retire "++show p
                   , Retire ]

retire p = todo [ Log $ "Retire "++show p
                , Retire ]

data PriestAgent = PA { name :: Priest
                      , inbox :: TChan Missive
                      , ledger :: TVar Ledger
                      , task :: TVar TaskPA
                      }

type MS = Map Priest (Missive -> IO ())

data Parliament = Parliament { pas :: [PriestAgent]
                             , passed :: TVar (Maybe Decree)
                             , majority :: Int
                             , messageService :: MS
                             , logger :: String -> IO ()
                             }

makePA :: Priest -> IO PriestAgent
makePA name = do
  inbox <- newTChanIO
  ledger <- newTVarIO (blankLedger { owner = name, prevVote = VNull name } )
  task <- newTVarIO OutOfOffice
  return (PA {..})

makeParliment :: IO Parliament
makeParliment = do
  putStrLn $ "Parliament founded with "++show priests
  pas <- mapM makePA priests
  passed <- newTVarIO Nothing
  let messageService = Map.fromList . map makeMS $ pas
        where makeMS (PA {..}) = (name,sendTo)
                where sendTo m = do 
                        ok <- if name==from m
                                then return True -- always works to send to oneself
                                else fmap (1/=) (randomRIO (1,4::Int))
                        if ok
                           then (atomically (writeTChan inbox m))
                           else logger $ "Messenger dropped: "++show (name,m)
                           
      logger = putStrLn
      majority = 1 + quot (length priests) 2
  return (Parliament {..})

-- Microseconds
attentionSpan :: Int
attentionSpan = 10^(6::Int)

fork :: IO () -> IO (MVar ())
fork act = do
  v <- newEmptyMVar
  void . mask $ \ unmask -> forkIO (finally (unmask act) (tryPutMVar v ()))
  return v

runPA :: Parliament -> PriestAgent -> IO ()
runPA (Parliament {..}) (PA {..})  = do
  gen <- newStdGen
  coins <- newTVarIO (randomRs (1,2::Int) gen)
  forever (loop coins)
 where
  loop :: TVar [Int] -> IO ()
  loop coins = do
    bored <- registerDelay =<< randomRIO (0,attentionSpan)
    todos <- atomically $ (runM handleMail) 
                 `orElse` (runM (changeTask bored coins))
    let (doFirst,doRetire) = partition (Retire==) todos
    forM_ doFirst $ \ todo ->
       case todo of
         Send to msg -> sendTo to msg
         Log s -> logger (show name ++ ": " ++ s)
         Announce msg -> mapM_ (`sendTo` msg) 
                               (delete name $ Map.keys messageService)
         Retire -> return () -- impossible due to partition
    when (not (null doRetire)) $ myThreadId >>= killThread
   where 
     sendTo to msg =
       case Map.lookup to messageService of
         Nothing -> logger $ show name ++": could not send "++show msg
                          ++" to unrecognized priest " ++ show to
         Just giveToMessenger -> giveToMessenger (Missive { from=name, message=msg })

  changeTask :: TVar Bool -> TVar [Int] -> M ()
  changeTask bored coins = do
    amBored <- readTVarM  bored
    when (not amBored) retryM
    t <- readTVarM task
    (coin:cs) <- readTVarM coins
    writeTVarM coins cs
    case (t,coin==1) of
      (Idle          , True)  -> startBallot
      (Idle          , False) ->  leaveOffice
      (Researching {}, True)  ->  leaveOffice
      (Researching {}, False) ->   idleOffice
      (Balloting {}  , True)  ->  leaveOffice
      (Balloting {}  , False) ->   idleOffice
      (OutOfOffice   , True)  ->   idleOffice
      (OutOfOffice   , False) -> startBallot
   where
    leaveOffice = setTask OutOfOffice
    idleOffice = setTask Idle

-- handleMail implements a state machine, based on current Message and Task
  handleMail :: M ()
  handleMail = do
    (Missive {from=p,message=m}) <- readTChanM inbox
    t <- readTVarM task
    l <- readTVarM ledger
    case (t,m) of
      (OutOfOffice    , _)               -> pass
      (_              , NextBallot b)    -> replyBallot l p b
      (_              , BeginBallot b d) -> perhapsVote l p b d
      (Researching lvs, LastVote b v)    -> noteLastVote l lvs b v p
      (_              , LastVote {})     -> pass
      (Balloting blt  , Voted b q)       -> noteVoted l blt b q
      (_              , Voted {})        -> pass
      (_              , Success d)       -> noteSuccess l d

  startBallot = do
    l <- readTVarM ledger
    complete <- readTVarM passed -- outside the protocol, used to quit the thread
    case complete of
      Just d -> noteSuccess l d
      Nothing -> do
        let highest = max (maybe (-1) getNumber (lastTried l))
                          (maybe (-1) getNumber (nextBallot l))
            b = BallotNumber (succ highest,name)
            l' = l { lastTried = Just b }
        saveLedger l'
        replyBallot l' name b -- This will always set nextBallot by construction of 'b'
        setTask (Researching mempty)
        announce (NextBallot b)

  replyBallot l p b | Just n <- nextBallot l, b<=n = pass
                    | otherwise = do
    saveLedger (l { nextBallot = Just b })
    reply name p (LastVote b (prevVote l))

  perhapsVote l p b d | Just b /= nextBallot l = pass
                      | otherwise = do
    saveLedger (l { prevVote = V (Vote b d name) })
    reply name p (Voted b name)

  noteLastVote l lvsIn b v p | lastTried l /= Just b = pass
                             | otherwise = do
    let lvs = Map.insert p v lvsIn
    if Map.size lvs < majority
       then setTask (Researching lvs)
       else do
         let Just q = mkNES $ Map.keysSet lvs -- safe
             d = fromMaybe (Decree $ "Decree "++show b) (v'dec vote)
               where vote = maximum (Map.elems lvs) -- safe
         let blt = Ballot { bal=b,qrm=q,dec=d,vot=mempty}
         setTask (Balloting blt)
         perhapsVote l name b d
         announce (BeginBallot b d)

  noteVoted l bltIn b p | bal bltIn /= b || Just b /= lastTried l = pass
                        | otherwise = do
    let blt = bltIn { vot = Set.insert p (vot bltIn) }
    if nes (qrm blt) `isSubsetOf` vot blt
      then do
        complete <- readTVarM passed
        case complete of
          Nothing -> do
            writeTVarM passed (Just (dec blt))
            noteSuccess l (dec blt)
            succeed name (Success (dec blt))
          Just old'd -> do
            setTask Idle
            log $ "Additional decree passed, old is "++show old'd
                  ++", new is "++show (dec blt)
      else setTask (Balloting blt)

  noteSuccess l d = do
    saveLedger (l { decrees = Set.insert d (decrees l) })
    setTask OutOfOffice
    retire name

  saveLedger x = writeTVarM ledger $! x
  setTask t = writeTVarM task t

main = do
  p <- makeParliment
  vs <- mapM (fork . (runPA  p)) (pas p)
  mapM_ readMVar vs
