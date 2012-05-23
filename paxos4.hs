{-# LANGUAGE GeneralizedNewtypeDeriving, RecordWildCards #-}
-- Converging on basic protocol
module Main where

import Prelude hiding            (maximum,foldr,any,all,map,log)

import Control.Concurrent        (forkIO,threadDelay,newEmptyMVar,MVar,putMVar,takeMVar,myThreadId,killThread)
import Control.Exception         (mask,finally)
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
data MVote = VNull Priest | V AVote deriving (Eq,Ord,Show)
data AVote = Vote { a'bal :: BallotNumber
                  , a'dec :: Decree
                  , a'pst :: Priest }
  deriving (Eq,Ord,Show)

v'bal :: MVote -> Maybe BallotNumber
v'bal (VNull _) = Nothing
v'bal (V v) = Just (a'bal v)

v'dec :: MVote -> Maybe Decree
v'dec (VNull _) = Nothing
v'dec (V v) = Just (a'dec v)

v'pst :: MVote -> Priest
v'pst (VNull p) = p
v'pst (V v) = a'pst v

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

data Ledger = Ledger { owner      :: !Priest
                     , decrees    :: !(Set Decree)
                     , lastTried  :: !(Maybe BallotNumber) -- ^ The number of the last ballot that p tried to initiate, or Nothing
                     , prevVote   :: !MVote                -- ^ The vote cast by p in the highest-numbered ballot in which he voted
                     , nextBallot :: !(Maybe BallotNumber) -- ^ The largest value of b for which p has sent a LastVote(b, v) message
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

pass :: STM [ActPA]
pass = return []

reply :: Priest -> Message -> STM [ActPA]
reply p m = return [ Log $ "Send to "++show p ++ " : "++show m 
                   , Send p m ]
log s = return [Log s]
announce m = return [ Log $ "Announce "++show m
                    , Announce m ]
succeed p m = return [ Log $ "Announce "++show m
                     , Announce m
                     , Log $ "Retire "++show p
                     , Retire ]
retire p = return [ Log $ "Retire "++show p
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

subsets [] = []:[]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)

quorums = let count = length priests
              need = 1 + quot count 2
          in filter ((need <=) . length) (subsets priests)

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
  mask $ \ unmask -> forkIO (finally (unmask act) (putMVar v ()))
  return v

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
                Retire -> myThreadId >>= killThread
    where sendTo to msg =
            case Map.lookup to messageService of
              Nothing -> logger $ show name ++": could not send " ++ show msg ++ " to unrecognized priest " ++ show to
              Just giveToMessenger -> giveToMessenger (Missive { from=name, message=msg })

  changeTask :: TVar Bool -> Int -> STM [ActPA]
  changeTask bored coin = do
    amBored <- readTVar bored
    when (not amBored) retry
    t <- readTVar task
    let leaveOffice = writeTVar task OutOfOffice >> pass
        idleOffice = writeTVar task Idle >> pass
    case (t,coin) of
      (Idle,1)           -> startBallot
      (Idle,_)           ->  leaveOffice
      (Researching {},1) ->  leaveOffice
      (Researching {},_) ->   idleOffice
      (Balloting {},1)   ->  leaveOffice
      (Balloting {},_)   ->   idleOffice
      (OutOfOffice,1)    ->   idleOffice
      (OutOfOffice,_)    -> startBallot

-- handleMail implements a state machine, based on current Message and Task
  handleMail :: STM [ActPA]
  handleMail = do
    (Missive {from=p,message=m}) <- readTChan inbox
    t <- readTVar task
    case (t,m) of
      (OutOfOffice    , _ )               -> pass
      (_              , NextBallot b )    -> replyBallot p b
      (_              , BeginBallot b d ) -> perhapsVote p b d
      (Researching lvs, LastVote b v )    -> noteLastVote lvs b v p
      (_              , LastVote {} )     -> pass
      (Balloting blt  , Voted b q)        -> noteVoted blt b q
      (_              , Voted {})         -> pass
      (_              , Success d)        -> noteSuccess d

  startBallot = do
    old <- readTVar passed
    case old of
      Just d -> noteSuccess d
      _ -> do
        l <- readTVar ledger
        let highest = max (maybe (-1) getNumber (lastTried l)) -- basic protocol: larger than lastTried
                          (maybe (-1) getNumber (nextBallot l)) -- need this so replyBallot sets nextBallot
            b = BallotNumber (succ highest,name)
        writeTVar ledger $! l { lastTried = Just b }
        writeTVar task (Researching mempty)
        void $ replyBallot name b -- This will always set nextBallot by construction of b
        announce (NextBallot b)

  replyBallot p b = do
    l <- readTVar ledger
    case nextBallot l of
      Just n | b<=n -> pass
      _ -> do writeTVar ledger $! l { nextBallot = Just b }
              reply p (LastVote b (prevVote l))

  noteLastVote lvsIn b v p = do
    l <- readTVar ledger
    if lastTried l /= Just b
      then pass
      else do
        let lvs = Map.insert p v lvsIn
        if Map.size lvs < majority
           then do
             writeTVar task $! Researching lvs
             pass
           else do
             let Just quorum = mkNES $ Map.keysSet lvs -- safe
                 d = fromMaybe (Decree $ "Decree "++show b) (v'dec vote)
                   where vote = mmax nullP (Map.elems lvs)
                           where nullP = VNull (fst $ Map.findMax lvs) -- ignored by v'dec & fromMaybe
             let blt = Ballot { bal=b,qrm=quorum,dec=d,vot=mempty}
             writeTVar task $! Balloting blt
             void $ perhapsVote name b d
             announce (BeginBallot b d)

  perhapsVote p b d = do
    l <- readTVar ledger
    if Just b /= nextBallot l
      then pass
      else do
        writeTVar ledger $! l { prevVote = V (Vote b d name) }
        reply p (Voted b name)

  noteVoted bltIn b p = do
    l <- readTVar ledger
    if bal bltIn /= b || Just b /= lastTried l
      then pass
      else do
        let blt = bltIn { vot = Set.insert p (vot bltIn) }
        if nes (qrm blt) `isSubsetOf` vot blt
          then do
            writeTVar task Idle
            p <- readTVar passed
            case p of
              Nothing -> do
                writeTVar passed (Just (dec blt))
                void $ noteSuccess (dec blt)
                succeed name (Success (dec blt))
              Just old'd -> do
                log $ "Additional decree passed, old is "++show old'd++", new is "++show (dec blt)
          else do
            writeTVar task (Balloting blt)
            pass

  noteSuccess d = do
    l <- readTVar ledger
    writeTVar ledger $! l { decrees = Set.insert d (decrees l) }
    retire name

main = do
  p <- makeParliment
  vs <- mapM (fork . (runPA  p)) (pas p)
  mapM_ takeMVar vs


