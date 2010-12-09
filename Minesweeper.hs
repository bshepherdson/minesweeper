
import qualified Data.Map as M
import Data.Map (Map, (!))
import Data.List
import System.Random
import Control.Monad
import Data.Maybe


data TileTruth = Mine | Num Int -- Num 0 for clear tiles
  deriving (Show,Read,Eq)
data TileState = Concealed | Revealed | Marked
  deriving (Show,Read,Eq)
data Tile = Tile TileState TileTruth
  deriving (Show,Read,Eq)

data Result = ResultError String Board | ResultComplete Board

type Board = Map (Int,Int) Tile


-- parameters -- beginner: 9x9, 10 mines. intermediate: 16x16, 40 mines. expert:  30x16, 99 mines
width  = 30
height = 16
mines  = 99


-- utility functions
adjacent b (i,j) = M.filterWithKey (\(x,y) _ -> abs (x - i) <= 1 && abs (y - j) <= 1) b

isNum (Tile Revealed (Num _)) = True
isNum _                       = False

isMarked (Tile Marked _) = True
isMarked _               = False
 
isConcealed (Tile Concealed _) = True
isConcealed _                  = False

isMine (Tile _ Mine) = True
isMine _             = False


clearCovered (Tile Concealed x) = Tile Revealed x
clearCovered x                  = x

markCovered (Tile Concealed x)  = Tile Marked x
markCovered x                   = x


-- no mistakes made
correct :: Board -> Bool
correct = M.null . M.filter (not . tileCorrect)
  where tileCorrect (Tile Marked (Num _)) = False
        tileCorrect (Tile Revealed Mine)  = False
        tileCorrect _                     = True

-- fully un-concealed (marked, revealed)
complete :: Board -> Bool
complete = M.null . M.filter isConcealed


foldNums f b = let nums = M.filter isNum b
               in  foldl' f b (M.toList nums)


-- looks for Num tiles with N mines already surrounding them
alreadySatisfied = foldNums satisfy
  where satisfy b ((i,j), Tile Revealed (Num n)) = 
          let adj = adjacent b (i,j)
              mines = M.size $ M.filter isMarked adj
          in  if mines == n
                then M.union (M.map clearCovered adj) b -- union is left-biased
                else b -- unchanged


onlyNPossibilities = foldNums possibilities
  where possibilities b ((i,j), Tile Revealed (Num n)) = 
          let adj       = adjacent b (i,j)
              mines     = M.size $ M.filter isMarked adj
              concealed = M.size $ M.filter isConcealed adj
          in  if mines + concealed == n
                then M.union (M.map markCovered adj) b -- union is left-biased
                else b -- unchanged



-- this is the first tricky bit of logic. it solves cases like:
-- OOO1
-- OOO2
-- 122*
-- by considering the 1 and 2 in the lower left.
-- for each number, consider each of its numbered neighbours.
-- compare the adjacent concealed tiles of each numbered tile, and:
-- * if one is a subset of the other and is smaller by the difference in mine count, the superset-only tiles are mines
-- * if one is a subset of the other and the mine counts are the same, the superset-only tiles are clear
-- this does not handle more complex cases of overlap (yet)
subsetConceals = foldNums subsets
  where subsets b ((i,j), Tile Revealed (Num n)) =
          let adj     = adjacent b (i,j)
              adjnums = M.filter isNum adj
              adjcons = M.filter isConcealed adj
              marked  = M.size $ M.filter isMarked adj
              checkNeighbour ((i',j'), Tile Revealed (Num n')) = 
                let adj'     = adjacent b (i',j')
                    adjcons' = M.filter isConcealed adj'
                    marked'  = M.size $ M.filter isMarked adj'
                    left     = M.difference adjcons  adjcons'
                    right    = M.difference adjcons' adjcons
                in case (M.null left, M.null right) of
                     (True,False)  -> case (n-marked) `compare` (n'-marked') of -- compare live mine counts
                                        EQ -> Just (M.union (M.map clearCovered right) b) -- equal mine counts, extras are clear
                                        LT -> case M.size right == (n'-marked') - (n-marked) of
                                                True  -> Just (M.union (M.map markCovered right) b) -- excess mine count equal to extra spaces
                                                False -> Nothing -- doesn't match up right
                                        GT -> error $ "Can't happen TF GT\n" ++ show ((i,j),(i',j')) ++ "\n" ++ show left ++ "\n" ++ show right ++ "\n" ++ visualize b
                     (False,True)  -> case (n-marked) `compare` (n'-marked') of -- compare live mine counts
                                        EQ -> Just (M.union (M.map clearCovered left) b) -- equal mine counts, extras are clear
                                        GT -> case M.size left == (n-marked) - (n'-marked') of
                                                True  -> Just (M.union (M.map markCovered left) b) -- excess mine count equal to extra spaces
                                                False -> Nothing -- doesn't match up right
                                        LT -> error $ "Can't happen FT LT\n" ++ show ((i,j),(i',j')) ++ "\n" ++ show left ++ "\n" ++ show right ++ "\n" ++ visualize b
                     (False,False) -> case (M.size left, M.size right, (n-marked) - (n'-marked')) of
                                        (1, 1, -1) -> Just $ M.union (M.map markCovered right) $ M.union (M.map clearCovered left)  b
                                        (1, 1, 1)  -> Just $ M.union (M.map markCovered left)  $ M.union (M.map clearCovered right) b
                                        _          -> Nothing
                     _ -> Nothing
                     

          in case (M.null adjcons, dropWhile isNothing $ map checkNeighbour $ M.toList adjnums) of
               (True,_)        -> b -- unchanged, no concealed tiles
               (_,[])          -> b -- unchanged
               (_, (Just x:_)) -> x -- found a change to make





iterateFix f x | x == x'   = x
               | otherwise = iterateFix f x'
  where x' = f x


cheapLogic b = foldl' (\b f -> f b) b [alreadySatisfied, onlyNPossibilities]

guess b = do
  i <- randomRIO (0,width-1)
  j <- randomRIO (0,height-1)
  case M.lookup (i,j) b of
    Nothing                 -> error "Can't happen"
    Just (Tile Concealed x) -> return $ M.insert (i,j) (Tile Revealed x) b
    Just _                  -> guess b

loop b = do
  let b'  = iterateFix (subsetConceals . iterateFix cheapLogic) b
  case (correct b', complete b') of
    (False,_)     -> return $ ResultError "bad logic" b'
    (True, True)  -> return $ ResultComplete b'
    (True, False) -> do
      b'' <- guess b'
      case correct b'' of
        False -> return $ ResultError "bad guess" b''
        True  -> loop b''




-- takes a board of mines and fills in the rest with the correct numbers
enumerateBoard :: Board -> Board
enumerateBoard b = let newboard = M.fromList $ do
                         i <- [0..width-1]
                         j <- [0..height-1]
                         guard $ M.lookup (i,j) b == Nothing
                         let n = M.size $ M.filter isMine $ adjacent b (i,j)
                         return ((i,j), Tile Concealed (Num n))
                   in M.union b newboard


generate :: IO Board
generate = do
  ms <- replicateM (2*mines) generateMine
  let b = last $ unfoldr insertMine (M.empty, ms)
  return $ enumerateBoard b
 where generateMine = do
         i <- randomRIO (0, width-1)
         j <- randomRIO (0, height-1)
         return $ ((i,j), Tile Concealed Mine)
       insertMine (b, m:ms) | M.size b == mines = Nothing
                            | otherwise         = let b' = M.insert (fst m) (snd m) b
                                                  in  Just (b', (b', ms))


main = do
  b <- generate
  putStrLn (visualize (M.map clearCovered b))
  result <- loop b
  case result of
    ResultComplete b' -> putStrLn "Solved"  >> putStrLn (visualize b')
    ResultError s b'  -> putStrLn ("Mistake: " ++ s) >> putStrLn (visualize b')


visualize :: Board -> String
visualize b = unlines $ map (map (visTile . snd)) rows
  where b'   = M.toList b
        rows = map (\x -> filter ((==x).snd.fst) b') [0..height-1] -- quadratic, don't care
        visTile (Tile Revealed  Mine)    = 'X'
        visTile (Tile Revealed  (Num 0)) = ' '
        visTile (Tile Revealed  (Num n)) = head (show n)
        visTile (Tile Marked    Mine)    = '*'
        visTile (Tile Marked    _)       = '@'
        visTile (Tile Concealed _)       = 'O'


{-

1*1      
111       
11        
*1   11211
22   1*2*1
*1   22311
11   1*111
     1112*
     1113*
     1*12*
-}

{-

OOOOOOOOOO12X1  
OOOOOOOOOO*211  
OOOOOOOOOO@3221 
OOOOOOOOOO*2X*1 
OOOOOOOOOO123331
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOO3O
OOOOOOOOOOOOOOOO
OOOOOOOOOOOOOOOO

-}
