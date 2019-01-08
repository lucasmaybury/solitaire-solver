module EightOff where

--------------------------------------------------------------------------------------------------------------------------------
-- Imported Modules --
--------------------------------------------------------------------------------------------------------------------------------
import System.Random
import Data.Maybe
import Data.List
import Data.Ord
import MeanStats
import Debug.Trace
import MergeSort



--------------------------------------------------------------------------------------------------------------------------------
-- Datatypes --
--------------------------------------------------------------------------------------------------------------------------------
data Pip = Ace | Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten | Jack | Queen | King deriving (Eq, Ord, Show, Enum, Bounded)
data Suit = Clubs | Diamonds | Hearts | Spades deriving (Eq, Ord, Show, Enum, Bounded)
type Card = (Pip, Suit)
type Deck = [Card]

type Reserves = [Card]
type Columns = [[Card]]
type Foundations = [Card]
type EOBoard = (Foundations, Columns, Reserves)



--------------------------------------------------------------------------------------------------------------------------------
-- Constants --
--------------------------------------------------------------------------------------------------------------------------------
pack :: Deck
pack = [ (pip, suit) | suit <- [Clubs .. Spades], pip <- [Ace .. King] ]



--------------------------------------------------------------------------------------------------------------------------------
-- Utilities --
--------------------------------------------------------------------------------------------------------------------------------
--sCard
--Returns the succesor to the passed card
sCard :: Card -> Card
sCard card@(pip,suit) = {-if(isKing card)then Nothing else-} (succ pip, suit)

--------------------------------------------------------------------------------------------------------------------------------
--pCard
--Returns the predecessor to the current card
pCard :: Card -> Card
pCard card@(pip,suit) = {-if(isAce card)then Nothing else-} (pred pip, suit)

--------------------------------------------------------------------------------------------------------------------------------
--isAce
--Returns if the card is an Ace or not
isAce :: Card -> Bool
isAce (pip, _) = pip == Ace

--------------------------------------------------------------------------------------------------------------------------------
--isKing
--Returns if the card is a King or not
isKing :: Card -> Bool
isKing (pip, _) = pip == King

--------------------------------------------------------------------------------------------------------------------------------
--succedes
--Returns whether a card is the successor of another
succedes :: Card -> Card -> Bool
succedes c1 c2 = ( (not(isAce c1))&&(c2==(pCard c1)) ) || ( (not(isKing c2))&&((sCard c2) == c1) )

--------------------------------------------------------------------------------------------------------------------------------
--getMaybe
getMaybe :: (Maybe a) -> a
getMaybe (Just x) = x

--------------------------------------------------------------------------------------------------------------------------------
-- Functions --
--------------------------------------------------------------------------------------------------------------------------------
--shuffle
--Shuffles a passed Deck of cards into a random order
shuffle :: Int -> Deck
shuffle seed = map fst ( mergesort (\(_,n1) (_,n2) -> n1<n2) (zip pack (take 52 (randoms (mkStdGen seed)):: [Int])))

--------------------------------------------------------------------------------------------------------------------------------
--eODeal
--Takes a Deck of cards, shuffles them, and deals them out into the format of an EOBoard
eODeal :: Int -> EOBoard
eODeal seed = (fnds,cols,res)  
 where  spack = shuffle seed
        cols  = [(take 6 spack), (take 6 (drop 6 spack)), (take 6 (drop 12 spack)), (take 6 (drop 18 spack)), 
                 (take 6 (drop 24 spack)), (take 6 (drop 30 spack)), (take 6 (drop 36 spack)), (take 6 (drop 42 spack))]
        fnds  = []
        res   = [spack!!48,spack!!49,spack!!50,spack!!51]
     
--------------------------------------------------------------------------------------------------------------------------------
--sortBoard
--Sorts the 3 parts of the board into order
sortBoard :: EOBoard -> EOBoard
sortBoard (fnds,cols,res) = (sort fnds, sortBy (comparing head) cols, sort res)

--------------------------------------------------------------------------------------------------------------------------------
--getSuitSize
--Returns the number of ascending, consecutive cards at the head of a list of cards
getSuitSize :: Int -> [Card] -> Int
getSuitSize s [] = s
getSuitSize s [x] = s+1
getSuitSize s (h:t@(th:_))
 | th `succedes` h = getSuitSize (s+1) t
 | otherwise = s+1

--------------------------------------------------------------------------------------------------------------------------------
--colScore
--Returns a score for a column, based on the value of the suit at the front of it
colScore :: [Card] -> Int
colScore [] = 0
colScore [x] = 1
colScore col = (getSuitSize 0 col) + (if (isKing.last) col then 10 else 0) --If king at the end, add 10 points

--------------------------------------------------------------------------------------------------------------------------------
-- Moving cards to the foundations --
--------------------------------------------------------------------------------------------------------------------------------
-- toFoundations
-- move everthing that will go to foundations
toFoundations :: EOBoard -> EOBoard
toFoundations bd = 
 toFA (reserveAcesToFoundations bd) -- because reserveAcesToFoundations is called only once

toFA :: EOBoard -> EOBoard -- called recursively till no change
toFA bd
 | bd/=cafBd = toFA cafBd
 | bd/=rtfBd = toFA rtfBd
 | bd/=chfBd = toFA chfBd
 |otherwise = bd
 where
  cafBd=(colAcesToFoundations bd) --- could trace here .. traceShow bd (colAcesToFoundations bd
  rtfBd=reserveToFoundations bd
  chfBd=colHeadsToFoundations bd
  
------------------------------------------------------------
-- reserveAcesToFoundations
-- move all aces from reserve to foundations
-- can only happen at start of game, first thing that happens,foundations must be []
reserveAcesToFoundations :: EOBoard -> EOBoard
reserveAcesToFoundations (fnds,cols,res)
 |(null fnds) = ((filter isAce res),cols,(filter (not.isAce) res)) -- composition there
 |otherwise = (fnds,cols,res)
------------------------------------------------------------
--reserveToFoundations
-- non-Aces from reserve to foundations
reserveToFoundations :: EOBoard -> EOBoard
reserveToFoundations (fnds,cols,res) = 
     ((map (\f-> (if (not (isKing f))&&(elem (sCard f) res) then (sCard f) else f)) fnds), -- update fnds
      cols,
      (filter (\r-> (not(elem (pCard r) fnds )))res))  --update res
------------------------------------------------------------
-- column aces to foundations    
colAcesToFoundations :: EOBoard -> EOBoard
colAcesToFoundations (fnds,cols,res) = 
 (fnds ++ (filter isAce colHeads),
 (filter (not.null) (map (\col -> if (isAce (head col)) then (tail col) else col) cols)),
  res)
  where
   colHeads = map head cols
------------------------------------------------------------
-- column heads to foundations
colHeadsToFoundations :: EOBoard -> EOBoard
colHeadsToFoundations (fnds,cols,res) = 
 ((map (\f-> if (not(isKing f))&&(elem (sCard f) colHeads) then (sCard f) else f) fnds), -- **f can't be king update foundations
  (filter (not.null) -- update columns
          (map (\col@(hc:rc)-> if (elem (pCard hc) fnds) then rc else col)cols)), -- may have emptied a column
  res) 
 where
  colHeads = map head cols 

--------------------------------------------------------------------------------------------------------------------------------
-- Moving between columns, other columns and reserves --
--------------------------------------------------------------------------------------------------------------------------------
--findMovesColCol
--Finds moves between columns
findMovesColCol :: EOBoard -> [EOBoard]
findMovesColCol board@(_,cols,_) = 
    filter ((\c1 (_,c2,_) -> not(c1==c2) )cols) --removes any boards where the columns stayed the same
        ( map 
            ( (\board@(fnds,cols,res) currentCol ->
                (fnds, --foundations stay the same
                filter (not.null) --filters out any empty columns
                    (newCols currentCol cols (8-(length res))), --tries to move the head card(s) from the top of the current column to another
                res) )
            board ) --pass the board into the lambda function
        cols ) --map over the head of each of the columns

--newCols
--Takes a set of columns and a single column, from which it tries to move the top card from, to another column
--Returns the same set of columns if the card can't be moved 
newCols :: [Card] -> Columns -> Int -> Columns
newCols _ [] _ = []
newCols moveCol cols freeResCells
 | (isKing.last) moveColHead = --If there's a king at the top of the cards to move
    if ((length cols)<8) && (moveColStackSize<=(freeResCells+1)) then
        moveColHead:moveColTail:(delete moveCol cols)
    else cols
 | (moveColStackSize<=(freeResCells+1)) = --If the stack can be moved all together
    let 
        baseCard = (sCard.last) moveColHead
        maybeDestinationCol = find ((==baseCard).head) cols
    in  
        if maybeDestinationCol==Nothing then cols --If there isnt anywhere to put the stack
        else let destinationCol = getMaybe maybeDestinationCol in
            moveColTail:
            (moveColHead++destinationCol):
            (filter (not.((flip elem) [moveCol,destinationCol]) ) cols)
            --Move the stack to the new column

 | otherwise = cols
 where moveColStackSize = getSuitSize 0 moveCol
       moveColHead = take moveColStackSize moveCol
       moveColTail = drop moveColStackSize moveCol
       --Splits the column into the moveable and non-moveable parts

--------------------------------------------------------------------------------------------------------------------------------
--findMovesColRes
--Finds moves between columns and reserves
findMovesColRes :: EOBoard -> [EOBoard]
findMovesColRes board@(fnds,cols,res)
 | length res == 8 = []
 | length cols == 0 = []
 | otherwise =  map (\colHead-> --for each iteration of the map, make a new EOBoard
                    (fnds, --foundations stay the same
                        (filter (not.null) --removes empty columns
                            (map --columns dont have the removed card anymore
                            ((\cardMoved col@(colh:colt)->if (colh==cardMoved) then colt else col) colHead)
                            --colHead is passed into the lambda function for comparison to each column's head
                            --if the moved card is the head card of the column, return the tail
                            --if not, return the whole column
                            cols)
                        ), 
                    colHead:res)) --Add the card to the reserves
                (map head (filter (\x-> 
                   not ( ((isKing.last) x) && ((length x)>1) && ((length x)==(getSuitSize 0 x)) )
                   --Dont consider columns that are a suit with a king at the head
                )cols)) --map over the head of each of the columns
    
--------------------------------------------------------------------------------------------------------------------------------
--findMovesResCol
--Finds moves between reserves and columns
findMovesResCol :: EOBoard -> [EOBoard]
findMovesResCol board@(fnds,cols,res)
 | length res == 0 = []
 | otherwise = 
            filter ((\c1 (_,c2,_) -> not (c1==c2) )cols) --removes any boards where the columns stayed the same (allows the reserves to change regardless of whether or not a cad has been moved)
            (   map --for each reserve card, try to move it to a column
                ((\board@(fnds,cols,res) currentRes-> 
                    if (isKing currentRes) then
                        if ((length cols)<8) then --if the head card is a king and there's an empty column
                            (fnds, [currentRes]:cols, delete currentRes res) --move the king to the empty column
                        else board
                    else --if the card isn't a king, or is a king and there aren't any empty columns
                        (   fnds, --foundations stay the same
                            (map ((\currentRes col -> --columns have the new card at the head
                                if ( (head col)==(sCard currentRes) ) then --if the card can move to the column
                                    currentRes:col --add it at the head
                                else col --if not, don't add it
                                )currentRes) --pass in the current reserve card
                                cols --iterate over the columns
                            ), 
                            delete currentRes res --the reserves don't have the moved card in it anymore
                        )
                ) board) --pass in the whole board as an argument to the lambda function
                res --map over the reserves
            )

--------------------------------------------------------------------------------------------------------------------------------
-- Search --
--------------------------------------------------------------------------------------------------------------------------------
data Tree = Empty | Node EOBoard EOBoard Int [Tree] deriving(Eq, Show)

getNodeScore (Node _ _ s _) = s

--------------------------------------------------------------------------------------------------------------------------------
--expandTree
expandTree :: Tree -> Tree
expandTree (Node board prevBoard score successors)
 | null successors = --If there are no successors, calculate them, if there arent any, set it to empty
        let newSuccessors = (map ((\prevBoard board -> Node board prevBoard (evalBoard board) []) board )
                                ( ((delete prevBoard).findMoves.toFoundations) board ) )
        in 
            if null newSuccessors then Node board prevBoard 0 newSuccessors
            else Node board prevBoard score newSuccessors
 | otherwise = Node board prevBoard (evalBoard board) (map expandTree successors)
 --Expand the node

--------------------------------------------------------------------------------------------------------------------------------
--expander
--Expand the tree 'depth' number of times
expander :: Int -> Tree -> Tree
expander depth tree
 | depth>0 = expander (depth-1) (expandTree tree)
 | otherwise = tree

--------------------------------------------------------------------------------------------------------------------------------
--findHighestScore
--Finds the highest scoring node in a given tree
findHighestScore :: Tree -> Int
findHighestScore (Node board _ _ successors)
 | null scores = 0
 | otherwise = maximum scores
 where scores = ( (map getNodeScore successors) ++ (map findHighestScore successors) )
 --Get the scores of the successors of the current node
 --Do the same for all the successsors

--------------------------------------------------------------------------------------------------------------------------------
--search
--Finds the highest value board within X moves of the current board
search :: EOBoard -> EOBoard -> Int
search prevBoard board = findHighestScore (expander 3 (Node board prevBoard 0 []))

--------------------------------------------------------------------------------------------------------------------------------
--evalBoard
--Takes a board and gives a score of how close the board is to finished
evalBoard :: EOBoard -> Int
evalBoard board@(fnds,cols,res)
 | (length fnds == 4) && (all isKing fnds) = 52000000
 | (findMoves board) == [] = 0
 | otherwise =
    (round
        (fromIntegral(
            --Number of cards in Foundations
            (1000000*(getScore board))
            +
            --Distance from a foundation-successor to the head of it's column
            (
            foldr ((-).round.((\cols col->
                let fndIndex = findIndex --If there's a card hidden in a column, find how far away it is from the head
                            ( (\foundationSuccessors x-> 
                                (isAce x) || (elem (pCard x) foundationSuccessors) )  (filter (not.isKing) fnds) )
                            col
                in 
                    (if      ((not.isNothing) fndIndex) then let index = (getMaybe fndIndex) in
                        100.0 * (fromIntegral index)
                    else 0.0)
            )cols) ) 10000 cols) --Start with 10000, subtracting every columns rating
            +
            --Number of cards stacked in the columns
            30*(foldr ((+).colScore) 0 cols)
        )
        *
        --Occupied cells in the reserves
        let freeCells = 8-(length res) in
        (if      ( freeCells <= 2 ) then 0.35 -- 0-2
         else if ( freeCells <= 4 ) then 0.7  -- 3-4
         else if ( freeCells <= 6 ) then 1.0  -- 5-6
         else                            1.5) -- 6-8
    ))

--------------------------------------------------------------------------------------------------------------------------------
--findMoves
--Takes an EOBoard and returns a list of the possible EOBoards that can be made after one move
findMoves :: EOBoard -> [EOBoard]
findMoves board = map sortBoard ( (findMovesColCol board) ++ (findMovesResCol board) ++ (findMovesColRes board) )
--Boards are sorted to that they can be checked for inequality with previous boards before being considered for another move

--------------------------------------------------------------------------------------------------------------------------------
--chooseMove
--Chooses a move from all possible moves that can be made from a board
--Takes the total game's history so it doesn't make loops
chooseMove :: [EOBoard] -> Maybe EOBoard
chooseMove boards@(currentBoard@(fnds,cols,res):prevBoards)
 | length newBoards == 0 = Nothing --If the current board has no moves to make from it
 | otherwise = Just (fst (maximumBy (comparing snd) boardScores))
 where  newBoards = filter (not.((flip elem) prevBoards)) (findMoves currentBoard) --Finds the possible new boards
        prevBoard = if (prevBoards==[]) then ([],[],[]) else head prevBoards
        boardScores = zip newBoards (map (search prevBoard) newBoards) --Scores the new boards

--------------------------------------------------------------------------------------------------------------------------------
--getScore
--Calculates the number of cards in the foundations
getScore :: EOBoard -> Int
getScore (foundations,_,_) = foldr ((+).(+1).fromEnum.fst) 0 foundations

--------------------------------------------------------------------------------------------------------------------------------
--eOGameA
--Plays a game to completion. Returns the board when it's won or lost
eOGameA :: [EOBoard] -> EOBoard
eOGameA boards@(currentBoard:prevBoards)
 | newBoard == Nothing = currentBoard
 | otherwise =  trace ((pb.sortBoard.toFoundations.getMaybe) newBoard)
                eOGameA (((sortBoard.toFoundations.getMaybe) newBoard):boards) --gets the next board,
 where newBoard = chooseMove ((toFoundations currentBoard):prevBoards)

--------------------------------------------------------------------------------------------------------------------------------
--eOGame
--Plays a game to completion. Returns a score: the number of cards which have been moved to the foundations
eOGame :: EOBoard -> Int
eOGame board = trace ((pb finalBoard)++(show (getScore finalBoard))) 
               (getScore finalBoard) 
 where finalBoard = eOGameA [toFoundations board]

--------------------------------------------------------------------------------------------------------------------------------
--eOExptA
--Collates a list of the scores recieved from a given number of eOGames
eOExptA :: RandomGen a => a -> Int -> [Int]
eOExptA seed 0 = []
eOExptA seed gamesLeft = game : (eOExptA  (snd splitSeed) (gamesLeft-1))
  where splitSeed = next seed --gets 2 random generators from the current one
        game = (eOGame(eODeal(fst splitSeed))) 

--------------------------------------------------------------------------------------------------------------------------------
--eOExpt
--Plays 100 games given an initial random seed. Returns the number of wins and the average score
eOExpt :: Int -> (Int, Float)
eOExpt seed = ( length(filter (==52) scores), --number of games won
                (fromIntegral (sum scores))/(fromIntegral (length scores)) ) --average score of all games played
  where scores = eOExptA (mkStdGen seed) 100

pb :: EOBoard -> String
pb (f,c,r) = 
    "\nFoundations  " ++ (show f) ++ 
    "\nColumns" ++ (foldr (++) "" ["\n             "++(show col) |col<-c]) ++
    "\n\nReserve      " ++ (show r) ++
    "\n------------------------------------------------------------\n"