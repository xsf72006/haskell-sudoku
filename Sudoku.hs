-- @2016.12
-- Author: Shaofeng XU
-- Sudoku JS by Haste
-- Reference: https://github.com/emilv/sudoku

module Main (main) where

import Haste
import Haste.DOM
import Haste.Events
import qualified Solver
import Data.List
import Data.Maybe
import Data.Char

type Puzzle = (String, Solver.Board) -- Example Puzzles

puzzles :: [Puzzle]
puzzles = [("Easy", Solver.easy),
           ("Gentle", Solver.gentle),
           ("Diabolical", Solver.diabolical),
           ("Unsolvable", Solver.unsolvable),
           ("Minimal", Solver.minimal),
           ("Empty", Solver.empty)
          ]

main :: IO ()
main = do showExamples $ zip [0..] puzzles
          return ()

-- Initialize Examples

showExamples :: [(Int, Puzzle)] -> IO ()
showExamples pz = do mapM_ addExmpBtn pz
                     Just selector <- elemById "selector"
                     Just solve <- elemById "solve"
                     Just check <- elemById "check"
                     onEvent solve Click
                       (\_ -> do board <- readBoard
                                 showSolution board)

                     onEvent check Click
                       (\_ -> do board <- readBoard
                                 checkSolution board)

                     return ()


addExmpBtn :: (Int, Puzzle) -> IO ()
addExmpBtn (id, p@(name, tpl)) = do c <- newElem "button"
                                    Just parent <- elemById "selector"
                                    setProp c "value" $ show id
                                    setClass c "btn" True
                                    setClass c "btn-default" True

                                    onEvent c Click $ \_ ->
                                     (do v <- getProp c "value"
                                         createPuzzle $ puzzles !! (strToInt v))

                                    createPuzzle $ puzzles !! 0
                                    appendChild parent c
                                    label <- newTextElem name
                                    appendChild c label

createPuzzle :: Puzzle -> IO ()
createPuzzle p@(_, board) = do Just puzzle <- elemById "puzzle"
                               clearChildren puzzle
                               makeBoard puzzle board
                               reset <- button "Reset"
                               onEvent reset Click 
                                  (\_ -> createPuzzle p)
                               return ()
                            where
                              button :: String -> IO Elem
                              button label = do Just controls <- elemById "controls"
                                                oldReset <- elemById (map toLower label)
                                                case oldReset of
                                                  Nothing -> return ()
                                                  Just btn -> deleteChild controls btn
                                                b <- newElem "button"
                                                setProp b "id" (map toLower label)
                                                setClass b "btn" True
                                                setClass b "btn-default" True
                                                btnText <- newTextElem label
                                                appendChild b btnText
                                                appendChild controls b
                                                return b


-- Check Board

checkSolution :: Solver.Board -> IO ()
checkSolution board = do if (any (any (=='.')) board)
                          then alert $ "Please complete the board"
                          else if (Solver.correct board)
                                then alert $ "Good job!"
                                else alert $ "Wrong Answer!"
                         return ()

showSolution :: Solver.Board
             -> IO ()
showSolution board = do
                      solution <- return (Solver.solve board)
                      if null solution
                        then alert $ "No Solution!"
                        else do
                              Just puzzle <- elemById "puzzle"
                              clearChildren puzzle
                              makeBoard puzzle (head solution)
                      return ()

-- Get Board

readBoard :: IO Solver.Board
readBoard = mapM (\x -> x) [mapM readOne idRow | idRow <- (split 9 [1..81])]


readOne :: Int -> IO Char
readOne id = do Just e <- elemById ("i"++(show id))
                q <- getProp e "value"
                (s:_) <- return (if null q then "." else q)
                return s

-- Util

strToInt :: String -> Int
strToInt "" = 0
strToInt x = read x

-- Make Table

makeBoard :: Elem -> Solver.Board -> IO()
makeBoard p board = mapM_ (setrow p) (zip (split 9 [1..81]) board)

split :: Int -> [a] -> [[a]]
split _ [] = []
split n l = let (h, t) = splitAt n l
            in  h : split n t

-- Add <tr>
setrow :: Elem -> ([Int], [Char]) -> IO ()
setrow p (ids, values) = do tr <- newElem "tr"
                            mapM_ (setCell addCellClass tr) (zip ids values)
                            appendChild p tr


-- Add <td>
setCell :: (Int -> String) -> Elem -> (Int, Char) -> IO ()
setCell classes tr (id, value) =
   do input <- newElem "input"
      td <- newElem "td"
      setProp input "id" ("i" ++ (show id))
      setProp input "value" (if value /= '.' then [value] else "")
      setAttr input "maxlength" "1"
      setAttr input "onkeypress" "return event.charCode >= 48 && event.charCode <= 57"
      setProp td "className" (classes id)
      appendChild td input
      appendChild tr td

addCellClass :: Int -> String
addCellClass id = 
  let
      x = ((id - 1) `mod` 9) + 1
      y = ((id - 1) `div` 9) + 1

      checkline :: Int -> String -> [String]
      checkline x cl = (if x < 9 && x `mod` 3 == 0 then [cl] else [])
  in  intercalate " " (["cell"] ++ (checkline x "r") ++ (checkline y "d"))
