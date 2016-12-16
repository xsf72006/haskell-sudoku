-- @2016.12
-- Author: Shaofeng XU
-- Sudoku Solver

-- Reference: 
-- Bird R. Functional pearl: A program to solve sudoku[J]. Journal of Functional Programming, 2006, 16(06): 671-679.

module Solver (
  easy, gentle, diabolical, unsolvable, minimal, empty, -- Examples
  solve, correct, -- Methods
  Board -- Board
) where

import Data.List

-- New type definitions
type Matrix a = [[a]]
type Board = Matrix Char

-- Default definitions
boardsize :: Int
boardsize = 9

boxsize :: Int
boxsize = 3

cellvals :: [Char]
cellvals = "123456789"

-- Cell check methods
blank :: Char -> Bool
blank = (== '.')

single :: [a] -> Bool
single [_] = True
single _ = False

-- Validity checking
correct :: Board -> Bool
correct g = all nodups (rows g) &&
            all nodups (cols g) &&
            all nodups (boxs g)

nodups :: Eq a => [a] -> Bool
nodups [] = True
nodups (x:xs) = not (elem x xs) && nodups xs

-- Get rows, columns and boxes
rows :: Matrix a -> Matrix a
rows = id

cols :: Matrix a -> Matrix a
cols = transpose

boxs :: Matrix a -> Matrix a
boxs =  unpack . map cols . pack
        where
          pack   = split . map split
          split  = chop boxsize
          unpack = map concat . concat

chop :: Int -> [a] -> [[a]]
chop n [] = []
chop n xs = take n xs : chop n (drop n xs)

-- Unfold Matrix
type Choices = [Char]

choices :: Board -> Matrix Choices
choices = map (map choose)

choose :: Char -> [Char]
choose e = if blank e then cellvals else [e]

collapse :: Matrix [a] -> [Matrix a]
collapse = cp . map cp

cp :: [[a]] -> [[a]]
cp [] = [[]]
cp (xs:xss) = [y:ys | y <- xs, ys <- cp xss]

-- Pruning
prune :: Matrix Choices -> Matrix Choices
prune = pruneBy boxs . pruneBy cols . pruneBy rows
        where pruneBy f = f . map reduce . f

reduce :: [Choices] -> [Choices]
reduce xss = [xs `minus` singles | xs <- xss]
             where singles = concat (filter single xss)

minus :: Choices -> Choices -> Choices
xs `minus` ys = if single xs then xs else xs \\ ys

-- Properties of matrices
blocked :: Matrix Choices -> Bool
blocked m = void m || not (safe m)

void :: Matrix Choices -> Bool
void = any (any null)

safe :: Matrix Choices -> Bool
safe cm = all consistent (rows cm) &&
          all consistent (cols cm) &&
          all consistent (boxs cm)

consistent :: [Choices] -> Bool
consistent = nodups . concat . filter single

-- Main
solve  :: Board -> [Board]
solve  = search . prune . choices

search :: Matrix Choices -> [Board]
search m
 | blocked m = []
 | all (all single) m = collapse m
 | otherwise = [g | m' <- expand m
                  , g  <- search (prune m')]

expand :: Matrix Choices -> [Matrix Choices]
expand m = [rows1 ++ [row1 ++ [c] : row2] ++ rows2 | c <- cs]
            where
              (rows1,row:rows2) = break (any (not . single)) m
              (row1,cs:row2)    = break (not . single) row

-- Some Examples
easy                  :: Board
easy                  =  ["2....1.38",
                          "........5",
                          ".7...6...",
                          ".......13",
                          ".981..257",
                          "31....8..",
                          "9..8...2.",
                          ".5..69784",
                          "4..25...."]

gentle                :: Board
gentle                =  [".1.42...5",
                          "..2.71.39",
                          ".......4.",
                          "2.71....6",
                          "....4....",
                          "6....74.3",
                          ".7.......",
                          "12.73.5..",
                          "3...82.7."]

diabolical            :: Board
diabolical            =  [".9.7..86.",
                          ".31..5.2.",
                          "8.6......",
                          "..7.5...6",
                          "...3.7...",
                          "5...1.7..",
                          "......1.9",
                          ".2.6..35.",
                          ".54..8.7."]

unsolvable            :: Board
unsolvable            =  ["1..9.7..3",
                          ".8.....7.",
                          "..9...6..",
                          "..72.94..",
                          "41.....95",
                          "..85.43..",
                          "..3...7..",
                          ".5.....4.",
                          "2..8.6..9"]

minimal               :: Board
minimal               =  [".98......",
                          "....7....",
                          "....15...",
                          "1........",
                          "...2....9",
                          "...9.6.82",
                          ".......3.",
                          "5.1......",
                          "...4...2."]

empty :: Board
empty = replicate n (replicate n '.')
          where n = boxsize ^ 2