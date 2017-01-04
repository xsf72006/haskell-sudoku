# A Sudoku Game based on Haskell
### Installation(Ubuntu 16.04 LTS)
1. Install Haskell Platform
```
sudo apt-get install haskell-platform
```

2. Install Haste Compiler
```
cabal update
cabal install haste-compiler
haste-boot
```

3. Compile Haskell File
```
cd <path-to-project>/Src/
hastec Sudoku.hs
```

4. Run index.html

### Reference
Sudoku Sover Algorithm:
* Bird R. Functional pearl: A program to solve sudoku[J]. Journal of Functional Programming, 2006, 16(06): 671-679. [[pdf](dl.acm.org/citation.cfm?id=1180089)]

Haste GUI reference:
https://github.com/emilv/sudoku/

