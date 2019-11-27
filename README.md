# ProofConstructor

### How to run

1. Generate lexer by command `alex Lex.x`
2. Generate parser by command `happy Synt.y`
3. Run program by command `ghci Main.hs`

### How to use

Program checks given proposition. If it is always true, program shows the proof of this proposition. Otherwise program tries to set variables to *True* or to *False* and if the proposition becomes true, shows it's proof. Otherwise it shows :(

1. Call `main` function
2. Input the proposition
3. See the result

If proposition is always true, you can see the proof with comments for each line.

1. Call `proofWithoutHypothesis` function
2. Input the proposition
3. See the result

Unfortunately, program works only if proposition has less then 4 different variables.