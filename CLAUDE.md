

# Available utilities

- MCP tool check_lean that takes Lean 4 source code and checks it with the Lean executable
- pbtdp.py: command-line script, takes a filename containing Lean source code and a function signature, generate sample inputs and evaluates the function on those inputs.
  Usage: `poetry run python pbtdp.py <filename> <function signature> [--num_test=N]`


# Development workflow

- Similar to test-driven development, except that the test cases will be automatically generated 

- Start with stub implementations, with sorrys in place of proofs.

- Run the code through check_lean to verify syntax, and to extract the goals from sorrys.

- Write the checks to guard each sorry, if they don’t exist yet. Ensure that the checks matches the goals extracted from the sorrys.

- Run pbtdp.py. If errors are caught, identify which part of the code emitted the error messages, and the input that lead to the error.

- Based on the above information, improve the implementation to address that error.

- If the checks guarding a sorry passed the tests, go ahead and try to prove the goal. 
  You may try hammer tactics including `omega`, `grind`, `hammer` (after import Hammer). 
  You may also try `check_lean` with the `sorry_hammer` parameter set to true, which will try to replace the first sorry with a proof by hammer.

- Repeat the above steps, until no more errors are caught by pbtdp.py, and all `sorry`s are replaced with proofs.


# More detailed instructions and best practices

1. **MCP tool usage**
   - Use `mcp__LeanTool__check_lean` to validate Lean syntax and extract proof goals from `sorry` statements
   - Analyze the proof goals to understand what needs to be proven for each `sorry`
   - Make sure runtime checks (using `checkRes` and `IO.println` error messages) match corresponding proof goals

2. **Property-based testing with pbtdp.py**
   - Pass the complete function signature including proof arguments:
     ```
     poetry run python pbtdp.py <filename> "<function> (arg1: Type1) (arg2: Type2) (proof1: P1) (proof2: P2)" --num_test=N
     ```
   - The script handles generating test cases and proof terms for the arguments
   - Default is 5 test cases, increase with `--num_test=N` for better coverage
   - Results show passed/failed/unknown tests and details of any failures
   - The script detects both standard Lean errors and custom "failed check:" messages

3. **Process for finding and fixing mismatches**
   - Compare runtime checks (using `checkRes:Bool`) with the proof goals shown by MCP tool
   - Make sure runtime checks test exactly the same conditions as proof goals
   - Re-verify using the MCP tool after making changes
   - Run property-based testing with increased test cases to confirm correctness

4. **Runtime verification pattern**
   ```lean
   let checkRes:Bool := condition_matching_proof_goal
   if !checkRes then
     IO.println "failed check: [exact condition being tested]"
   return ResultType (by sorry)
   ```

5. **Proving strategy**
   - Start proving after implementation passes all tests
   - Use condition introduction: `if h: cond` instead of `if cond` to get conditions in proof context
   - Common effective tactics: `omega`, `linarith`, `simp`, `constructor`, `exact`
   - For complex cases, use `by_cases` to split on conditions
   - Use `rw` (rewrite) to substitute equalities in goals and hypotheses

6. **Performance optimization**
   - Remove runtime checks for proven cases to speed up testing
   - Keep runtime checks only for remaining unproven cases during development
   - Use descriptive error messages to identify which unproven case is reached

7. **Best practices**
   - Runtime checks should exactly match the proof goals from sorries
   - Error messages should clearly indicate what condition failed
   - Increase test cases when needed to ensure coverage of all code paths
   - When using dependent types, include all proof arguments in testing signatures

# Advanced workflow insights

## Handling complex proof cases
- **When a proof seems impossible**: Check if your implementation is doing the right thing
- **Algorithm logic errors**: Sometimes failed proofs indicate the algorithm logic itself needs fixing, not just the proof
- **Case analysis**: Use `by_cases h : condition` to split complex proofs into manageable subcases
- **Structural reasoning**: For recursive functions on inductive types, reason about the structure (e.g., `max` of two values)

## Successful completion indicators
- All tests pass consistently (0 failed tests)
- All `sorry` statements are replaced with complete proofs
- Runtime checks can be removed from proven cases
- `partial def` can be changed to `def` (if structurally recursive)
- Property-based testing runs efficiently without timeouts

## Common proof patterns
- **Inequality proofs**: Use `linarith` for linear arithmetic, `omega` for Presburger arithmetic
- **Equality proofs**: Use `simp` to unfold definitions, `rw` to substitute
- **Constructor proofs**: Use `constructor` to split `∧` goals, `exact` for direct proofs
- **Case analysis**: Use `match` discriminants: `match h: expr with` to get equality hypotheses
