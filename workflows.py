
WORKFLOW_INIT="""## WORKFLOW

Follow these steps when solving the task:
"""

BASIC_FIXING="""
1. Write initial code based on the request
2. Invoke the check_lean_code tool to verify it
3. If there are errors, analyze them and make modifications
4. Continue this loop until either:
   - The code is valid
   - You determine you cannot fix the issues
"""

DRAFT_SKETCH_PROVE="""
1. Start with an informal proof sketch.
2. Translate into a formal proof sketch in Lean, containing `sorry` placeholders.
3. Call check_lean_code. If your code is syntactically correct, the tool will output goal states corresponding to each `sorry`
4. Replace a `sorry` with a proof or a more refined proof sketch. Call check_lean_code to verify.
5. For small proof goals, you may try hammer tactics including `grind`, or invoke check_lean_code with the parameter `sorry_hammer` set to true.
6. Repeat until the code is complete with no `sorry` left
"""

CODE_TEST_PROVE="""
This workflow is similar to test-driven development, except that the test cases will be automatically generated. 

1. Embed the specification in the function signature. In particular, preconditions can be encoded as input arguments, and postconditions via subtyping the return type. This will be the function we implement.
2. Start with stub implementations, with `sorry`s in place of proofs.
3. Run the code through check_lean_code to verify syntax, and to extract the goals from sorrys.
4. Write the checks to guard each sorry, if they don’t exist yet. Ensure that the checks match the goals extracted from the sorrys.
5. Call the run_tests tool. If errors are caught, identify which part of the code emitted the error messages, and the input that lead to the error.
6. Based on the above information, improve the implementation to address that error. Whenever you change the implementation, you will need to update the checks (go to Step 3).
7. If the checks guarding a `sorry` passed the tests, and the tests emit no errors other than for known stubs, go ahead and try to prove the goal. For small goals, you may try hammer tactics including `omega`, `grind`; or calling `check_lean_code` with the `sorry_hammer` parameter set to true, which will try to replace the first sorry with a proof by hammer.
8. For more complicated goals: extract the goal state from the `sorry` (by calling check_lean_code), and formulate an informal proof sketch. Then turn it into a formal proof sketch in Lean with sorry placeholders, and recursively solve each sorry.
8. If your proof attempt fails: analyze the error messages. Does your informal proof sketch still work, given the new information? If so, keep trying to address the errors and iterate. If you believe your informal sketch might not work, perhaps the implementation is incorrect. Check the implementation again, or try running more tests by calling run_tests again.
9. Repeat the above steps, until no more errors are caught by `run_tests`, and all `sorry`s are replaced with proofs.
10. If the original specification is in the form of separate function signature and theorem statements, fill in the body of the original function with a call to the implementation,
and prove the theorem statements by making use of the return type of the implementation. 
"""


WORKFLOW_DEFS = {
  'basic_fixing': BASIC_FIXING,
  'draft_sketch_prove': DRAFT_SKETCH_PROVE,
  'code_test_prove': CODE_TEST_PROVE, 
}

class Workflows:
    def __init__(self, workflow='basic_fixing'):
        self.set(workflow)
    def set(self,workflow):
        self.workflow=workflow
        self.sys_msg=WORKFLOW_INIT + WORKFLOW_DEFS.get(workflow, BASIC_FIXING)
