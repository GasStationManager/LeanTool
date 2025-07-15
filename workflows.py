
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

WORKFLOW_DEFS = {
  'basic_fixing': BASIC_FIXING,
  'draft_sketch_prove': DRAFT_SKETCH_PROVE,
}

class Workflows:
    def __init__(self, workflow='basic_fixing'):
        self.sys_msg=WORKFLOW_INIT + WORKFLOW_DEFS.get(workflow, BASIC_FIXING)
