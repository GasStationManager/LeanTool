import sys
import asyncio
import subprocess
import json
from typing import Dict, Any, Optional
from litellm import completion, acompletion
import tempfile
import os
import re
import traceback

import litellm

from pbtdp import run_property_testing
from workflows import Workflows

litellm.set_verbose=True
litellm.drop_params=True

models={
  'sonnet37':'anthropic/claude-3-7-sonnet-20250219',
  'sonnet35':'anthropic/claude-3-5-sonnet-20241022',
  'sonnet':'anthropic/claude-sonnet-4-20250514',
  'opus':'anthropic/claude-opus-4-20250514',
  'qwen':'ollama/hf.co/bartowski/Qwen2.5-Coder-14B-Instruct-GGUF:IQ4_XS',
  'qwen-max':'openrouter/qwen/qwen-max',
  'qwq': 'openrouter/qwen/qwq-32b',
  'kimi-k2': 'openrouter/moonshotai/kimi-k2',
  'grok4':'xai/grok-4-0709',
  'deepseek': 'deepseek/deepseek-chat',
  'r1': 'deepseek/deepseek-reasoner',
  'deepseek-coder':'ollama/hf.co/bartowski/DeepSeek-Coder-V2-Lite-Instruct-GGUF:Q5_K_M',
  'o1-mini':'o1-mini',
  'o1':'o1',
  'o3-mini':'o3-mini',
  'o3-mini-high':'o3-mini-high',
  'o3':'o3',
  'o4-mini':'o4-mini',
  'gpt':'gpt-4o',
  'gpt45':'openai/gpt-4.5-preview-2025-02-27',
  'gemini-flash':'gemini/gemini-2.5-flash',
  'gemini-pro':'gemini/gemini-2.5-pro-preview-06-05',
  'codestral':'openrouter/mistralai/codestral-2501',
  'mistral-large':'openrouter/mistralai/mistral-large-2411'
}


class LeanToolException(Exception):
    """Custom exception for Lean tool errors"""
    pass

SYSTEM_MESSAGE_TOOLS = """You are an assistant that writes Lean 4 code. 
You have access to a tool `check_lean_code` that can pass your code to be compiled and executed by the Lean proof assistant.

You can use the tool to:
- Verify that your Lean 4 code is syntactically valid
- Run your code with test inputs and check the results 
- Utilize Lean's interative features to return suggestions and/or information that helps you complete the task
"""

SYSTEM_MESSAGE_PLAIN_TEXT = """You may invoke the tool by enclosing your Lean 4 code in <Try> ... </Try> tags, without any <Result> </Result> tags in your output.
Your code inside the <Try> tags will be executed by Lean and outputs including error messages will be shown to you in the next user message.
"""

SYSTEM_MESSAGE_LOAD_SORRY = """
If your code is syntactically correct but contains `sorry` placeholders, calling the check_lean_code tool will output goal states corresponding to each `sorry`.
"""

SYSTEM_MESSAGE_FEATURES = """
You may import libraries as needed. If you are unsure about which particular Mathlib import contains what you need, you may `import Mathlib` to import all of Mathlib.

If you get stuck trying to solve a subgoal, try some of the following. Some of these may require Mathlib.

You are free to use tactics and commands that elicit suggestions from Lean, then call check_lean_code to get the suggestions. 
- `exact?` looks for tactics/theorems that exactly closes the current goal
- `apply?` looks for tactics/theorems that may be applicable to the current goal
- `rw?` looks for rewriting tactics that are applicable at the current goal. For example:
<example>
/-- The sum of first n numbers times 2 equals n * (n+1) -/
theorem sum_first_n_times_2 (n : ℕ) :
  2 * (∑ i in Finset.range n, (i + 1)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Finset.sum_range_succ]
    rw?

And Lean will return suggestions, including `rw [Nat.left_distrib]`
</example>

- `hint` tries every tactic registered via the register_hint tac command on the current goal, and reports which ones succeed
- If you know or guess the name of a theorem, you can use `#check` to print its type, e.g. `#check Nat.zero_add`.
- `#moogle` and `#leansearch` are two search engines that can take natural language queries and return relevant theorems and tactics in Mathlib. E.g. 
<example>
example : 3 ≤ 5 := by
  #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
</example>

You may also try the following tactics for closing goals, which might not have been in your training data:
- `aesop` searches for a proof that closes the goal
- `omega` can close goals using integer and natural number arithmetic
- `simp_all` is a stronger version of `simp [*] at *` where the hypotheses and target are simplified multiple times until no simplification is applicable.
- `bv_decide` can close goals involving booleans and bit vectors
- `grind` searches for a proof using a combination of techniques and solvers
- `hammer` (after `import Hammer`) searches for a proof using built-in premise selection and then a combination of solvers
"""

SYSTEM_MESSAGE_OUTPUT="""When you have a final answer:
- If successful, output the final valid Lean code wrapped in <Result> tags
- If unsuccessful after {max_attempts} attempts, output "FAIL" followed by your best attempt wrapped in <Result> tags

Example successful output:
<Result>
theorem identity (P : Prop) : P → P :=
λ h =>  h
</Result>

Example failed output:
FAIL
<Result>
-- Best attempt, though it had errors:
theorem almost_right (P : Prop) : P → P :=
sorry  -- Could not complete proof
</Result>"""

def extract_imports(code: str):
    lines=code.splitlines(keepends=True)
    imports=[]
    rest=''
    for ln in lines:
        if ln.startswith('import'):
            imports.append(ln.split()[1])
        else:
            rest+=ln
    return imports, rest

def strip_reasoning(messages):
    return [{k:v for k,v in m.items() if k!='reasoning_content'} for m in messages]

def result_has_sorry(result):
    if isinstance(result['output'], str):
        return 'sorry' in result['output']
    else:
        for ln in result['output']:
            if 'sorry' in ln.get('data', ''): 
                return True
        return False

class LeanFeatures:
    def __init__(self):
        self.sys_msg = SYSTEM_MESSAGE_FEATURES
    async def process(self, code, result):
        return result

class LoadSorry:
    def __init__(self):
        self.sys_msg = SYSTEM_MESSAGE_LOAD_SORRY
    async def process(self, code, result):
        has_sorry =result_has_sorry(result)
        if result['success'] and has_sorry:
            print ("Plugin LoadSorry activated")
            from pantograph import Server
            imports, rest=extract_imports(code)
            print (f"Creating server. Imports: {imports}")
            server=await Server.create(imports=['Init']+imports, project_path=".")
            print(f"Server created. Loading sorrys")
            units =await server.load_sorry_async(rest)
            print("Sorrys loaded")
            states = [ u.goal_state if u.goal_state is not None or len(u.messages)==0 else 'Error extracting goal state: '+'\n'.join(u.messages) for u in units]
            output = f"\nGoal States from sorrys:\n"+"\n\n".join([str(s) for s in states if s])
            if isinstance(result['output'], str):
                result['output'] += output
            else:
                result['output'].append({'goals': output})
            server._close()
        return result


class SorryHammer:
    def __init__(self, tactic = ['omega','hammer {disableAuto := true}'], imports = 'import Hammer\n', greedy=False):
        self.tactic = tactic if isinstance(tactic, str) else "first | " + " | ".join(['('+t+')' for t in tactic])
        self.imports = imports
        self.greedy = greedy
        self.sys_msg = f"""
If the `sorry_hammer` parameter of the check_lean_code tool call is set to True,
the tool will attempt to replace the first `sorry` in your code with a proof using a hammer tactic `{self.tactic}`.
If successful, it will return the modified code in the `code` field of the result.
Alternatively, without setting the `sorry_hammer` flag, you could manually replace a `sorry` with `{self.tactic}`, after including the imports `{self.imports}` in your code.
"""
    async def process(self, code, result, try_negation=False):
        has_sorry = result_has_sorry(result)
        orig_code = code
        if result['success'] and has_sorry:
            print ("Plugin SorryHammer activated")
            if self.imports not in code:
                code = self.imports + '\n' + code
            code = code.replace('sorry', self.tactic, 1)
            new_result = await check_lean_code(code, sorry_hammer=self.greedy)
            if new_result['success']:
                print ("SorryHammer succeeded")
                output = "SorryHammer successfully replaced "
                if result_has_sorry(new_result):
                  if self.greedy:
                    output += "some sorrys, but some remain."
                  else:
                    output += "the first sorry." 
                else:
                    output += "all sorrys."
                if isinstance(result['output'], str):
                    result['output'] =  output + '\n' + new_result['output']
                else:
                    result['output']=[{'data': output}] + new_result['output']
                result['code'] = new_result.get('code', code)
            else:
                print ("SorryHammer failed")
                output = "SorryHammer failed to replace the first sorry. The following is Lean's output from the attempt:"
                if isinstance(result['output'], str):
                    result['output'] +='\n' + output + '\n' + new_result['output']
                else:
                    result['output']+=[{'data': output}] + new_result['output']
                if try_negation:
                    code = orig_code
                    if self.imports not in code:
                        code = self.imports + '\n' + code
                    code = 'import LeanTool.CheckFalse\n' + code
                    code = code.replace('sorry', f"(check_false {self.tactic})", 1)
                    cf_result = await check_lean_code(code, sorry_hammer=False)
                    if not cf_result['success']:
                        cf_out = "SorryHammer proved that the goal corresponding to the first sorry is false. The following is the proof of the negation:"
                        if isinstance(result['output'],str):
                            result['output']+='\n'+cf_out+'\n'+cf_result['output']
                        else:
                            result['output']+=[{'data':output}]+cf_result['output']
        return result


class RunTests:
  def __init__(self):
    self.tool_name = "run_tests"
    self.sys_msg="""## run_tests tool for property-based testing
You have access to a tool `run_tests` that takes Lean source code and the signature of a function you want to test, and evaluates the function with randomly-generated inputs.
Common pattern for writing run-time tests in the function: 
```
let checkRes:Bool := condition_matching_proof_goal
if !checkRes then
  IO.println "failed check: [exact condition being tested]"
return ResultType (by sorry)
```
Here `condition_matching_proof_goal` should match the goal extracted from the subsequent `sorry` when running the `check_lean_code` tool.
Then, if `condition_matching_proof_goal` evaluates to `false`, we know that for this input, the goal corresponding to the `sorry` is false, and there is likely a bug in the function's implementation.
"""

  async def tool_function(self, code: str, signature: str, num_tests: int=20):
    inputo={'function_signature':signature, 'code_solution':code}
    return await run_property_testing(inputo, num_tests=num_tests )
    
  def tool_def(self):
    return {
      "type": "function",
      "function":{
        "name": "run_tests",
        "description": "Given Lean code containing a function with the given signature, evaluate the function with randomly-generated inputs. Collect the cases with 'Error:' or 'failed check:' in their output",
        "parameters": {
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": "Lean 4 code containing definitions"
                },
                "signature": {
                    "type": "string",
                    "description": "Signature of the function to test, in parenthesis notation. E.g. 'f (a b: Nat) (c: Int)'"
                },
                "num_tests": {
                    "type": "integer",
                    "description": "number of tests to run. Default is 20"
                },
            },
            "required": ["code", "signature"]
        }
      }
    }

default_plugins=[LoadSorry(), LeanFeatures(), SorryHammer(), RunTests(), Workflows()]


async def interactive_lean_check(
    proof_request: str,
    model: str = models['sonnet'],
    temperature: float = 0.1,
    max_attempts: int = 5,
    final_check: bool = False,
    prefix: str ='',
    files =[],
    plugins = default_plugins,
    plain_text_mode = False,
    debug = False,
    messages=None,
    api_key: str = None,
    workflow = None
) -> Dict[str, Any]:
    """
    Interactively work with an LLM to generate valid Lean code, allowing for
    multiple attempts based on feedback.
    """
    if debug:
        litellm._turn_on_debug()

    if model in ['deepseek/deepseek-reasoner','gemini/gemini-2.0-flash-thinking-exp','openrouter/qwen/qwq-32b']:
        plain_text_mode=True
    SYSTEM_MESSAGE_INFO=SYSTEM_MESSAGE_TOOLS
    if plain_text_mode:
        SYSTEM_MESSAGE_INFO += SYSTEM_MESSAGE_PLAIN_TEXT
    for p in plugins:
        if isinstance(p, Workflows) and workflow:
            p.set(workflow)
        SYSTEM_MESSAGE_INFO += p.sys_msg
    if not messages: messages=[{"role": "system", "content": SYSTEM_MESSAGE_INFO+SYSTEM_MESSAGE_OUTPUT.format(max_attempts=max_attempts)}]
    elif SYSTEM_MESSAGE_INFO not in [m['content'] for m in messages]:
        sys_msgs = [m for m in messages if m['role']=='system']
        other_msgs=[m for m in messages if m['role']!='system']
        messages=sys_msgs+ [{"role": "system", "content": SYSTEM_MESSAGE_INFO}] +other_msgs

    msg=f"{proof_request}"
    if len(prefix)>0:
        msg+=f"\nThe following code is prepended to your code before execution by Lean. So when submitting your code via the tool call or final <Result> tag, only submit the part after this prefix:\n{prefix}"
    if files is not None and len(files)>0:
        for fn in files:
            with open(fn) as f:
                txt=f.read()
            messages.append({
                "role": "user",
                "content": f"The following is the conent of the file '{fn}':\n{txt}"
            })
        #prompt caching
        messages[-1]['cache_control']={'type': 'ephemeral'}
    messages = messages + [
        {"role": "user", "content": msg}
    ]
    
    tools = [create_lean_check_function()]
    tool_plugin={}
    for p in plugins:
        if hasattr(p, 'tool_def'):
            tools.append(p.tool_def())
            tool_plugin[p.tool_name] = p

    attempts = []
    try:
        supp_parallel=litellm.supports_parallel_function_calling(model=model) 
    except Exception as e:
        print (e)
        supp_parallel=False
    for attempt in range(max_attempts+1):

        try:
            kwa={}
            if not plain_text_mode:
                kwa['tools']=tools
            if api_key:
                kwa['api_key']=api_key
            if model == 'o3-mini-high':
                model='o3-mini'
                kwa['reasoning_effort']='high'
            if supp_parallel and model not in ['o3-mini', 'o1']:
                kwa['parallel_tool_calls']=False
            if model not in ['o3-mini']:
                kwa['temperature']=temperature
            response = await acompletion(
                model=model,
                messages=strip_reasoning(messages),
                **kwa
            )
            
            # Check if we have a final result

            message = response.choices[0].message
            if not message:
                return {
                    "success":False,
                    "attempts":attempts,
                    "error":response.choices[0].finish_reason,
                    "messages":messages
                }
            message_content = message.content if hasattr(message, 'content') else None
            function_call = message.tool_calls[0] if hasattr(message, 'tool_calls') and message.tool_calls else None
            if message_content and "<Result>" in message_content:
                # Extract the final result
                match = re.search(r"<Result>(.*?)</Result>", message_content, re.DOTALL)
                if match:
                    final_code = match.group(1).strip()
                    final_code = final_code.replace("```lean", "").replace("```", "")
                    if final_check:
                      # Verify the final code works
                      final_result = await check_lean_code(final_code)
                      attempts.append({
                        "code": prefix+final_code,
                        "result": final_result,
                        "is_final": True
                      })
                    messages.append(message.model_dump())
                    if "FAIL" in message_content:
                        success=False
                    else:
                        success=final_result["success"] if final_check else True

                    return {
                        "success": success,
                        "attempts": attempts,
                        "final_code": final_code,
                        "messages": messages
                    }
            
            # If we have a function call, execute it and continue the conversation
            if function_call or (plain_text_mode and message_content and '<Try>' in message_content):
                if function_call:
                    args = json.loads(function_call.function.arguments)
                else:
                    match = re.search(r"<Try>(.*?)</Try>", message_content, re.DOTALL)

                    args = {'code': match.group(1).strip()}
                if (function_call and function_call.function.name == 'check_lean_code') or plain_text_mode:
                  result = await check_lean_code(
                    code=prefix+args["code"],
                    json_output=args.get("json_output", False),
                    sorry_hammer=args.get("sorry_hammer", False),
                    try_negation=args.get("try_negation", False),
                    plugins=plugins
                  )
                
                  attempts.append({
                    "code": args["code"],
                    "result": result,
                    "thought": message_content,
                    "is_final": False
                  })
                else:
                  p=tool_plugin.get(function_call.function.name)
                  if p:
                    result = await p.tool_function(**args)

                # Add the result to the conversation
                messages.append(message.model_dump())
                #{
                #    "role": "assistant",
                #    "content": None,
                #    "function_call": {
                #        "name": "check_lean_code",
                #        "arguments": json.dumps(args)
                #    }
                #})
                if plain_text_mode:
                  output=f"Given your code, Lean outputs the following:\n{result['output']}"
                  if result['error']:
                    output+=f"\nError message:\n{result['error']}"
                  messages.append({
                    "role": "user",
                    "content": output 
                  })
                else:
                  messages.append({
                    "tool_call_id": message.tool_calls[0].id,
                    "role": "tool",
                    "name": function_call.function.name,
                    "content": json.dumps(result)
                  })
                
                continue
            
            # If we get here without a Result tag or function call, add the response
            # to continue the conversation
            messages.append({
                "role": "assistant",
                "content": message_content
            })
            if 'anthropic' in model:
                return {
                        "success": False,
                        "attempts": attempts,
                        "messages": messages
                }
            else:
                tool_ins="Enclose your code in <Try> </Try> tags" if plain_text_mode else "Call the provided tool" 
                messages.append({
                    'role': 'user',
                    'content': f"To try your code with Lean, {tool_ins}. To finish with the final answer, enclose your final code with <Result> </Result>."
                })
        except Exception as e:
            attempts.append({
                "error": str(e) + '\n' + traceback.format_exc(),
                "is_final": False
            })
            await asyncio.sleep(1)
        if 'anthropic' in model:
            await asyncio.sleep(1)
    # If we've exhausted attempts, return the history
    return {
        "success": False,
        "attempts": attempts,
        "error": f"Failed to get valid result after {max_attempts} attempts",
        "messages": messages
    }

def create_lean_check_function() -> Dict[str, Any]:
    """
    Creates the function definition for LLM function calling.
    Returns a dictionary describing the function that can be passed to LLMs.
    """
    return {
      "type": "function",
      "function":{
        "name": "check_lean_code",
        "description": "Checks Lean 4 code using the Lean 4 proof assistant",
        "parameters": {
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": "The Lean 4 code to check"
                },
                "json_output": {
                    "type": "boolean",
                    "description": "Whether to get Lean's output in JSON format. If omitted, defaults to false"
                },
                "sorry_hammer": {
                    "type": "boolean",
                    "description": "If true, the tool will attempt to replace the first `sorry` in the code with a proof using a hammer tactic. Defaults to false."
                },
                "try_negation": {
                    "type": "boolean",
                    "description": "If true, and the sorry_hammer option is true, then if the hammer tactic fails to prove the goal of the first sorry, the tool will try to prove the negation of the goal statement. Defaults to false. Do not turn this on if you are currently trying to prove a contradiction, e.g. when the goal is `False`."
                },
            },
            "required": ["code"]
        }
      }
    }


async def check_lean_code(code: str, json_output: bool = False, sorry_hammer:bool = False, try_negation:bool = False, plugins = default_plugins) -> Dict[str, Any]:
    """
    Sends code to the Lean executable and returns the results.
    
    Args:
        code: Lean code to check
        json_output: Whether to get output in JSON format
        
    Returns:
        Dictionary containing:
            - success: bool indicating if code checked successfully
            - output: string or parsed JSON containing Lean's output
            - error: string containing error message if any
    """
    try:
        # Create temporary file for the Lean code
        with tempfile.NamedTemporaryFile(suffix='.lean', mode='w', encoding='utf-8', delete=False) as temp_file:
            temp_file.write(code)
            temp_file_path = temp_file.name
        
        # Prepare command with optional JSON flag
        cmd = ['lake', 'env', 'lean']
        if json_output:
            cmd.append('--json')
        cmd.append(temp_file_path)
        
        # Run Lean on the temporary file
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True
        )
        
        # Clean up temporary file
        os.unlink(temp_file_path)
        
        # Process the output
        success = result.returncode == 0
        output = result.stdout
        
        # Parse JSON output if requested and available
        if json_output and output:
            try:
                output = [json.loads(ln) for ln in output.splitlines() if ln.strip()]
            except json.JSONDecodeError as err:
                print(f"Failed to parse Lean JSON output: {err}.\n Keeping output as string.")
        result = {
            "success": success,
            "output": output,
            "error": result.stderr if not success else None
        }
        for p in plugins:
            if hasattr(p, 'process'):
                if not isinstance(p, SorryHammer):
                    result=await p.process(code, result)
                elif sorry_hammer:
                    result=await p.process(code, result, try_negation=try_negation)
        return result

    except subprocess.CalledProcessError as e:
        raise LeanToolException(f"Error running Lean: {str(e)}")
    except Exception as e:
        raise LeanToolException(f"Unexpected error: {str(e)}")


async def main(query):
    result = await interactive_lean_check(
        query,
        model=models['sonnet'],
        temperature=0.1,
        max_attempts=5
    )
    
    print("Success:", result["success"])
    print("Number of attempts:", len(result["attempts"]))
    
    if result["success"]:
        print("\nFinal code:")
        print(result["final_code"])
    else:
        print("\nFailed to get valid code. Best attempt:")
        print(result["attempts"][-1])
        
    print("\nFull interaction history:")
    for i, attempt in enumerate(result["attempts"], 1):
        print(f"\nAttempt {i}:")
        if 'code' in attempt: print(attempt["code"])
        elif 'error' in attempt:
                print("Error:", attempt["error"])
        if "result" in attempt:
            print("Result:", attempt["result"])


if __name__=='__main__':
  asyncio.run(main(sys.argv[1:]))
