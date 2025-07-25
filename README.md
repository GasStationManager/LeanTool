# LeanTool: Helping LLMs Be Better at Lean

LeanTool is a simple utility that connects LLMs with a "Code Interpreter" for [Lean](https://lean-lang.org/). This is implemented as *tool calls* from the LLM to the Lean executable, hence the name.

Current LLMs often have trouble with outputing code with correct Lean 4 syntax, due to the recent rapid changes in the Lean language and its libraries. By allowing LLMs to talk directly to Lean, 
they are given opportunities to fix their mistakes.
Furthermore, Lean being an interactive theorem prover,
there are many interactive features that are not well represented in training data. 
This utility includes some initial efforts on prompting the LLMs with instructions on using these interactive features to better produce proofs.

Our design goal is to be flexible: easy to plug into automated workflows, but can also be plugged into human-facing chat/copilot interfaces.

This is part of a broader effort to create [safe and hallucination-free coding AIs](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html). 


## Overview of Features

- Uses [LiteLLM](https://github.com/BerriAI/litellm) so you can plug in any compatible LLM, from OpenAI and Anthropic APIs to local LLMs hosted via ollama or vLLM.
- Feedback loop that allows the LLM to fix its errors.
- Uses [Pantograph](https://github.com/lenianiva/PyPantograph/) to extract goal states from `sorry`s. This facilitates breaking complex proof tasks down into simpler subtasks, e.g. [draft-sketch-prove](https://arxiv.org/abs/2210.12283).
- System prompt instructions to utilize Lean features that are likely missing from the LLMs' training data, including interactive commands that elicit suggestions / information from Lean
- Option to pass code in *plain text mode* instead of as tool calls formatted in JSON. This allows LeanTool
to be used by models that do not yet support tool/function calls, including
some reasoning models like Deepseek r1 and Gemini-2-flash-thinking.
- Plugin system to allow optional features to be included at run time.
- Flexible usage: as python library, as command-line chat interface, as OpenAI-compatible API server, or as [Model Context Protocol (MCP)](https://modelcontextprotocol.io/) server. Supports a wide range of coding assistants that can utilize custom OpenAI-compatible APIs and/or MCP servers, including Cursor, Aider, Cline, VS Code Agent Mode, Claude Code, and Gemini CLI.
- Experimental Feature: property-based testing of subgoals, now avaiable as the MCP tool `run_tests`. See [blog](https://gasstationmanager.github.io/ai/2025/05/22/alphabeta-goose.html) [posts](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html) for details.  
- Experimental Feature: the Sorry Hammer: automatically tries to prove each hole (`sorry`) with a hammer tactic ([LeanHammer](https://github.com/JOSHCLUNE/LeanHammer) by default).

## API Server Demo

A demo of the OpenAI-compatible API server is up at [http://www.codeproofarena.com:8800/v1](http://www.codeproofarena.com:8800/v1).
To use it, connect your app to the above URL as the API Base URL, "provider" as OpenAI or OpenAI-compatible,
"model" as one of the key names in the models dict in [leantool.py](https://github.com/GasStationManager/LeanTool/blob/main/leantool.py),
and API key as your API key for the chosen model. See below for specific set up details for OpenWebUI, Continue.dev, Cline and Aider.

## ProvablyCorrectVibeCoding

[http://ProvablyCorrectVibeCoding.com](http://ProvablyCorrectVibeCoding.com) is a web front end to LeanTool and [SafeVerify](https://github.com/GasStationManager/SafeVerify).  

## Installation

- Install Lean. E.g. for Linux:
```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```
- Install `poetry`
- Clone the repository
- Install [Pantograph](https://github.com/lenianiva/PyPantograph/) by following its instructions. Create the wheel file. E.g.
```
git clone --recurse-submodules https://github.com/stanford-centaur/PyPantograph.git
cd PyPantograph
uv build
```
- Modify `pyproject.toml` in the LeanTool directory, to ensure the `pantograph` entry points to the correct path and file name to the `.whl` file.
- `poetry install`
- Install Mathlib and other Lean dependencies, e.g.
```
lake exe cache get
lake update
lake build
```
- Set up your LLM model to connect via `LiteLLM`. E.g. for OpenAI, just set the environmental variable `OPENAI_API_KEY`. 
  For Anthropic, `ANTHROPIC_API_KEY`. If you want to try many different models, sign  up for an [OpenRouter](https://openrouter.ai/)
  API key and set `OPENROUTER_API_KEY`. For local models served by ollama, start by installing ollama. 
  See [Relevant LiteLLM Docs](https://docs.litellm.ai/docs/providers) for more detailed instructions. 
  The `models` dict in `leantool.py` has some preset models; it has the format "short name" : "LiteLLM model name". Modify it to have an entry for your model 
  if you have something different.

## Python Library and Built-in Interfaces

- `leantool.py` is the Python library. Simply import the file and call `interactive_lean_check` to invoke the feedback loop.
Currently used by [FormalizeWithTest](https://github.com/GasStationManager/FormalizeWithTest) autoformalization project,
and [WakingUp](https://github.com/GasStationManager/WakingUp) experiments on hallucination  detection.
- *Plugins* are optional features that users can choose to include at run time. There are a few built-in ones, but you can also implement your own and pass to the `interactive_lean_check` call. Here is a tentative interface design. A plugin is a python object that has the following members:
  - `sys_msg`: a string that will be attached to the system message
  - `async def process(self, code, result)`: a method that will be executed after the main Lean executable finishes. Takes in the LLM submitted code, and result a dict that records the results of the processing so far. The method should return the new result dict. 
- `cli_chat.py` command line chat interface. Simply run `poetry run python cli_chat.py`.
- `app.py` Streamlit chat interface.

## OpenAI-compatible Proxy Server
- `lean-api-server-flask.py` OpenAI API compatible proxy server. Can be plugged into any application that takes a OpenAI API model with custom base URL.
Can either use the API keys set in the environment variables, or take an API key token in the request,
which is then passed to the corresponding LLM.
Has been tested to work with [OpenWebUI](https://openwebui.com/), a fully featured chat interface, 
and coding assistants [Continue](https://www.continue.dev/), [Cline](https://cline.bot/), and [Aider](https://aider.chat/).


### Example Set Up with OpenWebUI

- After the Installation steps above, the following command will launch the API server at `http://localhost:8000/v1`:
```
poetry run python lean-api-server-flask.py
```

- Install [OpenWebUI](https://openwebui.com/). If you go with the docker option, you will need to install docker first.
  Since our proxy server exposes an OpenAI compatible API, you can use 
the [docker command for installing OpenWebUI with OpenAI API](https://github.com/open-webui/open-webui?tab=readme-ov-file#installation-for-openai-api-usage-only)
adding the command line option `--add-host host.docker.internal:host-gateway -e OPENAI_API_BASE_URL=http://host.docker.internal:8000/v1`
- Access OpenWebUI at [http://localhost:3000/](http://localhost:3000/).

### Example Set Up with Continue.dev

- After the API server is running, install Continue as a VS Code extension.  
- Follow the instructions [here](https://docs.continue.dev/customize/model-providers/openai)
to set up an OpenAI-compatible model by specifying an `apiBase` url.
Set the model name to be the key name of your chosen model in the models dict in `leantool.py`, e.g. "sonnet".
For the `apiKey` field you may provide your API key for the chosen model.

### Example Set Up with Cline

- Install the Cline VS Code extension.
- Set the model type to be OpenAI-compatible, and provide the base url.
Set the model name for your chosen model, e.g. "sonnet", and your API key.

### Example Set Up with Aider

- After the API server is running, install [Aider](https://aider.chat/).
- Connect to the server's models as OpenAI-compatible API models: see [instructions](https://aider.chat/docs/llms/openai-compat.html).
  E.g. for Mac/Linux:
```
export OPENAI_API_BASE=<endpoint for the API server>
export OPENAI_API_KEY=<key for your chosen model>

# Prefix the model name with openai/
aider --model openai/sonnet
```

## Model Context Protocol (MCP) Server
- `leanmcp.py` is a [Model Context Protocol (MCP)](https://modelcontextprotocol.io/) server. This exports Lean (and plugins including load_sorry) as a [MCP tool](https://modelcontextprotocol.io/docs/concepts/tools), without the LLM and the feedback loop. Works with apps that can utilize MCP servers, and are able to manage the feedback loop within the app.
  Has been tested to work with [Claude Code](https://docs.anthropic.com/en/docs/agents-and-tools/claude-code/overview), Claude Desktop, [Cursor](https://www.cursor.com/), [VS Code Agent Mode](https://code.visualstudio.com/docs/copilot/chat/chat-agent-mode), [Gemini CLI](https://github.com/google-gemini/gemini-cli), and [Goose](https://github.com/block/goose).
- Note that the MCP tool does not come with the system messages that would be integrated in the Python library mode or the OpenAI-compatible API server mode. You may want to take some of the system messages in `leantool.py` relevant to your use case, and put it in the corresponding settings for your coding assistant, e.g. `CLAUDE.md` for Claude Code or the "Rules for AI" setting in Cursor. 
- Can be run in `stdio` mode: e.g. when configuring your app for MCP, fill in the command `poetry run python leanmcp.py`
- Can also serve over the network in `sse` mode: e.g. run `poetry run python leanmcp.py --sse --port 8008`,
  then fill in the URL `http://<your-host-or-ip-address>:8008/sse` in your app's configuration.
- You can use tools like [Supergateway](https://github.com/supercorp-ai/supergateway) to convert between the two modes, in order to connect to apps that only support one mode. E.g. if you are serving the MCP server in `sse` mode, but wants Claude Desktop (which only supports `stdio`) to connect to it, you can install configure Claude Desktop's MCP with
```
{
    "mcpServers": {
        "LeanTool": {
            "command": "npx",
            "args": [
                "-y",
                "supergateway",
                "--sse",
                "<your-mcp-server>/sse"
            ]
        }
    }
}
```
  
### Example Set Up with Claude Code

- Install [Claude Code](https://docs.anthropic.com/en/docs/agents-and-tools/claude-code/overview)
- Add leanmcp.py as an mcp server. e.g. in the LeanTool repo directory:
```
claude mcp add LeanTool poetry run python leanmcp.py
poetry shell
claude  
```

### Example Set Up with Cursor
- Set up the MCP server in Cursor, see [instructions](https://docs.cursor.com/context/model-context-protocol). E.g. for `sse` mode,  run the server with `poetry run python leanmcp.py --sse --port 8008`,
  then in Cursor, go to `Cursor Settings > Features > MCP`, click on the `+ Add New MCP Server` button, and fill in the URL `http://<your-host-or-ip-address>:8008/sse`.
- Test the set up. You may want to explicitly ask the LLM to use the tool in your prompt. If needed, add additional instructions in the [Rules for AI](https://docs.cursor.com/context/rules-for-ai) setting.
- Example test prompt: "State a theorem in Lean 4 that n*(n+1) is even, for all natural numbers n. Write `sorry` in place of the proof. Pass the code to the provided tool to check for syntax, and show me its output". Cursor will show the MCP tool call; you may need to click the `Run tool` button to approve the call.
- If a MCP tool call hangs, try restarting Cursor. This is potentially related to the issue documented [here](https://github.com/modelcontextprotocol/python-sdk/issues/423) and [here](https://github.com/getcursor/cursor/issues/2998).
