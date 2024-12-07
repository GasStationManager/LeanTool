# LeanTool

This is a simple utility to arm LLMs with a "Code Interpreter" for Lean. Uses [LiteLLM](https://github.com/BerriAI/litellm) so you can plug in any compatible LLM, from OpenAI and Anthropic APIs to local LLMs hosted via ollama or vLLM.

Currently used by [FormalizeWithTest](https://github.com/GasStationManager/FormalizeWithTest) autoformalization project.

- `leantool.py` Python library
- `cli_chat.py` simple command line chat interface
- `app.py` Streamlit chat interface
