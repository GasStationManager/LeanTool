from mcp.server.fastmcp import FastMCP
import asyncio
from typing import Dict, Any, Optional

from starlette.applications import Starlette
from mcp.server.sse import SseServerTransport
from starlette.requests import Request
from starlette.routing import Mount, Route
from mcp.server import Server
import uvicorn

from leantool import check_lean_code
from pbtdp import run_property_testing

# Create an MCP server
mcp = FastMCP("LeanTool")


@mcp.tool()
async def check_lean (code: str, json_output: bool = False, sorry_hammer: bool = False)-> Dict[str, Any]:
    """
    Sends code to the Lean executable and returns the results.
    If the code is syntactically correct but contains `sorry`s, 
    the tool will extract and output the goal state for each `sorry`.
    
    Args:
        code: Lean code to check
        json_output: Whether to get output in JSON format
        sorry_hammer: If True, the tool will attempt to replace the first `sorry` in the code with a proof using a hammer tactic.
        
    Returns:
        Dictionary containing:
            - success: bool indicating if code checked successfully
            - output: string or parsed JSON containing Lean's output
            - error: string containing error message if any
            - code: the modified code (if using sorry_hammer and the hammer was successful)
    """
    return await check_lean_code (code, json_output, sorry_hammer)

@mcp.tool()
async def run_tests (code: str, signature: str, num_tests: int=20) -> Dict[str,Any]:
    """
    Given Lean code containing a function with the given signature, evaluate the function with
    num_tests randomly-generated inputs. Collect the cases with 'Error:' or 'failed check:' in their output

    Args:
        code: Lean code containing definitions
        signature: signature of the function to test, in parenthesis notation. E.g. 'f (a b: Nat) (c: Int)'
        num_tests: number of tests to run
    Returns:
        Dictionary containing:
            - total_tests: total number of tests run
            - passed: number of tests that passed without errors
            - unknown: number of tests that were not able to finish, due to run-time exceptions
            - failed: number of tests that contains 'Error:' or 'failed check:' in its output
            - failures: list of input-output pairs that failed.
    """
    inputo={'function_signature':signature, 'code_solution':code}
    return await run_property_testing(inputo, num_tests=num_tests )

def create_starlette_app(mcp_server: Server, *, debug: bool = False) -> Starlette:
    """Create a Starlette application that can server the provied mcp server with SSE."""
    sse = SseServerTransport("/messages/")

    async def handle_sse(request: Request) -> None:
        async with sse.connect_sse(
                request.scope,
                request.receive,
                request._send,  # noqa: SLF001
        ) as (read_stream, write_stream):
            await mcp_server.run(
                read_stream,
                write_stream,
                mcp_server.create_initialization_options(),
            )

    return Starlette(
        debug=debug,
        routes=[
            Route("/sse", endpoint=handle_sse),
            Mount("/messages/", app=sse.handle_post_message),
        ],
    )


if __name__ == '__main__':

    import argparse
    
    parser = argparse.ArgumentParser(description='Run MCP server for LeanTool')
    parser.add_argument('--sse', action='store_true', help='serve via SSE')
    parser.add_argument('--host', default='0.0.0.0', help='Host to bind to')
    parser.add_argument('--port', type=int, default=8080, help='Port to listen on')
    args = parser.parse_args()
    if args.sse:
        mcp_server = mcp._mcp_server  # noqa: WPS437

        # Bind SSE request handling to MCP server
        starlette_app = create_starlette_app(mcp_server, debug=True)

        uvicorn.run(starlette_app, host=args.host, port=args.port)
    else:
        mcp.run()

