from mcp.server.fastmcp import FastMCP
import asyncio
from typing import Dict, Any, Optional

from starlette.applications import Starlette
from mcp.server.sse import SseServerTransport
from starlette.requests import Request
from starlette.routing import Mount, Route
from mcp.server import Server
import uvicorn

from leantool import check_lean_code  # relative import via package root

# Create an MCP server
mcp = FastMCP("LeanTool")


@mcp.tool()
async def check_lean(code: str, json_output: bool = False) -> Dict[str, Any]:
    """Check Lean code by delegating to `check_lean_code`."""

    return await check_lean_code(code, json_output)


def create_starlette_app(mcp_server: Server, *, debug: bool = False) -> Starlette:
    """Create a Starlette app exposing the MCP server via Server-Sent Events."""

    sse = SseServerTransport("/messages/")

    async def handle_sse(request: Request) -> None:  # noqa: D401 – imperative handler
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


def main() -> None:
    """Entry-point used by `python -m leantool.leanmcp` and the console script."""

    import argparse

    parser = argparse.ArgumentParser(description="Run MCP server for LeanTool")
    parser.add_argument("--sse", action="store_true", help="serve via SSE")
    parser.add_argument("--host", default="0.0.0.0", help="Host to bind to")
    parser.add_argument("--port", type=int, default=8080, help="Port to listen on")
    args = parser.parse_args()

    if args.sse:
        mcp_server = mcp._mcp_server  # noqa: WPS437

        # Bind SSE request handling to MCP server
        starlette_app = create_starlette_app(mcp_server, debug=True)

        uvicorn.run(starlette_app, host=args.host, port=args.port)
    else:
        mcp.run()


if __name__ == "__main__":
    main()
