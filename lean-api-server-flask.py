from flask import Flask, request, jsonify, Response
import asyncio
from leantool import interactive_lean_check, models
import json
from datetime import datetime
from functools import partial

app = Flask(__name__)

def create_chat_completion_response(result):
    """Convert lean tool result into OpenAI-compatible response format"""
    if not result.get("messages"):
        return {
            "error": {
                "message": "No messages in result",
                "type": "internal_error",
                "code": 500
            }
        }
    
    # Get the last assistant message
    assistant_msgs = [m for m in result["messages"] if m["role"] == "assistant"]
    if not assistant_msgs:
        return {
            "error": {
                "message": "No assistant response in result",
                "type": "internal_error",
                "code": 500
            }
        }
    
    last_assistant_msg = assistant_msgs[-1]
    print (last_assistant_msg)
    
    response = {
        "id": f"chatcmpl-{datetime.now().strftime('%Y%m%d%H%M%S')}",
        "object": "chat.completion",
        "created": int(datetime.now().timestamp()),
        "model": request.json.get("model", "default"),
        "choices": [
            {
                "index": 0,
                "message": last_assistant_msg,
                "finish_reason": "stop"
            }
        ],
        "usage": {
            "prompt_tokens": -1,  # We don't track these
            "completion_tokens": -1,
            "total_tokens": -1
        }
    }
    
    return response


def generate_streaming_response(final_response, model):
    yield "data: " + json.dumps({
            "choices": [{"delta": {"content": final_response, "role": "assistant"}, "index": 0, "finish_reason": "stop"}],
            "model": model,
    }) + "\n\n"

    # Yield the final message to indicate the stream has ended
    yield "data: [DONE]\n\n"

@app.route("/v1/chat/completions", methods=["POST"])
def chat_completions():
    try:
        data = request.json
        
        if not data:
            return jsonify({
                "error": {
                    "message": "No JSON data provided",
                    "type": "invalid_request_error",
                    "code": 400
                }
            }), 400
        
        # Extract required fields
        messages = data.get("messages", [])
        if not messages:
            return jsonify({
                "error": {
                    "message": "No messages provided",
                    "type": "invalid_request_error",
                    "code": 400
                }
            }), 400
        
        # Get model from request or use default
        model = data.get("model", "sonnet")
        if model not in models:
            model = "sonnet"  # Default to sonnet if unknown model
            
        # Extract other parameters
        temperature = data.get("temperature", 0.1)
        max_attempts = data.get("max_attempts", 5)
        
        # Create event loop and run async function
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        
        result = loop.run_until_complete(interactive_lean_check(
            proof_request=messages[-1]["content"],
            model=models[model],
            temperature=temperature,
            max_attempts=max_attempts,
            messages=messages[:-1]  # Pass previous messages for context
        ))
        
        stream = data.get("stream", False)
        # Convert result to OpenAI format
        response = create_chat_completion_response(result)
        
        if "error" in response:
            return jsonify(response), 500
        if stream:
            return Response(generate_streaming_response(response['choices'][0]['message']['content'],model), content_type='text/event-stream')
            
        return jsonify(response)
        
    except Exception as e:
        import traceback
        print("Error:", str(e))
        print("Traceback:", traceback.format_exc())
        return jsonify({
            "error": {
                "message": str(e),
                "type": "internal_error",
                "code": 500,
                "traceback": traceback.format_exc()
            }
        }), 500

@app.route("/v1/models", methods=["GET"])
def list_models():
    """OpenAI-compatible endpoint to list available models"""
    model_list = []
    for model_id, full_name in models.items():
        model_list.append({
            "id": model_id,
            "object": "model",
            "created": 1677610602,  # placeholder timestamp
            "owned_by": "local",
            "permission": [],
            "root": full_name,
            "parent": None,
            "context_window": 100000,  # placeholder value
            "messages_supported": True,
            "tools_supported": True,
        })

    return jsonify({
        "object": "list",
        "data": model_list
    })

@app.route("/v1/models/<model_id>", methods=["GET"])
def get_model(model_id):
    """Get information about a specific model"""
    if model_id not in models:
        return jsonify({
            "error": {
                "message": f"Model '{model_id}' not found",
                "type": "invalid_request_error",
                "code": 404
            }
        }), 404

    return jsonify({
        "id": model_id,
        "object": "model",
        "created": 1677610602,  # placeholder timestamp
        "owned_by": "local",
        "permission": [],
        "root": models[model_id],
        "parent": None,
        "context_window": 100000,  # placeholder value
        "messages_supported": True,
        "tools_supported": True,
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000, debug=True)
