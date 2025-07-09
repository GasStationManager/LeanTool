from flask import Flask, request, jsonify, Response
import asyncio
from leantool import interactive_lean_check, models
import json
import io
from datetime import datetime
from functools import partial
import sys

app = Flask(__name__)

def get_api_key(request):
    """Extract API key from request headers"""
    auth_header = request.headers.get('Authorization')
    if not auth_header:
        print("No Authorization header")
        return None

    # Handle 'Bearer <key>' format
    parts = auth_header.split()
    if len(parts) == 2 and parts[0].lower() == 'bearer':
        return parts[1]
    elif len(parts) == 1:
        return parts[0]
    
    raise ValueError("Invalid Authorization header format")

def create_chat_completion_response(result, verbose=True):
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
    
    if assistant_msgs[-1].get("tool_calls",None):
        out_msg = {"role": 'assistant', 'content': ''} 
    else:
        out_msg = assistant_msgs[-1]


    if verbose:
            attf=io.StringIO()
            if len(result['attempts'])>0: print("\nAttempts:",file=attf)
            for i, attempt in enumerate(result["attempts"], 1):
                print(f"\nAttempt {i}:",file=attf)
                if "thought" in attempt and attempt['thought']:
                    print("Thought:\n"+attempt['thought'],file=attf)
                if "code" in attempt and attempt['code']:
                    print("Code:",file=attf)
                    print("```\n"+attempt["code"]+"\n```\n",file=attf)
                    if "result" in attempt and attepmt['result']:
                        print("Success:", attempt["result"]["success"], file=attf)
                        print("Output:", attempt["result"]["output"], file=attf)
                        if attempt["result"]["error"]:
                            print("Error:", attempt["result"]["error"], file=attf)
                elif "error" in attempt:
                    print("Error:", attempt["error"],file=attf)

            out_msg['content']=str(attf.getvalue())+out_msg.get('content', '')
    elif out_msg['content']=='': out_msg['content'] = assistant_msgs[-1]['content']

    print (out_msg)
    
    response = {
        "id": f"chatcmpl-{datetime.now().strftime('%Y%m%d%H%M%S')}",
        "object": "chat.completion",
        "created": int(datetime.now().timestamp()),
        "model": request.json.get("model", "default"),
        "choices": [
            {
                "index": 0,
                "message": out_msg,
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
        # Get API key first
        try:
            api_key = get_api_key(request)
        except ValueError as e:
            return jsonify({
                "error": {
                    "message": str(e),
                    "type": "authentication_error",
                    "code": 401
                }
            }), 401
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
            messages=messages[:-1],  # Pass previous messages for context
            api_key=api_key
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
    port = sys.argv[1] if len(sys.argv)>1 else 8000
    app.run(host="0.0.0.0", port=port, debug=True)
