#!/usr/bin/env python3
# -*- coding: UTF-8 -*-

import os
import re
from threading import Lock, Thread
from time import sleep
from ollama import Client, Options

AUTOSPEC_LLM_PORTS = [int(x) for x in os.environ['AUTOSPEC_LLM_PORTS'].split(',')]
AUTOSPEC_LLM_MODEL = os.environ['AUTOSPEC_LLM_MODEL']
AUTOSPEC_LLM_N_CTX = int(os.environ['AUTOSPEC_LLM_N_CTX'])
AUTOSPEC_LLM_SUPPORTS_SYSTEM = int(os.environ['AUTOSPEC_LLM_SUPPORTS_SYSTEM']) != 0
AUTOSPEC_LLM_TIMEOUT = int(os.environ['AUTOSPEC_LLM_TIMEOUT'])
AUTOSPEC_LLM_INSTANCES = len(AUTOSPEC_LLM_PORTS)

def load_llm():
    def _load(port):
        while True:
            try:
                Client(host="http://127.0.0.1:" + str(port)).chat(
                    model=AUTOSPEC_LLM_MODEL,
                    options=Options(num_ctx=AUTOSPEC_LLM_N_CTX),
                    messages=[{"role": "user", "content": "1 + 1?" }],
                    keep_alive="-1m",
                )
                break
            except:
                pass
    ts = []
    for port in AUTOSPEC_LLM_PORTS:
        t = Thread(target=_load, args=(port,))
        t.start()
        ts.append(t)
    for t in ts:
        t.join()

def replace_excessive_backticks(text):
    return re.sub(r'`{4,}', '```', text)

# Note: this was not modified to simplify source (like we did for # of tokens or OpenAI stuff. This is as-is from the original work)
def find_best_reply_content(reply_list):
    best_reply = reply_list[0]
    return best_reply

def convert_to_ollama_chat(messages):
    result = messages[::]
    if AUTOSPEC_LLM_SUPPORTS_SYSTEM:
        return result
    for i, msg in enumerate(result):
        if msg['role'] == 'system':
            result[i]['role'] = 'user'
    return result

class BaseChatClass:
    def __init__(self, conversation_list=None, continuous_talking=True) -> None:
        self.conversation_list = [] if conversation_list is None else conversation_list
        self.continuous_talking = continuous_talking
        self.clients = [Client(host="http://127.0.0.1:" + str(port), timeout=AUTOSPEC_LLM_TIMEOUT) for port in AUTOSPEC_LLM_PORTS]

    def get_response(self, prompt, temperature_arg=0.7, n_choices=1):
        self.conversation_list.append({"role":"user", "content":prompt})
        conversation = convert_to_ollama_chat(self.conversation_list)
        if len(self.clients) == 1:
            responses = []
            for _ in range(n_choices):
                try:
                    responses.append(replace_excessive_backticks(self.clients[0].chat(
                        model=AUTOSPEC_LLM_MODEL,
                        options=Options(temperature=temperature_arg, num_ctx=AUTOSPEC_LLM_N_CTX),
                        messages=conversation,
                        keep_alive="-1m",
                    )["message"]["content"]))
                except Exception as e:
                    print(e)
        elif n_choices <= len(self.clients):
            responses = [None for _ in range(n_choices)]
            def exec1(client, idx):
                try:
                    responses[idx]= replace_excessive_backticks(client.chat(
                        model=AUTOSPEC_LLM_MODEL,
                        options=Options(temperature=temperature_arg, num_ctx=AUTOSPEC_LLM_N_CTX),
                        messages=conversation,
                        keep_alive="-1m",
                    )["message"]["content"])
                except Exception as e:
                    print(e)
            ts = []
            for i in range(n_choices):
                t = Thread(target=exec1, args=(self.clients[i], i))
                t.start()
                ts.append(t)
            for t in ts:
                t.join()
            responses = [x for x in responses if x is not None]
        else:
            raise NotImplementedError() 
        if len(responses) > 0:
            if self.continuous_talking:
                self.conversation_list.append({"role": "assistant", "content": find_best_reply_content(responses)})
        else:
            self.conversation_list.pop()
        return list(set(responses)), 0
