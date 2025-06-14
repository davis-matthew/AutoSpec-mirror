#!/usr/bin/env python3
# -*- coding: UTF-8 -*-

import os, sys
import datetime
from typing import List
from src.parse_args import *
from src.llmveri import *
from src.baselib import *

current_path = os.path.dirname(os.path.abspath(__file__))
sys.path.append(os.path.dirname(current_path))
from conf.jsoninfo import *
load_json_config(True)

MAX_ITERATION_TIMES = 5

def main(argv: List[str]) -> None:
    # Parse the command line arguments
    gpt_file, gpt_task, _, llm_model, enable_mutation = parse_args(argv)
    
    # whether file exits
    pickleFile = gpt_file+'.pickle'
    if os.path.exists(pickleFile):
        # Load the pickle
        with open(gpt_file + ".pickle", "rb") as data:
            SAVE_PICKLE = pickle.load(data)
            if SAVE_PICKLE['Status'] == 0:
                os.remove(pickleFile)
            else:
                pass

    # Start
    iteration_times = 0
    llms_query_times = datetime.timedelta(0)
    total_solve_time = datetime.timedelta(0)
    tokens_usage = 0
    
    for i in range(MAX_ITERATION_TIMES):
        try:
            outputfolder = auto_naming_output_folder(gpt_file, False)
            ret, cur_query_times, cur_solve_time, cur_tokens_usage = LLMVeri_Main(gpt_file, gpt_task, outputfolder, llm_model, enable_mutation)
            iteration_times = iteration_times + 1
            llms_query_times = llms_query_times + cur_query_times
            total_solve_time = total_solve_time + cur_solve_time
            tokens_usage = tokens_usage + cur_tokens_usage
            if ret == True:
                break
        except Exception as e:
            print(e)
            raise e
    
    print("llms_query_times =", llms_query_times)
    print("total_solve_time =", total_solve_time)
    print("tokens_usage =", tokens_usage)
    print("@@@", iteration_times, "@@@")
    # End


if __name__ == "__main__":
    starttime = datetime.datetime.now()
    for i in range(0, len(sys.argv)):
        if '--enable-mutation' == sys.argv[i]:
            sys.argv[i] = '-u'
            break
    main(sys.argv[1:])
    endtime = datetime.datetime.now()
    print("\nstart time: ", starttime)
    print("end time: ", endtime)
    print("@@@ Finished @@@")