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


def main(argv: List[str]) -> None:
    # Parse the command line arguments
    gpt_file, gpt_task, outputfolder, enable_mutation = parse_args(argv)
    
    # Start
    try:
        ret, llms_query_times, total_solve_time, tokens_usage = LLMVeri_Main(gpt_file, gpt_task, outputfolder, enable_mutation)
        print("llms_query_times =", llms_query_times)
        print("total_solve_time =", total_solve_time)
        print("tokens_usage =", tokens_usage)
        print("ret =", ret)
    except Exception as e:
        print(e)
        raise e
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
    print("used time: ", endtime - starttime)
    print("@@@ Finished @@@")