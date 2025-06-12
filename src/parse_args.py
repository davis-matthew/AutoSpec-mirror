import os, sys
import getopt
import argparse
from typing import List
from .baselib import *

current_path = os.path.dirname(os.path.abspath(__file__))
sys.path.append(os.path.dirname(os.path.dirname(current_path)))
from utils.gptcore import *

def parse_args(argv: List[str]) -> argparse.Namespace:
    # Parse the command line arguments using the getopt module
    try:
        opts, args = getopt.getopt(argv, "hvf:t:o:a:m:u", ["help", "version", "File=", "Task=", "Output=", "API_KEY=", "MODEL=", "enable_mutation"])

    except getopt.GetoptError:
        print('Error: main.py -f <File> -t <task> -o <outputfolder>')
        sys.exit(2)

    valid_model = [ "gpt-3.5-turbo",
                    "gpt-3.5-turbo-0613",
                    "gpt-3.5-turbo-16k",
                    "gpt-3.5-turbo-16k-0613",
                    "gpt-4",
                    "gpt-4-0613",
                    "gpt-4-32k",
                    "gpt-4-32k-0613",
                    "codellama-34b-instruct",
                    "CodeLlama-7B-Instruct-GPTQ",
                    "codellama-13b-instruct",
                    "codellama-7b-instruct-gptq",
                    "codeLlama-7B-GPTQ",
                    "llama2-70b-chat",
                    "llama2-13b-chat",
                    "llama2-7b-chat",
                    "llama2-7b-chat-vllm"
                    ]

    gpt_file = ""
    gpt_task = 0
    output_folder = ""
    llm_model = "gpt-3.5-turbo"
    api_key_no = 0
    enable_mutation = False

    # Process the options list into elements of a list
    for opt, arg in opts:
        if opt in ("-h", "--help"):
            print('Syntax:')
            print('\tmain.py -f <File> -t <task> -o <outputfolder> -m <model>', "\n")
            print('Options:')
            print('\t-m <model>\t', end='')
            for i in range(0, len(valid_model)):
                if i == 0:
                    print('', valid_model[i])
                else:
                    print('\t\t\t', valid_model[i])
            print('\n\t-t <task>', end='')
            print('\t 0 --> Auto')
            print('\t\t\t 3 --> Infill loop')
            print('\t\t\t 4 --> Infill contract')
            sys.exit()
        elif opt in ("-v", "--version"):
            print('version 1.0.0')
            sys.exit()
        elif opt in ("-f", "--file"):
            gpt_file = arg
        elif opt in ("-t", "--task"):
            if arg.isdigit():
                gpt_task = int(arg)
            else:
                gpt_task = arg
        elif opt in ("-o", "--output"):
            output_folder = arg
        elif opt in ("-m", "--model"):
            llm_model = arg
        elif opt in ("-u", "--enable-mutation"):
            enable_mutation = True
        elif opt in ("-a", "--api-key"):
            if arg.isdigit():
                if int(arg) > 0 and int(arg) <= int(os.environ.get('OPENAI_API_KEY_NUM')):
                    api_key_no = int(arg)
                    os.environ['OPENAI_API_KEY'] = decode_api_key(os.environ.get('OPENAI_API_KEY_' + str(api_key_no-1)).encode()).decode()
                    os.environ['BALANCE'] = os.environ.get('BALANCE_' + str(api_key_no-1))
                    # Set the environment variable to record the current api_key_no
                    os.environ['CUR_OPENAI_API_KEY_ID'] = str(api_key_no)
                else:
                    print("Invaild api_key_no")
                    sys.exit(-1)
            else:
                print("Api-key is a digit number that save in our database.")
                sys.exit(-1)

    if not llm_model in valid_model:
        print('Error: ' + llm_model + ' is not a valid model')
        sys.exit(2)

    if gpt_file == "" and gpt_task == "":
        print('Error: file is not specified, or the string is not specified')
        print('Tips: Using -h to view help')
        sys.exit(2)
    
    if output_folder == "":
        print("[DEBUG] output folder is not specified, use default 'out' folder")
        output_folder = auto_naming_output_folder(gpt_file)

    print("[DEBUG] OPENAI_API_KEY = ", os.environ.get('OPENAI_API_KEY'), "\n[DEBUG] Balance = ", os.environ.get('BALANCE'))
    print('[DEBUG] gpt_file = ', gpt_file, ', gpt_task = ', gpt_task)
    print('[DEBUG] enable_mutation = ', enable_mutation)
    print('[DEBUG] output_folder = ', output_folder)

    print('')

    # Print the arguments list, which contains all arguments that don't start with '-' or '--'
    for i in range(0, len(args)):
        print('Argument %s is: %s' % (i + 1, args[i]))
    
    return gpt_file, gpt_task, output_folder, llm_model, enable_mutation