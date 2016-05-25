#!/usr/bin/env python

import argparse
import glob
import json
import os
import os.path
import random
import re
import socket
import subprocess
import time

args = None
descr = """Run provers on files and return results in JSON format. Currently
only z3 supported (hence the name)"""


def parse_arguments():
    global args
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument('files', metavar='F', nargs='+',
                        help='file or directory to be run on')
    parser.add_argument('-j', dest='parallel', type=int, action='store',
                        default=1,
                        help='number of processes to run in parallel')
    parser.add_argument('-o', dest='output', action='store',
                        default=None,
                        help='file to dump results to, stdout if absent')
    parser.add_argument('-v', dest='verbose', action='store_true',
                        help='print number of remaining VCs on stdout')
    parser.add_argument('-t', dest='timeout', type=int, action='store',
                        default=None,
                        help='timeout to be used, no timeout if not used')
    parser.add_argument('--limit', dest='limit', type=int, action='store',
                        default=None, metavar='N',
                        help='randomly select N files from all files')
    args = parser.parse_args()


def z3_cmd():
    result = ["z3", "-st"]
    if args.timeout:
        result.append("-T:" + str(args.timeout))
    return result


def compute_file_list():
    result = []
    for fn in args.files:
        if os.path.isdir(fn):
            result += glob.glob(os.path.join(fn, "*.smt2"))
        else:
            result.append(fn)
    if args.limit and args.limit < len(result):
        result = random.sample(result, args.limit)
    return result


status_reg = re.compile("unsat|sat|unknown|timeout")
limit_reg = re.compile("rlimit-count *(\d*)")
time_reg = re.compile(":time *(\d*.\d*)")


def regex_get(regex, text, group=None):
    m = regex.search(text)
    if m is None:
        print "regex not found, output was:"
        print text
        return "0"
    if group is None:
        return m.group()
    else:
        return m.group(group)


def parse_z3_output(output, fn):
    """ run on single file and extract statistics"""
    try:
        return\
            {"filename": fn,
             "status": regex_get(status_reg, output),
             "steps": int(regex_get(limit_reg, output, 1)),
             "time": float(regex_get(time_reg, output, 1))}
    except ValueError:
        return {"filename": fn, "status": "error", "output": output}


def start_server(fname):
    cmd = ["why3server",
           "-j", str(args.parallel),
           "--single-client",
           "--logging",
           "--socket", fname]
    print cmd
    subprocess.Popen(cmd)
    time.sleep(1)
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.connect(fname)
    return sock

id_num = 1


def send_request(fd, cmd):
    global id_num
    id_num = id_num + 1
    cmdstr = ';'.join(cmd)
    s = "run;{id_num};0;0;{cmd}\n".format(id_num=id_num, cmd=cmdstr)
    fd.sendall(s)
    return id_num


def read_request(fd):
    s = fd.recv(4096)
    l = s.splitlines()
    results = []
    for s in l:
        s = s.strip('\n')
        l = s.split(';')
        my_id = l[0]
        fn = l[-1]
        results.append((int(my_id), fn))
    return results


def get_all_results(cmd, output_parser, fnlist, max_running_processes=1):
    """This function will, for each element fn of the string list [fnlist],
       append fn to the string list [cmd], run the result as a command,
       extract its output to stdout/stderr, and run the output_parser on the
       pair (fn, output). The result of the function is the list of the
       results of the output_parser. Note that the order of results may be
       different from the order of strings in input.
   """
    results = []
    file_map = {}
    fd = start_server("sock.sock")
    for fn in fnlist:
        my_id = send_request(fd, cmd + [fn])
        file_map[my_id] = fn
    while len(file_map) > 0:
        if args.verbose:
            print "remaining VCs: ", len(file_map)
        l = read_request(fd)
        for my_id, out in l:
            with open(out, "r") as f:
                output = f.read()
            os.remove(out)
            cur_file = file_map[my_id]
            del file_map[my_id]
            results.append(parse_z3_output(output, cur_file))

    return results


def main():
    parse_arguments()
    file_list = compute_file_list()
    results = get_all_results(cmd=z3_cmd(),
                              output_parser=parse_z3_output,
                              fnlist=file_list,
                              max_running_processes=args.parallel)
    s = json.dumps({"results": results}, indent=2)
    if args.output:
        with open(args.output, "w+") as f:
            f.write(s)
    else:
        print s


main()
