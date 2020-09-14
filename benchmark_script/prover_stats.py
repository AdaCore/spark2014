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
from tqdm import tqdm

descr = """Run provers on files and return status,
time and steps in machine-parsable format (JSON or CSV)."""


class Prover:
    status_reg = re.compile("unsat|sat|unknown|timeout")
    pattern = "*.smt2"

    def __init__(self):
        self.executable_name = None
        self.version_arg = None

    @staticmethod
    def regex_get(regex, text, group=None):
        m = regex.search(text)
        if m is None:
            return None
        if group is None:
            return m.group()
        else:
            return m.group(group)

    def version(self):
        return subprocess.check_output([self.executable_name,
                                        self.version_arg]).strip()


class Z3(Prover):

    limit_reg = re.compile("rlimit-count *(\d*)")
    time_reg = re.compile(":time *(\d*.\d*)")

    def __init__(self, executable_name="z3"):
        Prover.__init__(self)
        self.executable_name = executable_name
        self.version_arg = "-version"

    def command(self, timeout, rlimit):
        result = [self.executable_name, "-st"]
        if timeout:
            result.append("-T:" + str(timeout))
        if rlimit:
            result.append("rlimit=" + str(rlimit))
        return result

    def parse_output(self, output, fn, time):
        """ run on single file and extract statistics"""
        try:
            try:
                mytime = float(Prover.regex_get(self.time_reg, output, 1))
            except (ValueError, TypeError):
                mytime = time
            try:
                mysteps = int(Prover.regex_get(self.limit_reg, output, 1))
            except TypeError:
                mysteps = 0
            return\
                {"filename": fn,
                 "status": Prover.regex_get(Prover.status_reg, output),
                 "steps": mysteps,
                 "time": mytime }
        except ValueError:
            return {"filename": fn, "status": "error", "output": output}


class Altergo(Prover):

    limit_reg = re.compile("\((\d*) steps\)")
    time_reg = re.compile("\((\d*.\d*)\)")
    status_reg = re.compile("Valid|Timeout|I don't know")
    steps_reg = re.compile("Steps limit reached: (\d*)")
    pattern = "*.why"

    def __init__(self, executable_name="alt-ergo"):
        Prover.__init__(self)
        self.executable_name = executable_name
        self.version_arg = "-version"

    def command(self, timeout, rlimit):
        result = [self.executable_name, "-max-split", "5",
                  "-use-fpa", "-disable-weaks", "-prelude",
                  "fpa-theory-2019-10-08-19h00.why"]
        if timeout:
            result.append("-timelimit")
            result.append(str(timeout))
        if rlimit:
            result.append("-steps-bound")
            result.append(str(rlimit))
        return result

    def parse_output(self, output, fn, time):
        """ run on single file and extract statistics"""
        try:
            ae_status = Prover.regex_get(self.status_reg, output)
            if ae_status is None:
                raise ValueError

            if ae_status == "Valid":
                status = "unsat"
            elif ae_status == "Timeout":
                status = "timeout"
            elif ae_status == "I don't know":
                status = "unkown"
            else:
                raise ValueError

            if status == "timeout":
                steps = 0
                time = 0
            else:
                steps = int(Prover.regex_get(self.limit_reg, output, 1))
                time = float(Prover.regex_get(self.time_reg, output, 1))
            return\
                {"filename": fn,
                 "status": status,
                 "steps": steps,
                 "time": time}
        except ValueError:
            try:
                # special case of steps limit reached
                steps_raw = Prover.regex_get(self.steps_reg, output, 1)
                if steps_raw is None:
                    raise ValueError;
                steps = int(steps_raw)
                return\
                    {"filename": fn,
                     "status": "rlimit",
                     "steps": steps,
                     "time": time}
            except ValueError:
                return {"filename": fn, "status": "error", "output": output}


class CVC4(Prover):
    limit_reg = re.compile("smt::SmtEngine::resourceUnitsUsed, (\d+.?\d*)")
    time_reg = re.compile("driver::totalTime, *(\d*.\d*)")

    def __init__(self, executable_name="cvc4"):
        Prover.__init__(self)
        self.executable_name = executable_name
        self.version_arg = "--version"

    def command(self, timeout, rlimit):
        result = [self.executable_name,
                  "--stats",
                  "--quiet"]
        if timeout:
            result.append("--tlimit=" + str(timeout * 1000))
        if rlimit:
            result.append("--rlimit=" + str(rlimit))
        return result

    def parse_output(self, output, fn, time):
        """ run on single file and extract statistics"""
        try:
            status = Prover.regex_get(Prover.status_reg, output)
            steps = int(Prover.regex_get(self.limit_reg, output, 1))
            time = float(Prover.regex_get(self.time_reg, output, 1))
            return\
                {"filename": fn,
                 "status": status,
                 "steps": steps,
                 "time": time}
        except ValueError:
            return {"filename": fn, "status": "error", "output": output}


def parse_arguments():
    args = None
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
                        help='timeout to be used, default: no timeout')
    parser.add_argument('--rlimit', dest='rlimit', type=int, action='store',
                        default=None,
                        help='resource limit (steps), default: no limit')
    parser.add_argument('--limit', dest='limit', type=int, action='store',
                        default=None, metavar='N',
                        help='randomly select N files from all files')
    parser.add_argument('--prover', dest='prover', action='store',
                        default="z3",
                        help='prover to be used [z3]')
    parser.add_argument('--format', dest='format', action='store',
                        default="json",
                        help='output format [json]')
    args = parser.parse_args()
    if args.prover != "z3" and args.prover != "cvc4" and\
       args.prover != "altergo":
        print("prover " + args.prover + " not supported, exiting.")
        exit(1)
    if args.format != "json" and args.format != "csv":
        print("output format " + args.format + " not supported, exiting.")
        exit(1)
    return args


def compute_file_list(files, prover, limit):
    result = []
    for fn in files:
        if not os.path.exists(fn):
            print("could not find " + fn + ", skipping")
        if os.path.isdir(fn):
            result += glob.glob(os.path.join(fn, prover.pattern))
        else:
            result.append(fn)
    if limit and limit < len(result):
        result = random.sample(result, limit)
    return result


def start_server(fname, parallel, verbose=False):
    cmd = ["why3server",
           "-j", str(parallel),
           "--single-client",
           "--logging",
           "--socket", fname]
    if verbose:
        print(cmd)
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
    fd.sendall(s.encode('utf-8'))
    return id_num


def read_request(fd):
    s = fd.recv(4096)
    lines = s.decode('utf-8').splitlines()
    results = []
    for s in lines:
        s = s.strip('\n')
        if s.startswith("F"):
            fields = s.split(';')
            my_id = fields[1]
            time = float(fields[3])
            fn = fields[-1]
            results.append((int(my_id), fn, time))
    return results


def get_all_results(prover, fnlist, parallel, verbose, timeout, rlimit):
    """This function will, for each element fn of the string list [fnlist],
       append fn to the string list [cmd], run the result as a command,
       extract its output to stdout/stderr, and run the output_parser on the
       pair (fn, output). The result of the function is the list of the
       results of the output_parser. Note that the order of results may be
       different from the order of strings in input.
   """
    results = []
    file_map = {}
    fd = start_server("sock.sock",
                      parallel=parallel,
                      verbose=verbose)
    for fn in fnlist:
        my_id = send_request(fd, prover.command(timeout=timeout,
                                                rlimit=rlimit) + [fn])
        file_map[my_id] = fn
    with tqdm(total=len(file_map)) as pbar:
        while len(file_map) > 0:
            requests = read_request(fd)
            pbar.update(len(requests))
            for my_id, out, req_time in requests:
                with open(out, "r") as f:
                    output = f.read()
                os.remove(out)
                cur_file = file_map[my_id]
                del file_map[my_id]
                results.append(prover.parse_output(output, cur_file, req_time))

    return results


def run_stats(prover, files,
              limit=None,
              parallel=1,
              timeout=1,
              rlimit=None,
              verbose=False):
    file_list = compute_file_list(files, prover, limit)
    results = get_all_results(prover=prover,
                              fnlist=file_list,
                              parallel=parallel,
                              verbose=verbose,
                              timeout=timeout,
                              rlimit=rlimit)
    return results


def main():
    args = parse_arguments()
    if args.prover == "z3":
        prover = Z3()
    elif args.prover == "cvc4":
        prover = CVC4()
    elif args.prover == "altergo":
        prover = Altergo()
    else:
        raise ValueError

    results = run_stats(prover=prover,
                        files=args.files,
                        limit=args.limit,
                        parallel=args.parallel,
                        timeout=args.timeout,
                        rlimit=args.rlimit,
                        verbose=args.verbose)

    if args.format == "json":
        s = json.dumps({"results": results}, indent=2)
    elif args.format == "csv":
        s = "Filename, Status, Time, Steps\n"
        for elt in results:
            if elt["status"] == "error":
                s += elt["filename"] + ", " + elt["status"] + ", 0 , 0\n"
            else:
                s += elt["filename"] + ", " + elt["status"] + ", " +\
                     str(elt["time"]) + ", " + str(elt["steps"]) + "\n"
    if args.output:
        with open(args.output, "w+") as f:
            f.write(s)
    else:
        print(s)


if __name__ == "__main__":
    main()
