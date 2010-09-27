#!/usr/bin/env python

import sys
import glob
import os
import re

if len(sys.argv) != 2:
    print 'Pass in a directory name'
    sys.exit(1)

def find_executable(executable, path=None):
    """Try to find 'executable' in the directories listed in 'path' (a
    string listing directories separated by 'os.pathsep'; defaults to
    os.environ['PATH']).  Returns the complete filename or None if not
    found
    """
    if path is None:
        path = os.environ['PATH']
    paths = path.split(os.pathsep)
    extlist = ['']
    if os.name == 'os2':
        (base, ext) = os.path.splitext(executable)
        # executable files on OS/2 can have an arbitrary extension, but
        # .exe is automatically appended if no dot is present in the name
        if not ext:
            executable = executable + ".exe"
    elif sys.platform == 'win32':
        pathext = os.environ['PATHEXT'].lower().split(os.pathsep)
        (base, ext) = os.path.splitext(executable)
        if ext.lower() not in pathext:
            extlist = pathext
    for ext in extlist:
        execname = executable + ext
        if os.path.isfile(execname):
            return execname
        else:
            for p in paths:
                f = os.path.join(p, execname)
                if os.path.isfile(f):
                    return f
    else:
        return None

sparkify_cmd = find_executable('sparkify')
root_dir = os.path.dirname(os.path.dirname(sparkify_cmd))
config_file = os.path.join(os.path.join(root_dir, 'test-support'), 
                           'standard.ads')

dir = sys.argv[1]
os.chdir(dir)

files = glob.glob('*.ad?')
cmd = 'sparkify ' + " ".join(files) + '> dummy.log 2>&1'
os.system(cmd)

# simplication: we assume currently only one *.adb file in the source 
#               directory, and likewise for the sparkified directory

source_file = glob.glob('*.adb')
if len(source_file) != 1:
    print 'More than one .adb file in source directory'
    exit(1)
source_file = source_file[0]
target_file = glob.glob(os.path.join('sparkified', '*.adb'))
if len(target_file) != 1:
    print 'More than one .adb file in sparkified directory'
    exit(1)
target_file = target_file[0]

source_subprograms = {}

f = open(source_file, 'r')
source_linenum = 1
for line in f:
    if line.find('procedure ') >= 0:
        subprogram_name = line.partition('procedure ')[2].strip()
        subprogram_name = subprogram_name.split()[0].split('(')[0].lower()
        source_subprograms[subprogram_name] = source_linenum
    elif line.find('function ') >= 0:
        subprogram_name = line.partition('function ')[2].strip()
        subprogram_name = subprogram_name.split()[0].split('(')[0].lower()
        source_subprograms[subprogram_name] = source_linenum
    source_linenum += 1

# from strings to line numbers
source_corresp = {}

f = open(target_file, 'r')
source_linenum = 1
target_linenum = 1
for line in f:
    if line.startswith('--@ line'):
        source_linenum = int(re.findall(r'[0-9]+', line)[0])
    else:
        source_corresp[str(target_linenum)] = source_linenum
        source_linenum += 1
    target_linenum += 1

os.chdir('sparkified')

cmd = 'sparkmake > dummy.log'
os.system(cmd)
cmd = 'spark -noecho -fdl=_fdl_ -flow=data -config=' + config_file 
cmd = cmd + ' -vcg @spark'
os.system(cmd)
cmd = 'sparksimp > dummy.log'
os.system(cmd)
cmd = 'pogs > dummy.log'
os.system(cmd)

f = open('sparkified.sum', 'r')
for line in f:
    if line.startswith('VCs for '):
        subprogram_name = line.partition('_')[2].partition(':')[0].strip()
        source_corresp['finish'] = source_subprograms[subprogram_name]
    elif line.find('| Undischarged') != -1:
        words = line.split('|')
        sub = words[3].split('@')
        check = sub[0].strip()
        linenum = sub[1].strip()
        error_msg = source_file + ":" + str(source_corresp[linenum]) + ":1: "
        if check == 'rtc check':
            error_msg = error_msg + "run-time check cannot be proved"
        elif check == 'assert':
            if linenum == 'finish':
                error_msg = error_msg + "postcondition cannot be proved"
            else:
                error_msg = error_msg + "assertion cannot be proved"
        print error_msg
