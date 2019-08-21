from test_support import *
import os.path
import shutil
from gnatpython.ex import Run

# This test recreates the Coq realizations of the SPARK Why3 definitions and
# checks them using Coq

why3_share = os.path.join(spark_install_path(), 'libexec', 'spark', 'share', 'why3')
why3_lib = os.path.join(why3_share, 'theories')
coq_libs_dir = os.path.join(why3_share, 'libs', 'coq')
driver_dir = os.path.join(why3_share, 'drivers')
why3_bin = os.path.join(spark_install_path(), 'libexec', 'spark', 'bin', 'why3realize')
gp_realized = ['Integer', 'Int_Power', 'Int_Minmax', 'Int_Abs', 'Int_Division', 'Array__1', 'Array__1__Concat']
am_realized = ['Rep_Proj_Base', 'Rep_Proj_BVGen', 'Rep_Proj_Int', 'Rep_Proj_ltBVGen']
realize_subdir = 'realize'

def copy_spark_why_files():
    theories_dir = os.path.join(spark_install_path(), 'share', 'spark', 'theories')
    theory_files = glob.glob(os.path.join(theories_dir,'*.mlw'))
    theory_files += glob.glob(os.path.join(theories_dir,'*.why'))
    curdir = os.getcwd()
    for f in theory_files:
        shutil.copyfile(f, os.path.join(curdir, os.path.basename(f)))

def compile_coq_files():
    cwd = os.getcwd()
    print ('Copying coq repository')
    shutil.copytree(coq_libs_dir, 'coq')
    # if new theories get added to our hardcoded 'coq-realizations.aux' file
    # in why3 repository, this list needs to be changed, too
    files_to_be_compiled = [
            "BuiltIn.v",
            "HighOrd.v",
            os.path.join("int", "Int"),
            os.path.join("int", "Abs"),
            os.path.join("int", "ComputerDivision"),
            os.path.join("int", "EuclideanDivision"),
            os.path.join("int", "Div2"),
            os.path.join("int", "MinMax"),
            os.path.join("int", "Exponentiation"),
            os.path.join("int", "Power"),
            os.path.join("int", "NumOf"),
            os.path.join("bool", "Bool"),
            os.path.join("real", "Real"),
            os.path.join("real", "Abs"),
            os.path.join("real", "ExpLog"),
            os.path.join("real", "FromInt"),
            os.path.join("real", "MinMax"),
            os.path.join("real", "RealInfix"),
            os.path.join("real", "PowerInt"),
            os.path.join("real", "Square"),
            os.path.join("real", "PowerReal"),
            os.path.join("real", "Trigonometry"),
            os.path.join("number", "Parity"),
            os.path.join("number", "Divisibility"),
            os.path.join("number", "Gcd"),
            os.path.join("number", "Prime"),
            os.path.join("number", "Coprime"),
            os.path.join("map", "Map"),
            os.path.join("map", "Const"),
            os.path.join("map", "Occ"),
            os.path.join("map", "MapPermut"),
            os.path.join("map", "MapInjection"),
            os.path.join("set", "Set"),
            os.path.join("option", "Option"),
            os.path.join("list", "List"),
            os.path.join("list", "Length"),
            os.path.join("list", "Mem"),
            os.path.join("list", "Nth"),
            os.path.join("list", "NthLength"),
            os.path.join("list", "HdTl"),
            os.path.join("list", "NthHdTl"),
            os.path.join("list", "Append"),
            os.path.join("list", "NthLengthAppend"),
            os.path.join("list", "Reverse"),
            os.path.join("list", "HdTlNoOpt"),
            os.path.join("list", "NthNoOpt"),
            os.path.join("list", "RevAppend"),
            os.path.join("list", "Combine"),
            os.path.join("list", "Distinct"),
            os.path.join("list", "NumOcc"),
            os.path.join("list", "Permut"),
            os.path.join("bv", "Pow2int"),
            os.path.join("bv", "BV_Gen")
            ]

    os.chdir('coq')
    print ('Compiling coq stdlib')
    for fn in files_to_be_compiled:
        process = Run(['coqc', '-R', '.', 'Why3', fn])
        if process.status != 0:
            print "FAILED ! Compilation of stdlib failed"
        lines = process.out.splitlines()
        lines = grep(".*Grammar extension", lines, invert=True)
        for line in lines:
            print line
    print ('Coq stdlib compiled')
    os.chdir(cwd)


def realize_theories():
    print ('Launch why3realize')
    for real in gp_realized:
        print ('Generate realization for ' + real)
        process = Run([why3_bin, '-L', '.', '-L', why3_lib, '-T',
                       '_gnatprove_standard.' + real, '-o', realize_subdir,
                       '-D', os.path.join(driver_dir, 'coq-realize.drv')])
        if process.status != 0:
            print "FAILED ! Generation of realization coq files failed"
        print process.out
    for real in am_realized:
        print ('Generate realization for ' + real)
        process = Run([why3_bin, '-L', '.', '-L', why3_lib, '-T',
                       'ada__model.' + real, '-o', realize_subdir, '-D',
                       os.path.join(driver_dir, 'coq-realize.drv')])
        if process.status != 0:
            print "FAILED ! Generation of realization coq files failed"
        print process.out

def check_realizations():
    print ('Check realizations')
    os.chdir(realize_subdir)
    for real in gp_realized+am_realized:
        print ('Run Coqc on realization file: ' + real)
        process = Run(['coqc', '-R', os.path.join('..', 'coq'), 'Why3', real + '.v'])
        if process.status != 0:
            print "FAILED ! The Coq compilation of the library filed"
        lines = process.out.splitlines()
        lines = grep(".*Grammar extension", lines, invert=True)
        for line in lines:
            print line
    print ('The realizations checks were run')

copy_spark_why_files()
compile_coq_files()
realize_theories()
check_realizations()
