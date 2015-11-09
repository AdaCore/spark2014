from test_support import *
import os.path
import shutil
from gnatpython.ex import Run

# This test recreates the Coq realizations of the SPARK Why3 definitions and
# checks them using Coq

why3_share = os.path.join(spark_install_path(), 'share', 'why3')
coq_libs_dir = os.path.join(why3_share, 'libs', 'coq')
driver_dir = os.path.join(why3_share, 'drivers')
why3_bin = os.path.join(spark_install_path(), 'libexec', 'spark', 'bin', 'why3realize.opt')
realized = ['Integer', 'Int_Power', 'Int_Minmax', 'Int_Abs', 'Int_Division', 'Array__1']
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
    shutil.copytree(coq_libs_dir, 'coq')
    files_to_be_compiled = [
            'BuiltIn.v',
            os.path.join('bool','Bool.v'),
            os.path.join('int', 'Int.v')]

    os.chdir('coq')
    for fn in files_to_be_compiled:
        process = Run(['coqc', '-R', '.', 'Why3', fn])
        print process.out
    os.chdir(cwd)


def realize_theories():
    for real in realized:
        process = Run([why3_bin, '-L', '.', '-T', '_gnatprove_standard.' + real, '-o',
            realize_subdir, '-D', os.path.join(driver_dir, 'coq-realize.drv')])
        print process.out

def check_realizations():
    os.chdir(realize_subdir)
    for real in realized:
        process = Run(['coqc', '-R', os.path.join('..', 'coq'), 'Why3', real + '.v'])
        print process.out

copy_spark_why_files()
compile_coq_files()
realize_theories()
check_realizations()




