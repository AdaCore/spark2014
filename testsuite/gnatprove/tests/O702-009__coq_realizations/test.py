import glob
import os.path
import shutil
from e3.os.process import Run
from test_support import grep, spark_install_path

# This test recreates the Coq realizations of the SPARK Why3 definitions and
# checks them using Coq

why3_share = os.path.join(spark_install_path(), "libexec", "spark", "share", "why3")
why3_lib = os.path.join(why3_share, "theories")
coq_libs_dir = os.path.join(why3_share, "libs", "coq")
driver_dir = os.path.join(why3_share, "drivers")
why3_bin = os.path.join(spark_install_path(), "libexec", "spark", "bin", "why3")
gp_realized = [
    "Integer",
    "Int_Power",
    "Int_Minmax",
    "Int_Abs",
    "Array__1",
]
am_realized = [
    "Rep_Proj_Base",
    "Rep_Proj_BVGen",
    "Rep_Proj_Int",
    "Rep_Proj_ltBVGen",
    "Array_Comparison_Axiom",
]
realize_subdir = "realize"


def copy_spark_why_files():
    theories_dir = os.path.join(spark_install_path(), "share", "spark", "theories")
    theory_files = glob.glob(os.path.join(theories_dir, "*.mlw"))
    theory_files += glob.glob(os.path.join(theories_dir, "*.why"))
    curdir = os.getcwd()
    for f in theory_files:
        shutil.copyfile(f, os.path.join(curdir, os.path.basename(f)))


def compile_coq_files():
    cwd = os.getcwd()
    print("Copying coq repository")
    shutil.copytree(coq_libs_dir, "coq")
    # if new theories get added to our hardcoded 'coq-realizations.aux' file
    # in why3 repository, this list needs to be changed, too
    files_to_be_compiled = [
        "BuiltIn.v",
        "HighOrd.v",
        "WellFounded.v",
        os.path.join("int", "Int.v"),
        os.path.join("int", "Abs.v"),
        os.path.join("int", "ComputerDivision.v"),
        os.path.join("int", "EuclideanDivision.v"),
        os.path.join("int", "Div2.v"),
        os.path.join("int", "MinMax.v"),
        os.path.join("int", "Exponentiation.v"),
        os.path.join("int", "Power.v"),
        os.path.join("int", "NumOf.v"),
        os.path.join("bool", "Bool.v"),
        os.path.join("real", "Real.v"),
        os.path.join("real", "Abs.v"),
        os.path.join("real", "ExpLog.v"),
        os.path.join("real", "FromInt.v"),
        os.path.join("real", "MinMax.v"),
        os.path.join("real", "RealInfix.v"),
        os.path.join("real", "PowerInt.v"),
        os.path.join("real", "Square.v"),
        os.path.join("real", "PowerReal.v"),
        os.path.join("real", "Trigonometry.v"),
        os.path.join("number", "Parity.v"),
        os.path.join("number", "Divisibility.v"),
        os.path.join("number", "Gcd.v"),
        os.path.join("number", "Prime.v"),
        os.path.join("number", "Coprime.v"),
        os.path.join("map", "Map.v"),
        os.path.join("map", "Const.v"),
        os.path.join("map", "Occ.v"),
        os.path.join("map", "MapPermut.v"),
        os.path.join("map", "MapInjection.v"),
        os.path.join("map", "MapExt.v"),
        os.path.join("set", "Set.v"),
        os.path.join("option", "Option.v"),
        os.path.join("list", "List.v"),
        os.path.join("list", "Length.v"),
        os.path.join("list", "Mem.v"),
        os.path.join("list", "Nth.v"),
        os.path.join("list", "NthLength.v"),
        os.path.join("list", "HdTl.v"),
        os.path.join("list", "NthHdTl.v"),
        os.path.join("list", "Append.v"),
        os.path.join("list", "NthLengthAppend.v"),
        os.path.join("list", "Reverse.v"),
        os.path.join("list", "HdTlNoOpt.v"),
        os.path.join("list", "NthNoOpt.v"),
        os.path.join("list", "RevAppend.v"),
        os.path.join("list", "Combine.v"),
        os.path.join("list", "Distinct.v"),
        os.path.join("list", "NumOcc.v"),
        os.path.join("list", "Permut.v"),
        os.path.join("bv", "Pow2int.v"),
        os.path.join("bv", "BV_Gen.v"),
    ]

    os.chdir("coq")
    print("Compiling coq stdlib")
    for fn in files_to_be_compiled:
        process = Run(["coqc", "-R", ".", "Why3", fn])
        if process.status != 0:
            print("FAILED ! Compilation of stdlib failed")
        lines = process.out.splitlines()
        lines = grep(".*Grammar extension", lines, invert=True)
        for line in lines:
            print(line)
    print("Coq stdlib compiled")
    os.chdir(cwd)


def realize_theories():
    print("Launch why3realize")
    for real in gp_realized:
        print("Generate realization for " + real)
        process = Run(
            [
                why3_bin,
                "realize",
                "-L",
                ".",
                "-L",
                why3_lib,
                "-T",
                "_gnatprove_standard." + real,
                "-o",
                realize_subdir,
                "-D",
                os.path.join(driver_dir, "coq-realize.drv"),
            ]
        )
        if process.status != 0:
            print("FAILED ! Generation of realization coq files failed")
        print(process.out)
    for real in am_realized:
        print("Generate realization for " + real)
        process = Run(
            [
                why3_bin,
                "realize",
                "-L",
                ".",
                "-L",
                why3_lib,
                "-T",
                "ada__model." + real,
                "-o",
                realize_subdir,
                "-D",
                os.path.join(driver_dir, "coq-realize.drv"),
            ]
        )
        if process.status != 0:
            print("FAILED ! Generation of realization coq files failed")
        print(process.out)


def check_realizations():
    print("Check realizations")
    os.chdir(realize_subdir)
    for real in gp_realized + am_realized:
        print("Run Coqc on realization file: " + real)
        process = Run(["coqc", "-R", os.path.join("..", "coq"), "Why3", real + ".v"])
        if process.status != 0:
            print("FAILED ! The Coq compilation of the library filed")
        lines = process.out.splitlines()
        lines = grep(".*Grammar extension", lines, invert=True)
        for line in lines:
            print(line)
    print("The realizations checks were run")


copy_spark_why_files()
compile_coq_files()
realize_theories()
check_realizations()
