from e3.os.process import Run

process = Run(["gnatprove"])
print(process.out)
