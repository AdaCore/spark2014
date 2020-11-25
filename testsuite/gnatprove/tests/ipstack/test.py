from subprocess import call

call(["make", "TARGET=native", "--silent", "spark"])
