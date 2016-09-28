from test_support import *
from shutil import copyfile
import time

copyfile("empty_restrictions.adc", "restrictions.adc")
gnatprove()
sleep(5)
copyfile("spark_restrictions.adc", "restrictions.adc")
gnatprove(opt=["-P", "test.gpr", "--warnings=continue"])
