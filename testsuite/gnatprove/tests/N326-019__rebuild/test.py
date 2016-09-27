from test_support import *
from shutil import copyfile

copyfile("empty_restrictions.adc", "restrictions.adc")
gnatprove()
sleep_on_windows(5)
copyfile("spark_restrictions.adc", "restrictions.adc")
gnatprove(opt=["-P", "test.gpr", "--warnings=continue"])
