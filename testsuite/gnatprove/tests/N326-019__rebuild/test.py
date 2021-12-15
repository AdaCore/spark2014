from test_support import gnatprove, sleep
from shutil import copyfile

copyfile("empty_restrictions.adc", "restrictions.adc")
gnatprove()
sleep(5)
copyfile("spark_restrictions.adc", "restrictions.adc")
gnatprove(opt=["-P", "test.gpr", "--warnings=continue"])
