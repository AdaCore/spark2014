import resource
from test_support import *

soft, hard = resource.getrlimit(resource.RLIMIT_DATA)
# setting memlimit to 128MB
resource.setrlimit(resource.RLIMIT_DATA, (2 ** 27, hard))

prove_all()
