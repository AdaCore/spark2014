from test_support import *
from subprocess import call

prove_all(cache_allowed=False)

installdir = spark_install_path()
why3session = os.path.join(installdir, 'libexec', 'spark', 'bin',
        'why3session')
call([why3session,'info', '--stats', os.path.join('gnatprove', 'add__addtwo')])
