from test_support import *

# The example should be all proved now. To reproduce:
#  - remove session files to avoid getting obsolete goals
#  - launch GNATprove with --level=2 on everything (~15min with -j4)
#  - launch GNATprove with --level=3 --timeout=30 on everything (~8min with -j4)
#
#  rm -r proof/sessions/
#  gnatprove -P test.gpr --level=2 -j0
#  gnatprove -P test.gpr --level=3 -j0 --timeout=30

prove_all(opt=["--replay"])
