-- REPSPEC.ADA
--
--                             Grant of Unlimited Rights
--
--     Under contracts F33600-87-D-0337, F33600-84-D-0280, MDA903-79-C-0687,
--     F08630-91-C-0015, and DCA100-97-D-0025, the U.S. Government obtained
--     unlimited rights in the software and documentation contained herein.
--     Unlimited rights are defined in DFAR 252.227-7013(a)(19).  By making
--     this public release, the Government intends to confer upon all
--     recipients unlimited rights  equal to those held by the Government.
--     These rights include rights to use, duplicate, release or disclose the
--     released technical data and computer software in whole or in part, in
--     any manner and for any purpose whatsoever, and to have or permit others
--     to do so.
--
--                                    DISCLAIMER
--
--     ALL MATERIALS OR INFORMATION HEREIN RELEASED, MADE AVAILABLE OR
--     DISCLOSED ARE AS IS.  THE GOVERNMENT MAKES NO EXPRESS OR IMPLIED
--     WARRANTY AS TO ANY MATTER WHATSOEVER, INCLUDING THE CONDITIONS OF THE
--     SOFTWARE, DOCUMENTATION OR OTHER INFORMATION RELEASED, MADE AVAILABLE
--     OR DISCLOSED, OR THE OWNERSHIP, MERCHANTABILITY, OR FITNESS FOR A
--     PARTICULAR PURPOSE OF SAID MATERIAL.
--*
--
-- PURPOSE:
--      THIS REPORT PACKAGE PROVIDES THE MECHANISM FOR REPORTING THE
--      PASS/FAIL/NOT-APPLICABLE RESULTS OF EXECUTABLE (CLASSES A, C,
--      D, E, AND L) TESTS.

--      IT ALSO PROVIDES THE MECHANISM FOR GUARANTEEING THAT CERTAIN
--      VALUES BECOME DYNAMIC (NOT KNOWN AT COMPILE-TIME).

-- HISTORY:
--      JRK 12/13/79
--      JRK 06/10/80
--      JRK 08/06/81
--      JRK 10/27/82
--      JRK 06/01/84
--      PWB 07/30/87  ADDED PROCEDURE SPECIAL_ACTION.
--      TBN 08/20/87  ADDED FUNCTION LEGAL_FILE_NAME.
--      BCB 05/17/90  ADDED FUNCTION TIME_STAMP.
--      WMC 01/24/94  INCREASED RANGE OF TYPE FILE_NUM FROM 1..3 TO 1..5.
--      KAS 06/19/95  ADDED FUNCTION IDENT_WIDE_CHAR.
--      KAS 06/19/95  ADDED FUNCTION IDENT_WIDE_STR.

PACKAGE REPORT IS

  -- THE REPORT ROUTINES.

     PROCEDURE TEST           -- THIS ROUTINE MUST BE INVOKED AT THE
                              -- START OF A TEST, BEFORE ANY OF THE
                              -- OTHER REPORT ROUTINES ARE INVOKED.
                              -- IT SAVES THE TEST NAME AND OUTPUTS THE
                              -- NAME AND DESCRIPTION.
        ( NAME : STRING;      -- TEST NAME, E.G., "C23001A-AB".
          DESCR : STRING      -- BRIEF DESCRIPTION OF TEST, E.G.,
                              -- "UPPER/LOWER CASE EQUIVALENCE IN " &
                              -- "IDENTIFIERS".
        )
     WITH GLOBAL => NULL;

     PROCEDURE FAILED         -- OUTPUT A FAILURE MESSAGE.  SHOULD BE
                              -- INVOKED SEPARATELY TO REPORT THE
                              -- FAILURE OF EACH SUBTEST WITHIN A TEST.
        ( DESCR : STRING      -- BRIEF DESCRIPTION OF WHAT FAILED.
                              -- SHOULD BE PHRASED AS:
                              -- "(FAILED BECAUSE) ...REASON...".
        )
     WITH GLOBAL => NULL,
          PRE    => FALSE;

     PROCEDURE RESULT
     WITH GLOBAL => NULL;     -- THIS ROUTINE MUST BE INVOKED AT THE
                              -- END OF A TEST.  IT OUTPUTS A MESSAGE
                              -- INDICATING WHETHER THE TEST AS A
                              -- WHOLE HAS PASSED, FAILED, IS
                              -- NOT-APPLICABLE, OR HAS TENTATIVELY
                              -- PASSED PENDING SPECIAL ACTIONS.

END REPORT;
