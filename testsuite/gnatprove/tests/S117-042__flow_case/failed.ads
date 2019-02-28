procedure FAILED
  -- OUTPUT A FAILURE MESSAGE. SHOULD BE INVOKED SEPARATELY TO REPORT THE
  -- FAILURE OF EACH SUBTEST WITHIN A TEST.

  (DESCR : String      -- BRIEF DESCRIPTION OF WHAT FAILED.
                       -- SHOULD BE PHRASED AS:
                       -- "(FAILED BECAUSE) ...REASON...".
  ) with
  GLOBAL => null,
  PRE => False;
