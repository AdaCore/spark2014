pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package body Show_Bug with
  SPARK_Mode => On
is

   protected body Control is

      procedure Write is
      begin
         V := B'(others => True); --  This works (when next line is commented out).
         V (0) := True;           --  This line crashes with a bug box:

         --  +===========================GNAT BUG DETECTED==============================+
         --  | Community 2018 (20180523) (spark) Program_Error EXCEPTION_ACCESS_VIOLATION|
         --  | Error detected at show_bug.adb:13:16                                     |
         --  | Please submit a bug report by email to report@adacore.com.               |
         --  | GAP members can alternatively use GNAT Tracker:                          |
         --  | http://www.adacore.com/ section 'send a report'.                         |
         --  | See gnatinfo.txt for full info on procedure for submitting bugs.         |
         --  | Use a subject line meaningful to you and us to track the bug.            |
         --  | Include the entire contents of this bug box in the report.               |
         --  | Include the exact command that you entered.                              |
         --  | Also include sources listed below.                                       |
         --  | Use plain ASCII or MIME attachment(s).                                   |
         --  +==========================================================================+

         --  The same happens with a record type; hence it seems that any kind
         --  of partial access to a synchronised variable triggers the problem.
      end Write;

   end Control;

end Show_Bug;
