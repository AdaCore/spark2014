with GPR2; use GPR2;
with GPR2.Project.Tree;
with String_Utils;

package Gnatprove_Build is

   --  This package contains types and subprograms related to the
   --  build process of Gnatprove.

   procedure Flow_Analysis_And_Proof
     (Tree              : Project.Tree.Object;
      SPARK_Files       : out String_Utils.String_Lists.List;
      SPARK_Error_Files : out String_Utils.String_Lists.List;
      Success           : out Boolean);
   --  Call gnat2why on all relevant units in analysis mode, generating
   --  unit.spark files. SPARK_Files is set to the expected .spark file paths
   --  (one per queued analysis action); a file may be absent if its action
   --  failed at runtime. SPARK_Error_Files is set to the expected
   --  .spark_error file paths (one per queued global-generation action);
   --  these carry frontend diagnostics for the report. Success is set to
   --  False if analysis failed.

end Gnatprove_Build;
