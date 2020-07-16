with Decl_Only; use Decl_Only;

package Call_Proc_No_Body with Annotate => (GNATprove, Terminating) is
   procedure Returning;

   procedure Nonreturning;
end;
