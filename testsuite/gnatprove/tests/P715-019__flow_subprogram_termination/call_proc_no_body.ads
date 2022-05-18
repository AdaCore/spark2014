with Decl_Only; use Decl_Only;

package Call_Proc_No_Body with Annotate => (GNATprove, Always_Return) is
   procedure Returning;

   procedure Nonreturning;
end;
