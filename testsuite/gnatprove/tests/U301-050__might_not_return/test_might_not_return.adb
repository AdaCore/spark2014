with Might_Not_Return_Callee; use Might_Not_Return_Callee;

procedure Test_Might_Not_Return with SPARK_Mode is

   procedure Caller is
   begin
      P;
   end Caller;
begin
   null;
end Test_Might_Not_Return;
