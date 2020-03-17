package body Volatiles_Illegal_4
  with SPARK_Mode
is
   procedure P1 (Par : in Vol_Rec_T ; Par2 : out Integer) is
   begin
      Par2 := Par.X;
   end P1;

   procedure P3 (Par : in out Vol_Rec_T) is
   begin
      Par.X := Par.X + 1; -- illegal RM 7.1.3(10)
   end P3;

   procedure P4 (X : in out Integer) is
   begin
      X := X + 1; -- legal, X is not Volatile
   end P4;
begin
   P1 (Vol1, A);  --  Vol1 does not have Effective_Reads => False.

   P3 (Vol2);     --  Vol2 does not have all attributes set to True.

   P4 (B);        --  B is a volatile while the formal parameter of
                  --  procedure P4 was not.
end Volatiles_Illegal_4;
