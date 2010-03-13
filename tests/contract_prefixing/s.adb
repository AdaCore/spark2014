package body S is

   procedure Inc_Positive (N : in out Signed)
   is
      pragma Precondition (N > 0 and N < Signed'Last);
      pragma Postcondition (N = N'Old + 1);
   begin
      N := Signed (Integer (N) + 1);
   end Inc_Positive;

   function Inc_Positive_F (N : Signed) return Signed
   is
      pragma Precondition (N > 0 and N < Signed'Last);
      pragma Postcondition (Inc_Positive_F'Result = N + 1);
   begin
      return Signed (Integer (N) + 1);
   end Inc_Positive_F;

   procedure Plus_Two  (N : in out Signed) is
   begin
      Inc_Positive (N);
      Inc_Positive (N);
   end Plus_Two;

   function Plus_Two_F (N : Signed) return Signed is
   begin
      return Inc_Positive_F (Inc_Positive_F (N));
   end Plus_Two_F;

end S;
