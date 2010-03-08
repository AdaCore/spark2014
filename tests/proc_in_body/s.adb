package body S is

   procedure Inc_Positive (N : in out Integer)
   is
      pragma Precondition (N > 0 and N < Integer'Last);
      pragma Postcondition (N = N'Old + 1);
   begin
      N := N + 1;
   end Inc_Positive;

   procedure Plus_Two  (N : in out Integer) is
   begin
      Inc_Positive (N);
      Inc_Positive (N);
   end Plus_Two;

end S;
