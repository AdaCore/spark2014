with Other;

package body Final is
   procedure Test_1 (N : in out Integer)
   is
   begin
      Other.A (N);
   end Test_1;

   procedure Test_2 (N : in out Integer)
   is
   begin
      Other.B (N);
   end Test_2;

   procedure Test_3 (N : in out Integer)
   is
   begin
      Other.A (N);
   end Test_3;

   procedure Test_4 (N : in out Integer)
   is
   begin
      Other.B (N);
   end Test_4;

end Final;
