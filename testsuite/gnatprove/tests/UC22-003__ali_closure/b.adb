with A;

package body B with SPARK_Mode is

   X : Integer;

   function Valid return Boolean is (X = A.A);

   procedure Set is
   begin
      X := A.A;
   end Set;

   procedure P is
   begin
      A.P;
   end P;

end B;
