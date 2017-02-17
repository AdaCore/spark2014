package body P is pragma SPARK_Mode (On);

   procedure P (X : in out A) is
   begin
      X (1,2) := X (1, 2) + 1;
   end P;

   procedure Q (Z : in out R) is
   begin
      Z.FA (1,2) := Z.FA (1,2) + 1;
   end Q;

end P;
