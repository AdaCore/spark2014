package body Test_Invariants with SPARK_Mode is

   procedure P (B : Boolean; X : in out T) is
   begin
      X.F := X.F + 1;
      if B then
         raise E;
      end if;
      X.F := X.F - 1;
   end P;

   procedure Q (B : Boolean; X : aliased in out T) is
   begin
      X.F := X.F + 1;
      if B then
         raise E;
      end if;
      X.F := X.F - 1;
   end Q;

end Test_Invariants;
