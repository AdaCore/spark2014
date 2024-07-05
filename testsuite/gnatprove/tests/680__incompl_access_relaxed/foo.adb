procedure Foo with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   type C is record
      F, G : Integer;
   end record with Predicate => False;

   type R is record
     T : C;
   end record;

   type L_Cell;
   type L is access L_Cell;
   type L_Cell is record
      V : R;
      N : L;
   end record;

   type Z is record
      U : Integer;
      P : L;
   end record;

   X : Z with Relaxed_Initialization;
   V : R with Relaxed_Initialization;

begin
   X.P := new L_Cell'(V => V, N => null);
   X.P := new L_Cell'(V => V, N => X.P);
   for I in 1 .. Id (1) loop
      pragma Assert (False); -- @ASSERT:FAIL
      X.U := 14;
   end loop;
end Foo;
