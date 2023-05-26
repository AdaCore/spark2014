package Test_Invariants with SPARK_Mode is

   E : exception;

   type T is private;

   --  X is not passed by reference, the invariant might be broken on exceptions

   procedure P (B : Boolean; X : in out T) with
     Exceptional_Cases => (E => True);

   --  X is passed by reference, the invariant shall be maintained on exceptions

   procedure Q (B : Boolean; X : aliased in out T) with --@INVARIANT_CHECK:FAIL
     Exceptional_Cases => (E => True);

private

   type T is record
      F : Integer := 0;
      G : Integer := 1;
   end record with
     Type_Invariant => F < G;

end Test_Invariants;
