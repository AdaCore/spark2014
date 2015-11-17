package Prot
  with SPARK_Mode
is
   type Int is record
      V : Integer;
   end record;
   subtype Nat is Int with Predicate => Nat.V >= 0;

   protected type T is
      procedure Check;
   private
      Data : Nat := (V => 0);
   end T;
end Prot;
