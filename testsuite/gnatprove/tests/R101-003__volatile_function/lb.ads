package LB
with
   SPARK_Mode
is
   type X (<>) is limited private;

   function Init return X;

private
   type A is limited record
      E : Integer;
   end record
   with
      Volatile, Async_Readers, Object_Size => 32;

   type X is limited new A;
end LB;
