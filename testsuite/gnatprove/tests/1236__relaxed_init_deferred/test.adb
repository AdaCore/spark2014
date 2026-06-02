procedure Test with SPARK_Mode is
   type T;
   type T_Acc is access T;
   type R is record
      F, G : T_Acc;
   end record with Relaxed_Initialization;
   type T is record
      C : R;
   end record;

   X : T;
begin
   pragma Assert (X'Initialized);
end;
