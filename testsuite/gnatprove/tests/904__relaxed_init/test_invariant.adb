procedure Test_Invariant with SPARK_Mode is
   package Nested is
      type T is private;
   private
      type T is new Integer with Type_Invariant => T > 0;
   end Nested;

   X : Nested.T with Relaxed_Initialization;

   type T is new Nested.T;

   Y : T with Relaxed_Initialization;
begin
   null;
end;
