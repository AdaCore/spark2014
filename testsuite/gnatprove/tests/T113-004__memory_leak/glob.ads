package Glob with SPARK_Mode is

   type T is access Integer;

   X : T;  -- @MEMORY_LEAK:NONE
   Y : T;  -- @MEMORY_LEAK:NONE
   Z : T;  -- @MEMORY_LEAK:NONE

   procedure Proc with
     Global => (Input => X, Output => Y, In_Out => Z);

   procedure Wrap_Proc (B : Boolean);

   procedure Groc;

   procedure Wrap_Groc with
     Global => (In_Out => (X, Y, Z));

   procedure Local;

end Glob;
