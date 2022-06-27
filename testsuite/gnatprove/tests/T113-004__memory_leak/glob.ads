package Glob with SPARK_Mode is

   type T is access Integer;

   X : T;  -- @RESOURCE_LEAK:NONE
   Y : T;  -- @RESOURCE_LEAK:NONE
   Z : T;  -- @RESOURCE_LEAK:NONE

   procedure Proc with
     Global => (Input => X, Output => Y, In_Out => Z);

   procedure Wrap_Proc (B : Boolean);

   procedure Groc;

   procedure Wrap_Groc with
     Global => (In_Out => (X, Y, Z));

   procedure Local;

end Glob;
