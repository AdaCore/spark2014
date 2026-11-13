procedure Array_Limitation with SPARK_Mode is
   package T is
      type Byte is mod 256 with Size => 8;
      type A is array (1 .. 2) of Byte with Component_Size => 8;
      function Read return A with
        Import, Global => null, Potentially_Invalid => Read'Result;
      procedure Fill (X : out A) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X;
      type D is new A with Component_Size => 16;
   end T;
   package body T is
   end T;
   use T;
   X : D with Import, Potentially_Invalid;
   Result : D := Read with Potentially_Invalid;
   pragma Unreferenced (Result);
begin
   Fill (X);
end Array_Limitation;
