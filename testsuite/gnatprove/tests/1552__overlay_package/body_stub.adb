package body Body_Stub with SPARK_Mode is
   --  Nested's specification is in the enclosing package specification, so
   --  only its body stub shares this declaration list with the overlay.

   Y : Integer := 1 with Address => Nested.X'Address;
   package body Nested is separate;
end Body_Stub;
