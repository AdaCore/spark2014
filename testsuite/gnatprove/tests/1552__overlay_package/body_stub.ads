package Body_Stub with SPARK_Mode is
   pragma Elaborate_Body;

   package Nested is
      X : Integer := 0;
      procedure Touch;
   end Nested;
end Body_Stub;
