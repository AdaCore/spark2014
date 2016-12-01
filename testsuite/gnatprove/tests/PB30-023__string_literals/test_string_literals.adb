procedure Test_String_Literals with SPARK_Mode is
   S : String := "toto";
   T : String (5 .. 8) := "toto";

   function Id (X : String) return String is (X);
begin
   pragma Assert (Id (S)'First = 1);
   pragma Assert (Id (T)'First = 5);
   pragma Assert (S = Id (T));
end Test_String_Literals;
