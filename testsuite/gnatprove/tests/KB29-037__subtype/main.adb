with Sub; use Sub;

procedure Main is pragma SPARK_Mode (On);
   X : constant S := 22;
   K : My_Int;
   Z : S := 22;
   TV : T := 22;
begin
   --  This call fails:
   -- Divide (Z);

   --  This call is OK:
   K := F (X);

   --  This call fails:
   -- K := Incorrect (X);

   --  This call fails:
   Divide_T (TV);
end Main;
