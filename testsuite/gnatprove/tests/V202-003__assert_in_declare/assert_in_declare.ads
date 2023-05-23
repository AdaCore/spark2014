package Assert_In_Declare with SPARK_Mode is

   function Rand (X : Integer) return Integer with Import;

   function F return Integer is
      ((declare
         Result : constant Integer := 0;
         pragma Assert (Result < 10);
       begin Result));

   function F_2 return Integer is
      ((declare
         Result : constant Integer := Rand (0);
         pragma Assert (Result < 10);
         pragma Assert (Result < 20);
       begin Result));

   function F_3 return Integer is
      ((declare
         Result : constant Integer := Rand (0);
         pragma Assert (Result < 10);
       begin Result));
   pragma Annotate (GNATprove, Intentional, "assertion might fail", "This is an assumption.");

end Assert_In_Declare;
