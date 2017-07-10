procedure Essai05 with
   Spark_Mode is
   type Index_A is range -3 .. 15;
   subtype Index_B is Index_A range 3 .. Index_A'Last;

   type Array_A is array (Index_A range <>) of Integer;
   type Array_B is array (Index_B range <>) of Integer;

   function Conv2 (V : Array_A) return Array_B
     with Global => null,
         Pre => True;

   function Conv (V : Array_A) return Array_B is
      R : Array_B (V'Range) := (others => 0); --@RANGE_CHECK:FAIL
   begin
      for I in V'Range loop
         R (I) := V (I);
      end loop;
      return R;
   end Conv;

   function Conv2 (V : Array_A) return Array_B is
      R : Array_B (V'Range) := (others => 0); --@RANGE_CHECK:FAIL
   begin
      for I in V'Range loop
         R (I) := V (I);
      end loop;
      return R;
   end Conv2;

   A : Array_A := (0, 1, 2);
   B : Array_B := Conv (A); --

begin
   null;
end Essai05;
