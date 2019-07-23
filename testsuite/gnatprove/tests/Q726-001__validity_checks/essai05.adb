procedure Essai05 with
   Spark_Mode is
   type Index_A is range -3 .. 15;
   subtype Index_B is Index_A range 3 .. Index_A'Last;

   type Array_A is array (Index_A range <>) of Integer;
   type Array_B is array (Index_B range <>) of Integer;

   function Conv (V : Array_A) return Array_B is
--        R : Array_B (V'First .. V'Last); -- flow: medium: "R" might not be initialized, prove 4: essai05.adb:22:19: medium: range check might fail
--        R : Array_B (V'First .. V'Last) := (others => 0); -- flow: ok, prove 4: essai05.adb:22:19: medium: range check might fail
--        R : Array_B (V'Range); -- flow: medium: "R" might not be initialized
      R : Array_B (V'Range) := (others => 0); -- flow: ok, prove 4: ok
   begin
      for I in V'Range loop
         R (I) := V (I);
      end loop;
      return R;
   end Conv;

   A : Array_A := (0, 1, 2);
   B : Array_B := Conv (A); --

begin
   null;
end Essai05;
