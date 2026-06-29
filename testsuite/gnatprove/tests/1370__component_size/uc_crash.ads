pragma Ada_2022;
with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

package UC_Crash with SPARK_Mode is

   --  Test that size of component can be computed for an array with bounds
   --  that are not statically known.

   type My4 is record
      A : Integer_32;
   end record;

   type Pad is
     array (Positive range 1 .. 8 - My4'Object_Size / 8) of Unsigned_8;

   type Padded is record
      Obj : My4;
      P   : Pad;
   end record
   with Alignment => 1;

   type Stor is record
      D : Unsigned_64;
   end record;

   function To_Raw is new Ada.Unchecked_Conversion (Padded, Stor);

   function F (X : Padded) return Stor is (To_Raw (X));

end UC_Crash;
