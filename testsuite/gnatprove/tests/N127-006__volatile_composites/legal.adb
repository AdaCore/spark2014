with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;
package body Legal
  with SPARK_Mode => On
is
   -- Read a scalar object
   procedure RV1 (X : out Integer)
   is
   begin
      X := V1; -- OK
   end RV1;

   -- Write a scalar object
   procedure WV1 (X : in Integer)
   is
   begin
      V1 := X; -- OK
   end WV1;


   -- read volatile record field
   procedure RV2 (X : out Boolean)
   is
   begin
      X := V2.F2; -- illegal in 14.0.1. Should be legal in 14.0.2+
   end RV2;

   -- write volatile record field
   procedure WV2 (X : in Boolean)
   is
   begin
      V2.F2 := X; -- illegal in 14.0.1. Should be legal in 14.0.2+
   end WV2;



   -- read volatile array element
   procedure RV3 (X : out Integer)
   is
   begin
      X := V3 (3); -- illegal in 14.0.1. Should be legal in 14.0.2+
   end RV3;

   -- read volatile array element via rename of Unchecked_Conversion
   procedure RV3UC (X : out Integer)
   is
      function C is new Ada.Unchecked_Conversion (Integer, Unsigned_32);
      Tmp : Unsigned_32 renames C (V3 (3)); -- illegal in 14.0.1. Should be legal in 14.0.2+
   begin
      X := Integer (Tmp);
   end RV3UC;

   -- write volatile array element
   procedure WV3 (X : in Integer)
   is
   begin
      V3 (3) := X; -- illegal in 14.0.1. Should be legal in 14.0.2+
   end WV3;


   -- read field of volatile array element
   procedure RV4 (X : out Boolean)
   is
   begin
      X := V4 (3).F2; -- illegal in 14.0.1. Should be legal in 14.0.2+
   end RV4;

   -- write field of volatile array element
   procedure WV4 (X : in Boolean)
   is
   begin
      V4 (3).F2 := X; -- illegal in 14.0.1. Should be legal in 14.0.2+
   end WV4;

   -- read field of volatile array element via locally initialized Tmp
   procedure RV4b (X : out Boolean)
   is
      Tmp : Boolean := V4 (3).F2; -- illegal in 14.0.1. Should be legal in 14.0.2+
   begin
      X := Tmp;
   end RV4b;

end Legal;
