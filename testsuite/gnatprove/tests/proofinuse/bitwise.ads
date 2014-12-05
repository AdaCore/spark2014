with Types; use Types;

package Bitwise with
  SPARK_Mode
is
   --  from N811-037 (industrial user)
   procedure Mask (X : Unsigned_32; Res : out Unsigned_8);

   --  from N522-012 (industrial user)
   procedure Mask_8bits (X : in Unsigned_32; Res : out Unsigned_32);

   --  from N613-008 (internal test)
   procedure Shift_Is_Div (X : Unsigned_32; Res : out Unsigned_32);

   --  from NB17-028 (internal test)
   procedure Swap (X, Y : in out Unsigned_32);

end Bitwise;
