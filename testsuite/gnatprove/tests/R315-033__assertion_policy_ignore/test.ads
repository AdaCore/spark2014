package Test
is
   type Byte is mod 2 ** 8;
   subtype Byte_Array_Range is Natural range Natural'First .. Natural'Last - 1;
   type Byte_Array is array (Byte_Array_Range range <>) of Byte;

   procedure Copy_Byte_Array
     (Src        : in     Byte_Array;
      Src_First  : in     Natural;
      Src_Length : in     Natural;
      Dest       : in out Byte_Array;
      Index      : in     Natural)
   with
      Global  => null,
      Depends => (Dest =>+ (Src, Src_First, Src_Length, Index)),
      Pre     =>
        (Src'First              <= Src_First and
         Src_First + Src_Length <= Src'Last + 1 and
         Dest'First             <= Index and
         Index + Src_Length     <= Dest'Last + 1),
      Post    =>
        (for all  I in Natural range Dest'Range =>
          (if I in Index .. Index + Src_Length - 1 then
             (Dest (I) = Src (Src_First + I - Index)) else
             (Dest (I) = Dest'Old (I))));

end Test;
