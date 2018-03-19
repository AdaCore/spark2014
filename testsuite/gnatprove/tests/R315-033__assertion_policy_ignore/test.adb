package body Test
is

   procedure Copy_Byte_Array
     (Src        : in     Byte_Array;
      Src_First  : in     Natural;
      Src_Length : in     Natural;
      Dest       : in out Byte_Array;
      Index      : in     Natural)
   is
   begin
      for I in Natural range 0 .. Src_Length - 1
      loop
         Dest (Index + I) := Src (Src_First + I);
         pragma Loop_Invariant
           (for all  J in Natural range Dest'Range =>
             (if J      in Index .. Index + I then
                 (Dest (J) = Src (Src_First + J - Index)) else
                 (Dest (J) = Dest'Loop_Entry (J))));
      end loop;
   end Copy_Byte_Array;

end Test;
