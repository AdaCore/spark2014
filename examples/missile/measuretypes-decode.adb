-- Bus decoding for measuretypes
--
-- $Log: measuretypes-decode.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/01 18:19:54  adi
-- Added Newton
--
-- Revision 1.2  2003/08/27 21:01:03  adi
-- Added Kelvin
--
-- Revision 1.1  2003/08/25 14:42:40  adi
-- Initial revision
--
--
with systemTypes;
package body Measuretypes.decode is
   Word_Max : constant := (1 + Bus.Word'Last);

   function Kelvin(B : Bus.Word) return Measuretypes.Kelvin
   is begin
      return Measuretypes.Kelvin(B);
   end Kelvin;

   function Newton(Lo, Hi : Bus.Word) return Measuretypes.Newton
   is
      Ans : Measuretypes.Newton;
      Negative : Boolean;
      Tmp_Hi : Bus.Word;
   begin
      Tmp_Hi := Hi;
      if Tmp_Hi >= 16#8000# then
         Tmp_Hi := Tmp_Hi - 16#8000#;
         Negative := True;
      else
         Negative := False;
      end if;
      Ans := Measuretypes.Newton(Lo) +
        Measuretypes.Newton(Tmp_Hi)*Word_Max;
      if Negative then
         Ans := -Ans;
      end if;
      return Ans;
   end Newton;


   procedure Meter(M : out Measuretypes.Meter;
                   Lo, Hi : in bus.Word)
   is
   begin
      M := Measuretypes.Meter(Lo) +
        Measuretypes.Meter(Hi)*Word_Max;
   end Meter;

   -- decode in a single word
   function Meter_Single(B : Bus.Word)
     return Measuretypes.meter
   is
   begin
      return Measuretypes.Meter(B);
   end Meter_Single;

   function Meter_Per_Sec(B : Bus.Word)
     return Measuretypes.Meter_Per_Sec
   is
      Vel : Measuretypes.Meter_Per_Sec;
   begin
      if b >= 16#8000# then
         Vel := -(Measuretypes.Meter_Per_Sec(B - 16#8000#));
      else
         Vel := Measuretypes.Meter_Per_Sec(B);
      end if;
      return Vel;
   end Meter_Per_Sec;

   function Bit4_Array(B : Bus.Word)
     return Measuretypes.Bit4_Array
   is
      Grid : Measuretypes.Bit4_Array := Measuretypes.Bit4_Array'
        (others => Measuretypes.Bit4_Slice'(others => False));
      Datum, Add_Bit : Bus.Word;
   begin
      Datum := b;
      Add_Bit := 16#8000#;
      for Actual_X in reverse Measuretypes.bit4_Range loop
         --# assert actual_x in measuretypes.bit4_range;
         for Actual_Y in reverse Measuretypes.bit4_Range loop
         --# assert actual_x in measuretypes.bit4_range and
         --#        actual_y in measuretypes.bit4_range;
            if Datum >= Add_Bit then
               grid(Actual_X)(Actual_Y) := True;
               Datum := Datum - Add_Bit;
            end if;
            Add_Bit := Add_Bit / 2;
         end loop;
      end loop;
      return grid;
   end Bit4_array;


end Measuretypes.decode;
