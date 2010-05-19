-- Bus encoding for measuretypes
--
-- $Log: measuretypes-encode.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/09/01 18:24:21  adi
-- Added Newton
--
-- Revision 1.3  2003/08/27 20:42:29  adi
-- Added Kelvin
--
-- Revision 1.2  2003/08/25 13:32:45  adi
-- Added bit4_array
--
-- Revision 1.1  2003/08/24 19:14:59  adi
-- Initial revision
--
--
with systemTypes;
package body Measuretypes.encode is
   Word_Max : constant := (1 + Bus.Word'Last);

   function Kelvin(K : Measuretypes.Kelvin) return Bus.Word
   is begin
      return Bus.Word(K);
   end Kelvin;

   procedure Newton(N : in Measuretypes.Newton;
                    Lo, Hi : out Bus.Word)
   is
      Tmp : Measuretypes.Newton;
      Negative : Boolean;
   begin
      Tmp := N;
      if (Tmp < 0) then
         Tmp := -Tmp;
         Negative := True;
      else
         Negative := False;
      end if;
      Lo := Bus.Word(Tmp mod Word_Max);
      Hi := Bus.Word(Tmp / Word_Max);
      if Negative then
         Hi := Hi + 16#8000#;
      end if;
   end Newton;

   procedure Meter(M : in Measuretypes.Meter;
                   Lo, Hi : out bus.Word)
   is
   begin
      Lo := Bus.Word(M mod Word_max);
      Hi := Bus.Word(M / Word_max);
   end Meter;

   -- Encode in a single word, with restriction
   function Meter_Single(M : Measuretypes.Meter;
                         R : Measuretypes.Meter)
     return Bus.word
   is
      Distance : Measuretypes.Meter;
   begin
      if m < 0 then
         Distance := 0;
      elsif m > R then
         Distance := R;
      else
         Distance := M;
      end if;
      if distance > Measuretypes.Meter(Bus.Word'Last) then
         distance := Measuretypes.Meter(Bus.Word'Last);
      end if;
      return Bus.Word(distance);
   end Meter_Single;

   procedure Meter_Per_Sec(V : in Measuretypes.Meter_Per_Sec;
                           W : out bus.Word)
   is
      Negative : Boolean;
      Vel : Measuretypes.Meter_Per_Sec;
   begin
      if V < 0 then
         Negative := True;
         Vel := -V;
      else
         Negative := False;
         Vel := V;
      end if;
      w := Bus.Word(Vel);
      if Negative then
         w := w + 16#8000#;
      end if;
   end Meter_Per_Sec;

   function Bit4_Array(A : in Measuretypes.Bit4_Array)
                      return Bus.word
   is
      Datum, Add_Bit : Bus.Word;
   begin
      Datum := 0;
      Add_Bit := 1;
      for Actual_X in Measuretypes.bit4_Range loop
         --# assert actual_x in measuretypes.bit4_range;
         for Actual_Y in Measuretypes.bit4_Range loop
         --# assert actual_x in measuretypes.bit4_range and
         --#        actual_y in measuretypes.bit4_range;
            if A(Actual_X)(Actual_Y) then
               Datum := Datum + Add_Bit;
            end if;
            if Add_Bit <= 16#4000# then
               Add_Bit := Add_Bit * 2;
            end if;
         end loop;
      end loop;
      return Datum;
   end Bit4_array;


end Measuretypes.encode;
