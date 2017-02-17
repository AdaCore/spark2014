pragma SPARK_Mode(On);

package body Test is

   procedure Decode_TLV(TLV_Information : out TLV_Record) is
   begin
      -- Bounded_Strings.Clear(TLV_Information.Filestore_Message);
      Bounded_Strings.Append(TLV_Information.Filestore_Message, 'X');
   end Decode_TLV;

end Test;
