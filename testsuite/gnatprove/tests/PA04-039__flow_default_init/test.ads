pragma SPARK_Mode(On);

with Bounded_Strings;

package Test is

   type TLV_Record is
      record
         Filestore_Message : Bounded_Strings.Bounded_String(60);
      end record;

   procedure Decode_TLV(TLV_Information : out TLV_Record)
     with
       Global => null,
       Depends => (TLV_Information => TLV_Information);

end Test;
