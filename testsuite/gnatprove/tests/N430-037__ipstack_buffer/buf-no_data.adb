with Buf.Common;

package body Buf.No_Data with
  SPARK_Mode,
  Refined_State => (State => Buf2_List)
is
   Buf2_List : Integer;

   procedure Free_Buffer is
   begin
      Common.Buf_List := Common.Buf_List + 1;
      Free_List := Free_List + 1;
   end Free_Buffer;

end Buf.No_Data;
