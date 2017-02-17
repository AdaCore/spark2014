with Buf.Common;

package body Buf.No_Data with
  SPARK_Mode,
  Refined_State => (State => Free_List)
is
   Free_List : Integer;

   procedure Free_Buffer with
     Refined_Global => (In_Out => (Common.State, Free_List))
   is
   begin
      Common.Do_Some;
      Free_List := Free_List + 1;
   end Free_Buffer;

end Buf.No_Data;
