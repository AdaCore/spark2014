limited with Buf.Common;

private package Buf.No_Data with
  SPARK_Mode,
  Abstract_State => (State with Part_Of => Buf.State)
is
   Free_List : Integer with Part_Of => Buf.State;

   procedure Free_Buffer with
     Global => (In_Out => (Common.Buf_List, Free_List));
end Buf.No_Data;
