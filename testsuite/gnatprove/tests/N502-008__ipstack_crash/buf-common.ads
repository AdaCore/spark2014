limited with Buf.No_Data;

package Buf.Common with
  SPARK_Mode,
  Abstract_State => State
is
   Buf_List : Integer;
   procedure Do_Some with
     Global   => (In_Out => (State, No_Data.State)),
     Annotate => (GNATprove, Always_Return);
end Buf.Common;
