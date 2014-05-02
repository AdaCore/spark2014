limited with Buf.Common;

package Buf.No_Data with
  SPARK_Mode,
  Abstract_State => State
is
   procedure Free_Buffer with
     Global => (In_Out => (Common.State, State));
end Buf.No_Data;
