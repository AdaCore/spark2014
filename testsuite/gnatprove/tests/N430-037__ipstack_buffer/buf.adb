with Buf.No_Data;
with Buf.Common;
package body Buf with
  SPARK_Mode,
  Refined_State => (State => (Buf.No_Data.State,
                              Buf.No_Data.Free_List,
                              Buf.Common.Buf_List))
is
   procedure P is null;
   --  dummy procedure to force a body
end Buf;
