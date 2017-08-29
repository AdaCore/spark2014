with Debuglog.Client;

package body Debug_Ops
with
   SPARK_Mode => Off
is

   procedure Dump_State
   is
   begin
      Debuglog.Client.Put (Item => "Msg");
   end Dump_State;

end Debug_Ops;
