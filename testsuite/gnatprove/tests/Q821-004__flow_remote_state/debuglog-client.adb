with Debuglog.Sink;

package body Debuglog.Client
with
   SPARK_Mode => Off
is

   procedure Put (Item : Character)
   is
   begin
      Sink.Write_Character (Item => Item);
   end Put;

   procedure Put (Item : String)
   is
   begin
      for I in Item'Range loop
         Put (Item => Item (I));
      end loop;
   end Put;

end Debuglog.Client;
