with System.Storage_Elements;

-- Clock
package body Clock
is
   Tick_Ext : Times
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read (Time : out Times)
   is
   begin
      Time := Tick_Ext;
   end Read;

end Clock;
