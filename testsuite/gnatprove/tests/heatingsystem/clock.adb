with System.Storage_Elements;

-- Clock
package body Clock
  with Refined_State => (Ticks => Tick_Ext)
is
   Tick_Ext : Times
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);
   pragma Annotate(Gnatprove, Intentional, "constraints on bit representation","");

   procedure Read (Time : out Times)
     with Refined_Global  => Tick_Ext,
          Refined_Depends => (Time => Tick_Ext)
   is
   begin
      Time := Tick_Ext;
   end Read;

end Clock;
