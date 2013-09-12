with System.Storage_Elements;

-- Clock
package body Clock is  

  Ticks : Times;

  Tick_Ext : Times;
  for Tick_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

  function PF_Read return Times is
     (Ticks);

  procedure Read (Time : out Times) is
  begin
     Ticks := Tick_Ext;
     Time  := Ticks;
  end Read;

end Clock;
