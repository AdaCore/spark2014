with System.Storage_Elements;

-- Clock
package body Clock
  with Refined_State => (Ticks => (Ticks_C,
                                   Tick_Ext))
is
  Ticks_C : Times;

  Tick_Ext : Times
    with Volatile,
         Async_Writers,
         Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

  function PF_Read return Times is (Ticks_C)
    with Refined_Global => Ticks_C;

  procedure Read (Time : out Times)
    with Refined_Global  => (Input  => Tick_Ext,
                             Output => Ticks_C),
         Refined_Depends => ((Ticks_C,
                              Time) => Tick_Ext)
  is
  begin
     Ticks_C := Tick_Ext;
     Time    := Ticks_C;
  end Read;

end Clock;
