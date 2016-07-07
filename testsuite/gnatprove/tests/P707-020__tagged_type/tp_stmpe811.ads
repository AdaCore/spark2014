with TP;
with STMPE811;

package TP_STMPE811 is

   type Touch_Panel_SMPT811 is
   limited new TP.Touch_Panel_Device with private;

private

   type Touch_Panel_SMPT811 is
   limited new STMPE811.STMPE811_Device (Port => 0) with null record;

end;
