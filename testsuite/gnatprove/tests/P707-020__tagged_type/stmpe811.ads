with TP;

package STMPE811 is

   type STMPE811_Device (Port : Integer) is
   limited new TP.Touch_Panel_Device with private;

private

   type STMPE811_Device (Port : Integer) is
   limited new TP.Touch_Panel_Device with record
      Dummy : Integer := 0;
   end record;

end;
