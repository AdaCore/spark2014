with System;

package soc with Initializes => Periph
  --  Add Base to change proof error
is

   Base : constant System.Address := System'To_Address (16#00_00_00_00#);
   Periph : Integer with Import,Address => Base;

end soc;
