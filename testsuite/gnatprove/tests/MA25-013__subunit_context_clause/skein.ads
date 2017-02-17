with System;
with Interfaces;

use type Interfaces.Unsigned_64;

package Skein
  with SPARK_Mode => On
is
   procedure Set_Flags (F : in out Integer);
end Skein;
