--  Demonstration code for the AdaPilot project
--  (http://adapilot.likeabird.eu).
--  Copyright (C) 2016 Simon Wright <simon@pushface.org>

with STM32_SVD;

package I2C3
with
  SPARK_Mode => On,
  Elaborate_Body
is

   function Initialized return Boolean;

   procedure Initialize
   with
     Pre => not Initialized,
     Post => Initialized;

private

end I2C3;
