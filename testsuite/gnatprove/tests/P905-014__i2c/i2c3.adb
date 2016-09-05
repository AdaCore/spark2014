
with I2C3_Support;

package body I2C3
with
  SPARK_Mode => On
is

   Initialization_Done : Boolean := False;

   function Initialized return Boolean
     is (Initialization_Done);

   procedure Initialize
   is
   begin
      I2C3_Support.Instantiation.Initialize;
      Initialization_Done := True;
   end Initialize;

end I2C3;
