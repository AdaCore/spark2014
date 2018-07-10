pragma SPARK_Mode (On);

package body Main is

   Tot : constant Natural := Total.Compute (In_Ctxt => Total.A);

   function Get
     (Data    : in Total.Enum)
      return Total.Enum
   is
   begin
      return Total.Ctxt (Data);
   end Get;

end Main;
