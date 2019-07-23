with Ada.Numerics.Elementary_Functions;
with Ada.Numerics.Generic_Elementary_Functions;
with Ada.Text_IO;

package body P is

   package Global_Elementary_Functions is
     new Ada.Numerics.Generic_Elementary_Functions (Float);

   function Proxy1 (X : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Sin (X);
   end;

   function Proxy2 (X : Float) return Float is
      package Local_Elementary_Functions is
        new Ada.Numerics.Generic_Elementary_Functions (Float);
   begin
      return Local_Elementary_Functions.Sin (X);
   end;

   function Proxy3 (X : Float) return Float is
   begin
      return Global_Elementary_Functions.Sin (X);
   end;

   procedure Proxy4 (X : Float) is
      package My_IO is new Ada.Text_IO.Float_IO (Float);
   begin
      My_IO.Put (X);
   end;

   protected body PT is
      function S1 (X : Float) return Float is
      begin
         return Proxy1 (X);
      end S1;

      function S2 (X : Float) return Float is
      begin
         return Proxy2 (X);
      end S2;

      function S3 (X : Float) return Float is
      begin
         return Proxy3 (X);
      end S3;

      procedure Print (X : Float) is
      begin
         Proxy4 (X);
      end Print;
   end PT;
end P;
