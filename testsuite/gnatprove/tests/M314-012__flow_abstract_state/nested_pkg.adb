package body Nested_Pkg
is
   pragma SPARK_Mode (On);

   function G return Boolean is (True);

   package X is
      function F return Boolean;

      procedure Wibble with Pre => G;
   end X;

   package body X is
      function F return Boolean is (True);

      procedure Wibble is
      begin
         --  precondition. g body is visible
         null;
      end Wibble;

      procedure Test is
      begin
         pragma Assert (F);  --  body visible

         pragma Assert (G);  --  body visible

         Wibble;             --  body visible
      end Test;

   end X;

   procedure Test
   is
   begin
      pragma Assert (X.F);   --  spec visible

      pragma Assert (G);     --  body visible

      X.Wibble;              --  spec visible
   end Test;

end Nested_Pkg;
