procedure Test with SPARK_Mode is

   package Nested is
      type Gen is private;

      function Read (X : Gen) return Integer with
        Global => null,
        Import;

      function Random (X : Gen) return Integer with
        Global => null,
        Import,
        Side_Effects;
      pragma Annotate (GNATprove, Mutable_In_Parameters, Gen);
   private
      pragma SPARK_Mode (Off);
      type Gen is access Integer;
   end Nested;
   use Nested;

   G : Gen;

   procedure Test is
      X : Integer;
   begin
      for I in 1 .. 100 loop
         pragma Assert (Read (G) = Read (G)'Loop_Entry);   -- @ASSERT:FAIL
         X := Random (G);
      end loop;
   end Test;

begin
   null;
end;
