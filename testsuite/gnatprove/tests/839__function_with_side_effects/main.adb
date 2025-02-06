pragma Extensions_Allowed (On);

procedure Main with SPARK_Mode is

   function F (X : in out Integer) return Integer with
     Global => null,
     Import,
     Side_Effects;

   procedure Test is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry);   -- @ASSERT:FAIL
         X : Integer := F (Y);
      end loop;
   end Test;
begin
   null;
end Main;
