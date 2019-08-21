procedure P (Y : out Integer) is

   --  Routines One and Two are semantically the same, just
   --  * One has a DECLARE block that does nothing, while
   --  * Two has a NULL statement that does nothing.
   --  So they should trigger roughly the same flow messages.

   procedure One with
      Global => (Output => Y)
   is
      J : Natural := 0;
   begin
      loop
         declare
            procedure Dummy with
               Global => null
            is
            begin
               return;
            end Dummy;
         begin
            null;
         end;

         J := J + 1;
      end loop;

      Y := J;
   end One;

   procedure Two with
      Global => (Output => Y)
   is
      J : Natural := 0;
   begin
      loop
         null;

         J := J + 1;
      end loop;

      Y := J;
   end Two;

begin
   null;
end P;
