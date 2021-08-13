procedure Ctx (T : in out Integer) is
   pragma Unreferenced (T);

   procedure Assert (Condition : Boolean)
     with Post => Condition, Global => null;

   procedure Update (A, B : in out Boolean)
     with Pre     => True,
          Post    => (A = (A'Old and B'Old)) and (B = not B'Old),
          Depends => (A => (A, B), B => B);

   ------------
   -- Assert --
   ------------

   procedure Assert (Condition : Boolean) is
   begin
      pragma Assert (Condition);
   end Assert;

   ------------
   -- Update --
   ------------

   procedure Update (A, B : in out Boolean) is
   begin
      A := A and B;
      B := not B;
   end Update;

   X, Y : Boolean := True;

--  Start of processing for Ctx

begin
   Update (X, Y); --  The API design requires Y to be modified by Update,
                  --  even though we don't intend to use it after the call.
   Assert (X);
end Ctx;
