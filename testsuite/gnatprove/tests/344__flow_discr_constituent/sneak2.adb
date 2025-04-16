procedure Sneak2 with Global => null is

   procedure Test (X : Integer; Y : out Integer)
   with Post    => Y = X,                   --  This always holds
        Depends => (Y => null, null => X)   --  Flow wrongly thinks this holds
   is
      package P
        with Abstract_State => State
      is
         procedure Read (Y : out Integer)
         with Global => (Output => State);
      end;

      package body P
        with Refined_State => (State => Storage)
      is
         Storage : String := (1 .. X => ' ');

         procedure Read (Y : out Integer)
         with Refined_Global => (Output => Storage)
         is
         begin
            Y := Storage'Last;
            Storage := (others => ' ');
         end;
      end;

   begin
      P.Read (Y);
   end;

   Y : Integer;

begin
   Test (12345, Y);
end;
