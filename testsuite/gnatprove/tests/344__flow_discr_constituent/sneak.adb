procedure Sneak with Global => null is

   procedure Test (X : Integer; Y : out Integer)
   with Post    => Y = X,                   --  Data flow when executed
        Depends => (Y => null, null => X)   --  But flow fails to see it
   is
      type T (D : Integer) is null record;

      package P
        with Abstract_State => State
      is
         procedure Read (Y : out Integer)
         with Global => (Output => State);
         --  The implicitly generated dependency contract is:
         --    Depends => ((Y, State) => null, null => (Y, State))
         --  i.e. all outputs depend on all inputs.
      end;

      package body P
        with Refined_State => (State => Storage)
      is

         Storage : T (X);

         procedure Read (Y : out Integer)
         with Refined_Global => (Output => Storage)
         is
         begin
            Y := Storage.D;
         end;
      end;

   begin
      P.Read (Y);
   end;

   Y : Integer;

begin
   Test (12345, Y);
end;
