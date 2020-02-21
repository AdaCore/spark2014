procedure Main (Low, High : Integer) with Global => null is
   subtype T is Integer range Low .. High;

   procedure Swap (X, Y : in out String) with Pre => True is
      --  Dummy precondition to prevent inlining for proof
      Tmp : constant String := X;
   begin
      X := Y;
      Y := Tmp;
   end;

   S : String (T) := (others => ' ');

begin
   Swap (S (T), S (T)); --  Slices indexed by a subtype name

   Swap (S (T'First .. T'Last), S (T'First .. T'Last));
   --  Slices indexed by explicit ranges; semantically equivalent
end;
