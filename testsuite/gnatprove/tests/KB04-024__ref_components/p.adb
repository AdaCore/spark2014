procedure P (Havok_A, Havok_B : Boolean) is
   type T is array (1 .. 2) of Boolean;
   X : T := (others => Havok_A);

   type R is record
      B : Boolean;
   end record;

   Y : R := (B => Havok_B);


   procedure Assign (B : in out Boolean) is
   begin
      B := True;
   end Assign;
begin
   Assign (X (1));
   Assign (Y.B);
end P;

