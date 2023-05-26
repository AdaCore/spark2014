package body Transitive
  with SPARK_Mode => On
is

   function Prop_Transitive (A, B, C : in Natural) return Boolean
   -- Define the transitivity of Property
     with Global => null,
          Post   => (if Prop_Transitive'Result
                        and then Property (A, B)
                        and then Property (B, C)
                    then Property (A, C)),
          Ghost  => True,
          Import => True;

   procedure Shift (X : in out Natural)
     with Post => Property (X'Old, X)
   is
   begin
      -- Tell the proof tool that Property holds after this operation
      pragma Assume (Property (X, X / 2));
      X := X / 2;
   end Shift;

   procedure Change (X : in out Natural) is
      X_Last : Natural
        with Ghost => True;
   begin
      -- Tell the proof tool that the Property applies to to an unchanged value
      pragma Assume (Property (X, X));
      for I in 1 .. 10 loop
         pragma Loop_Invariant (Property (X'Loop_Entry, X));
         X_Last := X;
         Shift (X);
         -- Tell the proof tool that
         --    since the Property holds for X'Loop_Entry and X_Last  and
         --    the Property holds for X'Last and X then the property
         --    must hold for X'Loop_Entry and X
         pragma Assume (Prop_Transitive (X'Loop_Entry, X_Last, X));
      end loop;
   end Change;

end Transitive;
