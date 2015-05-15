package body InvertInjection is

   procedure Invert (A : ElementArray; B : in out ElementArray) is
   begin
      for I in Element'Range loop
         pragma Loop_Invariant
           (for all J in Element'First .. (I-1) => B (A (J)) = J);
         B (A (I)) := I;
      end loop;
      pragma Assert (for all J in Element'Range => B (A (J)) = J);
   end Invert;

end InvertInjection;
