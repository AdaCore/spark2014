package Disr_Type_Missing is

   type State is (A, B, C);

   type R (S : State) is record
      case S is
         when A =>
            X : Integer;
         when B =>
            Y : Natural;
      end case;
   end record;

   function Update (X : R) return R is
      (case X.S is
        when A => (S => C),
        when B => (S => A, X => 1),
        when C => (S => Y, Y => 2));

end Disr_Type_Missing;
