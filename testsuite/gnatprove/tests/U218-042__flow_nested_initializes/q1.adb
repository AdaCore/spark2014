package body Q1 with Refined_State => (State1 => Q2.State2) is
   package Q2 with Abstract_State => State2 is
      procedure Dummy with Global => null;
   end Q2;
   package body Q2 with Refined_State => (State2 => (X, Q3.State3)) is
      X : Boolean := True;

      package Q3 with Abstract_State => State3 is
         procedure Dummy with Global => null;
      end Q3;
      package body Q3 with Refined_State => (State3 => Y) is
         Y : Boolean := False;
         procedure Dummy is null;  --  Q3.Dummy
      end Q3;

      procedure Dummy is null;  --  Q2.Dummy

   end Q2;
   procedure Dummy is null;  --  Q1.Dummy
end Q1;
