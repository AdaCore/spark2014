package Surfaces
  --# own out Elevators, out Ailerons, out Rudder;
is
   type Controlangle is range -45 .. 45;
   --# assert Controlangle'Base is Short_Short_Integer;

   procedure Move_Elevators(Position : in Controlangle);
   --# global out Elevators;
   --# derives Elevators from Position;

   procedure Move_Ailerons(Position : in Controlangle);
   --# global out Ailerons;
   --# derives Ailerons from Position;

   procedure Move_Rudder(Position : in Controlangle);
   --# global out Rudder;
   --# derives Rudder from Position;
end Surfaces;
