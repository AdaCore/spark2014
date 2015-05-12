package Surfaces
  with Abstract_State => ((Elevators with External => Async_Readers),
                          (Ailerons  with External => Async_Readers),
                          (Rudder    with External => Async_Readers)),
       Initializes    => (Elevators, Ailerons, Rudder)
is
   type Controlangle is new Short_Short_Integer range -45 .. 45;

   procedure Move_Elevators (Position : in Controlangle)
     with Global  => (Output => Elevators),
          Depends => (Elevators => Position);

   procedure Move_Ailerons (Position : in Controlangle)
     with Global  => (Output => Ailerons),
          Depends => (Ailerons => Position);

   procedure Move_Rudder (Position : in Controlangle)
     with Global  => (Output => Rudder),
          Depends => (Rudder => Position);
end Surfaces;
