with Degrees, Instruments, Scale, Surfaces;

package AP
  with Abstract_State => (State with External => Async_Writers),
       Initializes    => State
is
   procedure Control
     with Global  => (Input  => (Instruments.Altitude,
                                 Instruments.Bank,
                                 Instruments.Heading,
                                 Instruments.Heading_Bug,
                                 Instruments.Mach,
                                 Instruments.Pitch,
                                 Instruments.Rate_Of_Climb,
                                 Instruments.Slip),
                      In_Out => (Surfaces.Ailerons,
                                 Surfaces.Elevators,
                                 Surfaces.Rudder,
                                 State)),
          Depends => (State              =>+ (Instruments.Altitude,
                                              Instruments.Bank,
                                              Instruments.Pitch,
                                              Instruments.Slip),
                      Surfaces.Ailerons  =>+ (Instruments.Bank,
                                              Instruments.Heading,
                                              Instruments.Heading_Bug,
                                              Instruments.Mach,
                                              State),
                      Surfaces.Elevators =>+ (Instruments.Altitude,
                                              Instruments.Mach,
                                              Instruments.Pitch,
                                              Instruments.Rate_Of_Climb,
                                              State),
                      Surfaces.Rudder    =>+ (Instruments.Mach,
                                              Instruments.Slip,
                                              State));
end AP;
