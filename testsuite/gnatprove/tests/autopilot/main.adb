with AP, Instruments, Surfaces;

procedure Main
  with Global  => (Input  => (Instruments.Altitude,
                              Instruments.Bank,
                              Instruments.Heading,
                              Instruments.Heading_Bug,
                              Instruments.Mach,
                              Instruments.Pitch,
                              Instruments.Rate_Of_Climb,
                              Instruments.Slip),
                   Output => (Surfaces.Ailerons,
                              Surfaces.Elevators,
                              Surfaces.Rudder),
                   In_Out => AP.State),
       Depends => (AP.State =>+ (Instruments.Altitude,
                                 Instruments.Bank,
                                 Instruments.Pitch,
                                 Instruments.Slip),
                   Surfaces.Ailerons => (AP.State,
                                         Instruments.Altitude,
                                         Instruments.Bank,
                                         Instruments.Heading,
                                         Instruments.Heading_Bug,
                                         Instruments.Mach,
                                         Instruments.Pitch,
                                         Instruments.Slip),
                   Surfaces.Elevators => (AP.State,
                                          Instruments.Altitude,
                                          Instruments.Bank,
                                          Instruments.Mach,
                                          Instruments.Pitch,
                                          Instruments.Rate_Of_Climb,
                                          Instruments.Slip),
                   Surfaces.Rudder => (AP.State,
                                       Instruments.Altitude,
                                       Instruments.Bank,
                                       Instruments.Mach,
                                       Instruments.Pitch,
                                       Instruments.Slip))
is
begin
   loop
      AP.Control;
   end loop;
end Main;
