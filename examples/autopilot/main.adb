with AP;
--# inherit Surfaces, Instruments, AP;
--# main_program;
procedure Main
   --# global in out AP.State;
   --#           out Surfaces.Elevators,
   --#               Surfaces.Ailerons,
   --#               Surfaces.Rudder;
   --#        in     Instruments.Altitude,
   --#               Instruments.Bank,
   --#               Instruments.Heading,
   --#               Instruments.Heading_Bug,
   --#               Instruments.Mach,
   --#               Instruments.Pitch,
   --#               Instruments.Rate_Of_Climb,
   --#               Instruments.Slip;
   --# derives AP.State
   --#          from *,
   --#               Instruments.Altitude,
   --#               Instruments.Bank,
   --#               Instruments.Pitch,
   --#               Instruments.Slip &
   --#  Surfaces.Elevators
   --#          from
   --#               AP.State,
   --#               Instruments.Altitude,
   --#               Instruments.Bank,
   --#               Instruments.Mach,
   --#               Instruments.Pitch,
   --#               Instruments.Rate_Of_Climb,
   --#               Instruments.Slip
   --#          &
   --#  Surfaces.Ailerons
   --#          from
   --#               AP.State,
   --#               Instruments.Altitude,
   --#               Instruments.Bank,
   --#               Instruments.Heading,
   --#               Instruments.Heading_Bug,
   --#               Instruments.Mach,
   --#               Instruments.Pitch,
   --#               Instruments.Slip  &
   --#  Surfaces.Rudder
   --#          from AP.State,
   --#               Instruments.Altitude,
   --#               Instruments.Bank,
   --#               Instruments.Mach,
   --#               Instruments.Pitch,
   --#               Instruments.Slip
   --#  ;
is
begin

   loop
      AP.Control;
   end loop;
end Main;
