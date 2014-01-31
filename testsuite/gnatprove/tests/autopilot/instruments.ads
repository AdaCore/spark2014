package Instruments
  with Abstract_State => ((Altitude with External => Async_Writers),
                          (Bank with External => Async_Writers),
                          (Heading with External => Async_Writers),
                          (Heading_Bug with External => Async_Writers),
                          (Mach with External => Async_Writers),
                          (Pitch with External => Async_Writers),
                          (Rate_Of_Climb with External => Async_Writers),
                          (Slip with External => Async_Writers))
is
   type Feet is new Integer range 0 .. 50_000;
   type Bankangle is new Short_Short_Integer range -45 .. 45;
   type Headdegree is new Short_Integer range 0 .. 359;
   type Feetpermin is new Short_Integer range -6000 .. 6000;
   type Machnumber is new Short_Short_Integer range 0 .. 100;
   type Pitchangle is new Short_Short_Integer range -10 .. 20;
   type Slipangle is new Short_Short_Integer range -25 .. 25;

   procedure Read_Altimeter (Present_Altitude : out Feet)
     with Global  => (Input  => Altitude),
          Depends => (Present_Altitude => Altitude);

   procedure Read_Bank_Indicator (Present_Bank : out Bankangle)
     with Global  => (Input  => Bank),
          Depends => (Present_Bank => Bank);

   procedure Read_Compass (Present_Heading : out Headdegree)
     with Global  => (Input  => Heading),
          Depends => (Present_Heading => Heading);

   procedure Read_Heading_Bug (Target_Heading : out Headdegree)
     with Global  => (Input  => Heading_Bug),
          Depends => (Target_Heading => Heading_Bug);

   procedure Read_Mach_Indicator (Present_Mach : out Machnumber)
     with Global  => (Input  => Mach),
          Depends => (Present_Mach => Mach);

   procedure Read_Pitch_Indicator (Present_Pitch : out Pitchangle)
     with Global  => (Input  => Pitch),
          Depends => (Present_Pitch => Pitch);

   procedure Read_VSI (Present_Rate_Of_Climb : out Feetpermin)
     with Global  => (Input  => Rate_Of_Climb),
          Depends => (Present_Rate_Of_Climb => Rate_Of_Climb);

   procedure Read_Slip_Indicator (Present_Slip : out Slipangle)
     with Global  => (Input  => Slip),
          Depends => (Present_Slip => Slip);
end Instruments;
