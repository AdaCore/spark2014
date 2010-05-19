package Instruments
  --# own in Altitude      : Feet;
  --#     in Bank          : Bankangle;
  --#     in Heading       : Headdegree;
  --#     in Heading_Bug   : Headdegree;
  --#     in Mach          : Machnumber;
  --#     in Pitch         : Pitchangle;
  --#     in Rate_Of_Climb : Feetpermin;
  --#     in Slip          : Slipangle;
is
   type Feet       is range     0 .. 50_000;
   --# assert Feet'Base is Integer;

   type Bankangle  is range   -45 .. 45;
   --# assert Bankangle'Base is Short_Short_Integer;

   type Headdegree is range     0 .. 359;
   --# assert Headdegree'Base is Short_Integer;

   type Feetpermin is range -6000 .. 6000;
   --# assert Feetpermin'Base is Short_Integer;

   type Machnumber is range     0 .. 100;
   --# assert Machnumber'Base is Short_Short_Integer;

   type Pitchangle is range   -10 .. 20;
   --# assert Pitchangle'Base is Short_Short_Integer;

   type Slipangle  is range   -25 .. 25;
   --# assert Slipangle'Base is Short_Short_Integer;

   procedure Read_Altimeter(Present_Altitude : out Feet);
   --# global in Altitude;
   --# derives Present_Altitude from Altitude;

   procedure Read_Bank_Indicator(Present_Bank : out Bankangle);
   --# global in Bank;
   --# derives Present_Bank from Bank;

   procedure Read_Compass(Present_Heading : out Headdegree);
   --# global in Heading;
   --# derives Present_Heading from Heading;

   procedure Read_Heading_Bug(Target_Heading : out Headdegree);
   --# global in Heading_Bug;
   --# derives Target_Heading from Heading_Bug;

   procedure Read_Mach_Indicator(Present_Mach : out Machnumber);
   --# global in Mach;
   --# derives Present_Mach from Mach;

   procedure Read_Pitch_Indicator(Present_Pitch : out Pitchangle);
   --# global in Pitch;
   --# derives Present_Pitch from Pitch;

   procedure Read_VSI(Present_Rate_Of_Climb : out Feetpermin);
   --# global in Rate_Of_Climb;
   --# derives Present_Rate_Of_Climb from Rate_Of_Climb;

   procedure Read_Slip_Indicator(Present_Slip : out Slipangle);
   --# global in Slip;
   --# derives Present_Slip from Slip;

end Instruments;
