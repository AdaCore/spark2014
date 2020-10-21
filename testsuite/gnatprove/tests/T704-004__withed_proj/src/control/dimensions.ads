--  Copy of Dimensions with Long_Float and SPARK_Mode

pragma SPARK_Mode;

with Ada.Numerics;
with Ada.Numerics.Generic_Elementary_Functions;

package Dimensions is
   pragma Pure;

   e  : constant := Ada.Numerics.e;
   Pi : constant := Ada.Numerics.Pi;

   --  Dimensioned type Mks_Type

   type Mks_Type is new Long_Float
     with
      Dimension_System => (
        (Unit_Name => Meter,    Unit_Symbol => 'm',   Dim_Symbol => 'L'),
        (Unit_Name => Kilogram, Unit_Symbol => "kg",  Dim_Symbol => 'M'),
        (Unit_Name => Second,   Unit_Symbol => 's',   Dim_Symbol => 'T'),
        (Unit_Name => Ampere,   Unit_Symbol => 'A',   Dim_Symbol => 'I'),
        (Unit_Name => Kelvin,   Unit_Symbol => 'K',   Dim_Symbol => '@'),
        (Unit_Name => Mole,     Unit_Symbol => "mol", Dim_Symbol => 'N'),
        (Unit_Name => Candela,  Unit_Symbol => "cd",  Dim_Symbol => 'J'));

   --  SI Base dimensioned subtypes

   subtype Unconstrained_Length is Mks_Type
     with
      Dimension => (Symbol => 'm',
        Meter  => 1,
        others => 0);

   subtype Mass is Mks_Type
     with
      Dimension => (Symbol => "kg",
        Kilogram => 1,
        others   => 0);

   subtype Unconstrained_Time is Mks_Type
     with
      Dimension => (Symbol => 's',
        Second => 1,
        others => 0);

   subtype Electric_Current is Mks_Type
     with
      Dimension => (Symbol => 'A',
        Ampere => 1,
        others => 0);

   subtype Thermodynamic_Temperature is Mks_Type
     with
      Dimension => (Symbol => 'K',
        Kelvin => 1,
        others => 0);

   subtype Amount_Of_Substance is Mks_Type
     with
      Dimension => (Symbol => "mol",
        Mole   => 1,
        others => 0);

   subtype Luminous_Intensity is Mks_Type
     with
      Dimension => (Symbol => "cd",
        Candela => 1,
        others  => 0);

   --  Initialize SI Base unit values

   --  Turn off the all the dimension warnings for these basic assignments
   --  since otherwise we would get complaints about assigning dimensionless
   --  values to dimensioned subtypes (we can't assign 1.0*m to m).

   pragma Warnings (Off, "*assumed to be*");

   m   : constant Unconstrained_Length      := 1.0;
   kg  : constant Mass                      := 1.0;
   s   : constant Unconstrained_Time        := 1.0;
   A   : constant Electric_Current          := 1.0;
   K   : constant Thermodynamic_Temperature := 1.0;
   mol : constant Amount_Of_Substance       := 1.0;
   cd  : constant Luminous_Intensity        := 1.0;

   pragma Warnings (On, "*assumed to be*");

   --  SI Derived dimensioned subtypes

   subtype Absorbed_Dose is Mks_Type
     with
      Dimension => (Symbol => "Gy",
        Meter  =>  2,
        Second => -2,
        others =>  0);

   subtype Angle is Mks_Type
     with
      Dimension => (Symbol => "rad",
        others => 0);

   subtype Unconstrained_Area is Mks_Type
     with
      Dimension => (
        Meter  => 2,
        others => 0);

   subtype Catalytic_Activity is Mks_Type
     with
      Dimension => (Symbol => "kat",
        Second => -1,
        Mole   => 1,
        others => 0);

   subtype Celsius_Temperature is Mks_Type
     with
      Dimension => (Symbol => "°C",
        Kelvin => 1,
        others => 0);

   subtype Electric_Capacitance is Mks_Type
     with
      Dimension => (Symbol => 'F',
        Meter    => -2,
        Kilogram => -1,
        Second   =>  4,
        Ampere   =>  2,
        others   =>  0);

   subtype Electric_Charge is Mks_Type
     with
      Dimension => (Symbol => 'C',
        Second => 1,
        Ampere => 1,
        others => 0);

   subtype Electric_Conductance is Mks_Type
     with
      Dimension => (Symbol => 'S',
        Meter    => -2,
        Kilogram => -1,
        Second   =>  3,
        Ampere   =>  2,
        others   =>  0);

   subtype Electric_Potential_Difference is Mks_Type
     with
      Dimension => (Symbol => 'V',
        Meter    =>  2,
        Kilogram =>  1,
        Second   => -3,
        Ampere   => -1,
        others   =>  0);

   --  Note the type punning below. The Symbol is a single "ohm" character
   --  encoded in UTF-8 (ce a9 in hexadecimal), but this file is not compiled
   --  with -gnatW8, so we're treating the string literal as a two-character
   --  String.

   subtype Electric_Resistance is Mks_Type
     with
      Dimension => (Symbol => "Ω",
        Meter    =>  2,
        Kilogram =>  1,
        Second   => -3,
        Ampere   => -2,
        others   =>  0);

   subtype Energy is Mks_Type
     with
      Dimension => (Symbol => 'J',
        Meter    =>  2,
        Kilogram =>  1,
        Second   => -2,
        others   =>  0);

   subtype Equivalent_Dose is Mks_Type
     with
      Dimension => (Symbol => "Sv",
        Meter  =>  2,
        Second => -2,
        others =>  0);

   subtype Force is Mks_Type
     with
      Dimension => (Symbol => 'N',
        Meter    => 1,
        Kilogram => 1,
        Second   => -2,
        others   => 0);

   subtype Frequency is Mks_Type
     with
      Dimension => (Symbol => "Hz",
        Second => -1,
        others =>  0);

   subtype Illuminance is Mks_Type
     with
      Dimension => (Symbol => "lx",
        Meter   => -2,
        Candela =>  1,
        others  =>  0);

   subtype Inductance is Mks_Type
     with
      Dimension => (Symbol => 'H',
        Meter    =>  2,
        Kilogram =>  1,
        Second   => -2,
        Ampere   => -2,
        others   =>  0);

   subtype Luminous_Flux is Mks_Type
     with
      Dimension => (Symbol => "lm",
        Candela => 1,
        others  => 0);

   subtype Magnetic_Flux is Mks_Type
     with
      Dimension => (Symbol => "Wb",
        Meter    =>  2,
        Kilogram =>  1,
        Second   => -2,
        Ampere   => -1,
        others   =>  0);

   subtype Magnetic_Flux_Density is Mks_Type
     with
      Dimension => (Symbol => 'T',
        Kilogram =>  1,
        Second   => -2,
        Ampere   => -1,
        others   =>  0);

   subtype Power is Mks_Type
     with
      Dimension => (Symbol => 'W',
        Meter    =>  2,
        Kilogram =>  1,
        Second   => -3,
        others   =>  0);

   subtype Pressure is Mks_Type
     with
      Dimension => (Symbol => "Pa",
        Meter    => -1,
        Kilogram =>  1,
        Second   => -2,
        others   =>  0);

   subtype Radioactivity is Mks_Type
     with
      Dimension => (Symbol => "Bq",
        Second => -1,
        others =>  0);

   subtype Solid_Angle is Mks_Type
     with
      Dimension => (Symbol => "sr",
        others => 0);

   subtype Unconstrained_Speed is Mks_Type
     with
      Dimension => (
        Meter  =>  1,
        Second => -1,
        others =>  0);

   subtype Volume is Mks_Type
     with
      Dimension => (
        Meter  => 3,
        others => 0);

   subtype Constant_Type is Dimensions.Mks_Type with Dimension => (Symbol => 'K', others => 0);

   subtype Unconstrained_Acceleration is Dimensions.Mks_Type
     with
       Dimension => (Meter  =>  1,
                     Second => -2,
                     others =>  0);

   subtype Acceleration_Meter is Dimensions.Mks_Type
     with
       Dimension => (Meter  =>  2,
                     Second => -2,
                     others =>  0);

   subtype Inverse_Length is Dimensions.Mks_Type
     with
       Dimension => (Meter  => -1,
                     others =>  0);

   subtype InvAcc is Dimensions.Mks_Type
     with
       Dimension => (Meter  => -1,
                     Second =>  2,
                     others =>  0);

   subtype TimeSQ is Dimensions.Mks_Type
     with
       Dimension => (Meter  =>  0,
                     Second =>  2,
                     others =>  0);

   --  Dimensions, types and numeric operations

   --  Angular velocity in radians per second.
   subtype Unconstrained_Angular_Velocity is Dimensions.Mks_Type
     with
       Dimension => (Symbol => "radps",
                     Second => -1,
                     others =>  0);
   Max_Angular_Velocity : constant Unconstrained_Angular_Velocity := 1_000_000.0 / s;
   subtype Angular_Velocity is Unconstrained_Angular_Velocity range -Max_Angular_Velocity .. Max_Angular_Velocity;

   subtype Normalized_Angle is Angle range -Pi .. Pi;
   Max_Acceleration : constant Unconstrained_Acceleration := 1000.0 * m / s / s;
   subtype Acceleration is Unconstrained_Acceleration range -Max_Acceleration .. Max_Acceleration;
   subtype Positive_Acceleration is Acceleration range 0.1 * m / s / s .. Max_Acceleration;
   subtype Non_Zero_Acceleration is Acceleration range -Max_Acceleration .. Max_Acceleration
     with Predicate => abs (Non_Zero_Acceleration) >= 0.1 * m / s / s;

   Map_Size : constant Unconstrained_Length := 1_000_000.0 * m;
   subtype Length is Unconstrained_Length range -Map_Size * m .. Map_Size * m;
   subtype Non_Negative_Length is Unconstrained_Length range 0.0 * m .. Map_Size * m;
   subtype Short_Length is Unconstrained_Length range -50.0 * m .. 50.0 * m;
   subtype Non_Negative_Short_Length is Unconstrained_Length range 0.0 * m .. 50.0 * m;
   subtype Area is Unconstrained_Area range -Map_Size**2 * m * m .. Map_Size**2 * m * m;

   Max_Speed : constant Unconstrained_Speed := 1_000_000.0 * m / s;
   subtype Speed is Unconstrained_Speed range -Max_Speed .. Max_Speed;
   subtype Slow_Speed_Type is Speed range 0.0 * m / s .. 100.0 * m / s;

   Max_Time : constant Unconstrained_Time := 86000000.0 * s;
   subtype Time is Unconstrained_Time range -Max_Time .. Max_Time;

   Max_Float    : constant Float         := 1_000_000_000.0;
   Max_Constant : constant Constant_Type := 1_000_000_000.0;
   subtype Saturated_Constant is Constant_Type range -Max_Constant .. Max_Constant;
   subtype Positive_Constant is Constant_Type range 0.0 .. Max_Constant;

   subtype Normal_Value is Constant_Type range -1.0 .. 1.0;

   type Position_Type is record
      X       : Length;
      Y       : Length;
   end record;

   --  Pose is a combination of position and orientation. 2D.
   type Pose_Type is record
      Pos     : Position_Type;
      Heading : Normalized_Angle;
   end record;

   type Vector_Type is record
      dx : Length;
      dy : Length;
   end record;

   --  Used for Bezier curves to hold pose setpoint and current speed factor.
   type Pose_Speed is record
      Pose          : Pose_Type;
      Vector_Length : Non_Negative_Length;
   end record;

   --  Defines movement relative to current position and orientation
   --  Vector is movement of center, Rotation is rotation relative to current direction
   type Movement_Type is record
      Vector   : Vector_Type;
      Rotation : Normalized_Angle;
   end record;

   --  parameters for a line ax + by + c = 0
   type Line_Parameter_Type is record
      a : Normal_Value;
      b : Normal_Value;
      c : Length;
   end record
     with Dynamic_Predicate =>
       (a /= 0.0 or b /= 0.0) and
     a**2 + b**2 in 0.9 .. 1.1;

   package Angle_Numerics is new Ada.Numerics.Generic_Elementary_Functions (Angle);
   package Mks_Numerics is new Ada.Numerics.Generic_Elementary_Functions (Mks_Type);

   --  Degrees, integer positive numbers in valid range
   --  Should be used to program missions, not in other code.
   --  Use with care.
   type Degrees is new Natural range 0 .. 359;

   --  Initialize derived dimension values

   --  Turn off the all the dimension warnings for these basic assignments
   --  since otherwise we would get complaints about assigning dimensionless
   --  values to dimensioned subtypes.

   pragma Warnings (Off, "*assumed to be*");

   rad : constant Angle                         := 1.0;
   sr  : constant Solid_Angle                   := 1.0;
   Hz  : constant Frequency                     := 1.0;
   N   : constant Force                         := 1.0;
   Pa  : constant Pressure                      := 1.0;
   J   : constant Energy                        := 1.0;
   W   : constant Power                         := 1.0;
   C   : constant Electric_Charge               := 1.0;
   V   : constant Electric_Potential_Difference := 1.0;
   F   : constant Electric_Capacitance          := 1.0;
   Ohm : constant Electric_Resistance           := 1.0;
   Si  : constant Electric_Conductance          := 1.0;
   Wb  : constant Magnetic_Flux                 := 1.0;
   T   : constant Magnetic_Flux_Density         := 1.0;
   H   : constant Inductance                    := 1.0;
   dC  : constant Celsius_Temperature           := 273.15;
   lm  : constant Luminous_Flux                 := 1.0;
   lx  : constant Illuminance                   := 1.0;
   Bq  : constant Radioactivity                 := 1.0;
   Gy  : constant Absorbed_Dose                 := 1.0;
   Sv  : constant Equivalent_Dose               := 1.0;
   kat : constant Catalytic_Activity            := 1.0;

   --  SI prefixes for Meter

   um  : constant Unconstrained_Length := 1.0E-06;  -- micro (u)
   mm  : constant Unconstrained_Length := 1.0E-03;  -- milli
   cm  : constant Unconstrained_Length := 1.0E-02;  -- centi
   dm  : constant Unconstrained_Length := 1.0E-01;  -- deci
   dam : constant Unconstrained_Length := 1.0E+01;  -- deka
   hm  : constant Unconstrained_Length := 1.0E+02;  -- hecto
   km  : constant Unconstrained_Length := 1.0E+03;  -- kilo
   Mem : constant Unconstrained_Length := 1.0E+06;  -- mega

   --  SI prefixes for Kilogram

   ug  : constant Mass := 1.0E-09;  -- micro (u)
   mg  : constant Mass := 1.0E-06;  -- milli
   cg  : constant Mass := 1.0E-05;  -- centi
   dg  : constant Mass := 1.0E-04;  -- deci
   g   : constant Mass := 1.0E-03;  -- gram
   dag : constant Mass := 1.0E-02;  -- deka
   hg  : constant Mass := 1.0E-01;  -- hecto
   Meg : constant Mass := 1.0E+03;  -- mega

   --  SI prefixes for Second

   us  : constant Time := 1.0E-06;  -- micro (u)
   ms  : constant Time := 1.0E-03;  -- milli
   cs  : constant Time := 1.0E-02;  -- centi
   ds  : constant Time := 1.0E-01;  -- deci
   das : constant Time := 1.0E+01;  -- deka
   hs  : constant Time := 1.0E+02;  -- hecto
   ks  : constant Time := 1.0E+03;  -- kilo
   Mes : constant Unconstrained_Time := 1.0E+06;  -- mega

   --  Other constants for Second

   min  : constant Time := 60.0 * s;
   hour : constant Time := 60.0 * min;
   day  : constant Unconstrained_Time := 24.0 * hour;
   year : constant Unconstrained_Time := 365.25 * day;

   --  SI prefixes for Ampere

   mA  : constant Electric_Current := 1.0E-03;  -- milli
   cA  : constant Electric_Current := 1.0E-02;  -- centi
   dA  : constant Electric_Current := 1.0E-01;  -- deci
   daA : constant Electric_Current := 1.0E+01;  -- deka
   hA  : constant Electric_Current := 1.0E+02;  -- hecto
   kA  : constant Electric_Current := 1.0E+03;  -- kilo
   MeA : constant Electric_Current := 1.0E+06;  -- mega

   pragma Warnings (On, "*assumed to be*");

end Dimensions;
