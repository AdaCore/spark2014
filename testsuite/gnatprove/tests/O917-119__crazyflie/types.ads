with Interfaces;

package Types is

   --  General types used for C Interfacing.

   type T_Int8   is new Interfaces.Integer_8;
   type T_Int16  is new Interfaces.Integer_16;
   type T_Int32  is new Interfaces.Integer_32;
   type T_Int64  is new Interfaces.Integer_64;

   type T_Uint6 is mod 2 ** 6;
   for T_Uint6'Size use 6;

   type T_Uint8  is new Interfaces.Unsigned_8;
   type T_Uint16 is new Interfaces.Unsigned_16;
   type T_Uint32 is new Interfaces.Unsigned_32;

   subtype T_Bit_Pos_8 is Natural  range 0 .. 7;
   subtype T_Bit_Pos_16 is Natural range 0 .. 15;

   type T_Uint8_Array  is array (Integer range <>) of T_Uint8;
   type T_Uint16_Array is array (Integer range <>) of T_Uint16;

   type T_Int32_Array  is array (Integer range <>) of T_Int32;
   type T_Int64_Array  is array (Integer range <>) of T_Int64;

   type Float_Array is array (Integer range <>) of Float;

   subtype Natural_Float is Float range 0.0 .. Float'Last;

   --  Types used by the stabilization system.

   --  Allowed delta time range.
   subtype T_Delta_Time   is Float range 0.001 .. 1.0;

   --  Smoothing terms. Used for barycentric expressions.
   subtype T_Alpha        is Float range 0.0 .. 1.0;

   --  Angle range type, in degrees.
   --  This range is deduced from the MPU9150 Datasheet.
   subtype T_Degrees        is Float range -360.0 .. 360.0;

   --  Allowed speed range, in m/s.
   --  This range is deduced from the MPU9150 Datasheet.
   subtype T_Speed        is Float range -2000.0 .. 2000.0;

   --  Allowed sensitivity for target altitude change in Alt Hold mode.
   subtype T_Sensitivity  is Float range 100.0 .. 300.0;

   --  Allowed factor to relate Altitude with Thrust command for motors.
   subtype T_Motor_Fac    is Float range 10_000.0 .. 15_000.0;

   --  Types used for the implementation of Mahony and Madgwick algorithms

   subtype T_Quaternion is Float range -1.0 .. 1.0;

end Types;
