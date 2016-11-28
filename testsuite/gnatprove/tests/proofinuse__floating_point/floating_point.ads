with Types; use Types;
with Ada.Numerics.Elementary_Functions; use Ada.Numerics.Elementary_Functions;

package Floating_Point with
  SPARK_Mode
is
   --  from MA18-004 (internal test)
   procedure Range_Add (X : Float_32; Res : out Float_32);

   --  from M809-005 (internal test)
   procedure Range_Mult (X : Float_32; Res : out Float_32);

   --  from N121-026 (industrial user)
   procedure Range_Add_Mult (X, Y, Z : Float_32; Res : out Float_32);

   --  from MC13-026 (industrial user)
   procedure Guarded_Div (X, Y : Float_32; Res : out Float_32);
   procedure Guarded_Div_Original (X, Y : Float_32; Res : out Float_32);
   procedure Guarded_Div_Original_Fixed (X, Y : Float_32; Res : out Float_32);

   --  from N920-003 (teaching example)
   procedure Fibonacci (N : Positive; X, Y : Float_32; Res : out Float_32);

   --  from NC01-041 (industrial user)
   procedure Int_To_Float_Complex (X : Unsigned_16;
                                   Y : Float_32;
                                   Res : out Float_32);

   --  from NC03-013 (industrial user)
   procedure Int_To_Float_Simple (X : Unsigned_16; Res : out Float_32);

   --  from NC04-023 (industrial user)
   function Float_To_Long_Float (X : Float) return Long_Float;

   C : constant := 10.0;
   type T is range 0 .. 1_000_000;

   --  from O227-007 (industrial user)
   procedure Incr_By_Const (State : in out Float_32;
                            X     : T);

   --  Quake3's method of computing a good approximation of 1/sqrt(x). This
   --  is extremely difficult to verify, I have included it here as
   --  something to aim for.
   --
   --  See http://en.wikipedia.org/wiki/Fast_inverse_square_root for more
   --  information.
   function Approximate_Inverse_Square_Root (X : Float) return Float;

   subtype Coord is Float range -4096.0 .. 4096.0;

   procedure Angle_Between (A_X, A_Y : Coord;
                            B_X, B_Y : Coord;
                            C_X, C_Y : Coord;
                            Res      : out Float);

   --  The following User_Rule_* are user-written axioms from OldSPARK from
   --  a real world project. They are also submitted to SMTCOMP.

   subtype Squarable_Float is Float range -18446742974197923840.0 ..
                                           18446742974197923840.0;

   procedure User_Rule_2 (X, Y, Z : Float;
                          Res     : out Boolean);

   procedure User_Rule_3 (X, Y : Float;
                          Res  : out Boolean);

   procedure User_Rule_4 (X, Y : Float;
                          Res  : out Boolean);

   procedure User_Rule_5 (X   : Float;
                          Res : out Boolean);

   procedure User_Rule_6 (X, Y, Z, A : Float;
                          Res        : out Boolean);

   procedure User_Rule_7 (X, Y, Z, A : Float;
                          Res        : out Boolean);

   procedure User_Rule_8 (A, B, C : Float;
                          Res     : out Boolean);

   procedure User_Rule_9 (A, B : Float;
                          Res  : out Boolean);

   procedure User_Rule_10 (A, B : Float;
                           Res  : out Boolean);

   procedure User_Rule_11 (A, B, C, D : Float;
                           Res        : out Boolean);

   procedure User_Rule_12 (A, B, C, D : Float;
                           Res        : out Boolean);

   procedure User_Rule_13 (D0, D1, R : Float;
                           Res       : out Boolean);

   procedure User_Rule_14 (D0, D1, R, X : Float;
                           Res          : out Boolean);

   procedure User_Rule_15 (X, Y : Float;
                           Res  : out Boolean);

   procedure User_Rule_16 (X, Y : Float;
                           Res  : out Boolean);

   --  from P912-012 (industrial user)
   procedure Float_Different (X, Y : Float_32; Res : out Float_32);
   procedure Float_Greater (X, Y : Float_32; Res : out Float_32);

   --  from P914-008 (industrial user)
   procedure Diffs (X, Y, Z : Float);

   --  from P201-069 (academic user)
   procedure Sub_Then_Add1 (X, Y : Float_32; Res : out Float_32);
   procedure Sub_Then_Add2 (X, Y : Float_32; Res : out Float_32);

   --  from PB25-029 (industrial user)
   procedure Half_Bound (X : Float_32; Res : out Float_64);

end Floating_Point;
