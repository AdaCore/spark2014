with Types; use Types;

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

   --  from N920-003 (teaching example)
   procedure Fibonacci (N : Positive; X, Y : Float_32; Res : out Float_32);

   --  from NC01-041 (industrial user)
   procedure Int_To_Float_Complex (X : Unsigned_16; Y : Float_32; Res : out Float_32);

   --  from NC03-013 (industrial user)
   procedure Int_To_Float_Simple (X : Unsigned_16; Res : out Float_32);

   --  from NC04-023 (industrial user)
   function Float_to_Long_Float (X : Float) return Long_Float
   is (Long_Float (X))
      with Pre  => (X >= Float'First and
                    X <= Float'Last),
           Post => (Float_to_Long_Float'Result >= Long_Float (Float'First) and
                    Float_to_Long_Float'Result <= Long_Float (Float'Last));

end Floating_Point;
