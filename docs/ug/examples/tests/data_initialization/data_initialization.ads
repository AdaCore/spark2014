package Data_Initialization with
  SPARK_Mode
is
   type Data is record
      Val : Float;
      Num : Natural;
   end record;

   G1, G2, G3 : Data;

   procedure Proc
     (P1 : in     Data;
      P2 :    out Data;
      P3 : in out Data)
   with
     Global => (Input  => G1,
                Output => G2,
                In_Out => G3);

   procedure Call_Proc with
     Global => (Output => (G1, G2, G3));

end Data_Initialization;
