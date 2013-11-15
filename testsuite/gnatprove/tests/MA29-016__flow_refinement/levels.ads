package Levels
  with Abstract_State => Abs_0
is

   function Read_Partial_0 return Integer
     with Global => Abs_0;

   function Read_Partial_Combined return Integer
     with Global => Abs_0;

   function Wibble_0 return Integer is (Read_Partial_0 + 1)
     with Global => Abs_0;

   procedure Post_Test_01
     with Global => (Proof_In => Abs_0),
          Post   => Wibble_0 > Read_Partial_0;

   procedure Post_Test_02
     with Global => Abs_0,
          Post   => Read_Partial_0 + 1 > Read_Partial_0;

   procedure Test_03 (A : out Integer)
   with Global => Abs_0;

   procedure D_Test_01 (X : out Integer;
                        Y : in out Integer)
     with Global  => Abs_0,
          Depends => (X => Abs_0,
                      Y =>+ Abs_0);

end Levels;
