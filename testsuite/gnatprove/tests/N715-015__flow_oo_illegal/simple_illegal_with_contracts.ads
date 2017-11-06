package Simple_Illegal_With_Contracts is pragma Elaborate_Body;
   type Level_0_T (D : Integer) is tagged record
      A : Integer;
      case D is
         when 0 =>
            Extra : Integer;

         when others =>
            null;
      end case;
   end record;

   PI, I , IO, O : Integer := 0;

   procedure P (Par : in out Level_0_T)
     with Global => (Proof_In => PI,
                     Input    => I,
                     In_Out   => IO,
                     Output   => O);

   type Level_1_1_T is new Level_0_T with record
      B1 : Integer;
   end record;

   procedure P (Par : in out Level_1_1_T)
     with Global => (Input  => (PI, I),  --  PROBLEM: PI cannot be an Input
                     In_Out => IO,
                     Output => O);

   type Level_1_2_T is new Level_0_T with record
      B2 : Integer;
   end record;

   procedure P (Par : in out Level_1_2_T)
     with Global => (Proof_In => PI,
                     In_Out   => (I, IO),  --  PROBLEM: I cannot be an In_Out
                     Output   => O);

   type Level_1_3_T is new Level_0_T with record
      B3 : Integer;
   end record;

   procedure P (Par : in out Level_1_3_T)
     with Global => (Proof_In => PI,
                     Output   => (I, IO, O));  --  PROBLEM: I cannot be an                                                     --           output

   type Level_1_T is new Level_0_T with record
      B : Integer;
   end record;

   procedure P (Par : in out Level_1_T)  --  ALL OK
     with Global => (Proof_In => PI,
                     Input    => I,
                     Output   => (IO, O));

   type Level_2_1_T is new Level_1_T with record
      C1 : Integer;
   end record;

   procedure P (Par : in out Level_2_1_T)
     with Global => (Proof_In => (PI, I),
                     Output   => O);  --  PROBLEM: IO has to be an output
end Simple_Illegal_With_Contracts;
