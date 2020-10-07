package body Refined_Global_Examples
  with SPARK_Mode,
       Refined_State => (State => (A, B))
is
   A : Integer;  --  The constituents of State
   B : Integer;

   procedure P1_1 (I : in Integer)
     with Refined_Global => (In_Out => A,  --  Refined onto constituents of State
                             Output => B)  --  B is Output but A is In_Out and
                                           --  so Global State is also In_Out
   is
   begin
      B := A;
      A := I;
   end P1_1;

   procedure P1_2 (I : in Integer)
     with Refined_Global => (Output => A)  --  Not all of the constituents of
                                           --  State are updated and so the Global
                                           --  State must In_Out
   is
   begin
      A := I;
   end P1_2;

   procedure P1_3 (Result : out Integer)
     with Refined_Global => (Input => B)  --  Not all of the constituents of State
                                          --  are read but none of them are
                                          --  updated so the Global State is Input
   is
   begin
      Result := B;
   end P1_3;

   procedure P1_4 (I : in Integer)
     with Refined_Global => (Output => (A, B))  --  The constituents of State are
                                                --  not read but they are all
                                                --  updated and so the mode
                                                --  selector of State is Output
   is
   begin
      A := I;
      B := A;
   end P1_4;

end Refined_Global_Examples;
