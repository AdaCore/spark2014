with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   subtype Int is Integer range 1 .. 9;

   type Rec_Null is null record;

   type Rec is record
     A, B, C : Int := 5;
   end record;

   type Rec_Discr (D1, D2 : Int) is record
     A, B, C: Int := 5;
   end record;

   type Rec_Tagged is tagged record
      A : Int := 1;
   end record;

   type Rec_Extend is new Rec_Tagged with
      record
         B : Int := 2;
      end record;

   --------------------
   -- Check_Contents --
   --------------------

   function Check_Contents (R : Rec_Null) return Boolean is (R in Rec_Null);

   function Check_Contents (R : Rec; A, B, C : Int) return Boolean is
      (R.A = A and then R.B = B and then R.C = C);

   function Check_Contents (R : Rec_Discr; D1, D2, A, B, C : Int)
      return Boolean
   is         (R.D1 = D1
      and then R.D2 = D2
      and then R.A = A
      and then R.B = B
      and then R.C = C);

   --  Local variables

   RN1 :          Rec_Null;
   RN2 : constant Rec_Null := (null record);
   RN3 : constant Rec_Null := (others => <>);

   R1  :          Rec;                                    --  (5, 5, 5)
   R2  : constant Rec := (1, 2, 3);                       --  (1, 2, 3)
   R3  : constant Rec := (A => 1, B => 2, C => 3);        --  (1, 2, 3)
   R5  : constant Rec := (1, 1, C => 2);                  --  (1, 1, 2)
   R4  : constant Rec := (A | B => 1, C => 2);            --  (1, 1, 2)
   R6  : constant Rec := (1,  B => 1, C => <>);           --  (1, 1, 5)
   R7  : constant Rec := (1, others => 2);                --  (1, 2, 2)
   R8  : constant Rec := (A => 1, others => 2);           --  (1, 2, 2)
   R9  : constant Rec := (R1);                            --  (5, 5, 5)
   R10 : constant Rec := (R1 with delta B => 9);          --  (5, 9, 5)
   R11 : constant Rec := (R1 with delta B => 9, C => 1);  --  (5, 9, 1)

   RD1 : constant Rec_Discr := (1, 2, 3, 4, 5);           --  (1, 2, 3, 4, 5)
   RD2 : constant Rec_Discr := (1, others => 2);          --  (1, 1, 2, 2, 2)
   RD3 : constant Rec_Discr := (D1 | D2 => 1,
                                others  => 2);            --  (1, 1, 2, 2, 2)

   RT1 : constant Rec_Tagged := (A => 7);
   --  Extended aggregate: TO UNCOMMENT WHEN SUPPORTED BY RAC
   --  RT2 : constant Rec_Extend := (A => 8, B => 9);

begin

   Put_Line ("-----------------------");
   Put_Line ("-- Record aggregates --");
   Put_Line ("-----------------------");
   Put_Line ("");

   Put_Line ("RN1: " & Boolean'Image (Check_Contents (RN1)));
   Put_Line ("RN2: " & Boolean'Image (Check_Contents (RN2)));
   Put_Line ("RN3: " & Boolean'Image (Check_Contents (RN3)));
   Put_Line ("");

   Put_Line ("R1 : " & Boolean'Image (Check_Contents (R1,  5, 5, 5)));
   Put_Line ("R2 : " & Boolean'Image (Check_Contents (R2,  1, 2, 3)));
   Put_Line ("R3 : " & Boolean'Image (Check_Contents (R3,  1, 2, 3)));
   Put_Line ("R4 : " & Boolean'Image (Check_Contents (R4,  1, 1, 2)));
   Put_Line ("R5 : " & Boolean'Image (Check_Contents (R5,  1, 1, 2)));
   Put_Line ("R6 : " & Boolean'Image (Check_Contents (R6,  1, 1, 5)));
   Put_Line ("R7 : " & Boolean'Image (Check_Contents (R7,  1, 2, 2)));
   Put_Line ("R8 : " & Boolean'Image (Check_Contents (R8,  1, 2, 2)));
   Put_Line ("R9 : " & Boolean'Image (Check_Contents (R9,  5, 5, 5)));
   Put_Line ("R10: " & Boolean'Image (Check_Contents (R10, 5, 9, 5)));
   Put_Line ("R11: " & Boolean'Image (Check_Contents (R11, 5, 9, 1)));
   Put_Line ("");

   Put_Line ("RD1: " & Boolean'Image (Check_Contents (RD1, 1, 2, 3, 4, 5)));
   Put_Line ("RD2: " & Boolean'Image (Check_Contents (RD2, 1, 2, 2, 2, 2)));
   Put_Line ("RD3: " & Boolean'Image (Check_Contents (RD3, 1, 1, 2, 2, 2)));
   Put_Line ("");

   Put_Line ("RT1: " & Boolean'Image (RT1.A = 7));
   --  Put_Line ("RT2: " & Boolean'Image (RT2.A = 8 and then RT2.B = 9));

end Main;
