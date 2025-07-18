package body P is

   type My_Base_Rec
     (D1 : Boolean;
      D2 : Boolean)
   is record
      F : Integer := 12345;
   end record;

   type My_Rec is new My_Base_Rec;

   subtype T0 is My_Rec;

   subtype T1 is T0;

   subtype T2 is T1 (True, False);

   type R is record
      F_T : T2;
      F_I : Small_Int;
   end record;

   procedure Proc (J : Choice; K : Small_Int := 0)
   is
      V1_T1 : T1 := (True, False, 1111);
      V2_T1 : T1 := (True, True, 2222);
      V1_Int : Integer := 5;
      V2_Int : Integer := K + 15;
      V_R : R;
   begin
      case J is
      when 1 =>
         V_R := (F_T => V1_T1, F_I => V1_Int);
      when 2 =>
         V_R := (F_T => V2_T1, F_I => V1_Int); -- @DISCRIMINANT_CHECK:FAIL
      when 3 =>
         V_R := (F_T => V1_T1, F_I => V2_Int); -- @RANGE_CHECK:FAIL
      when others =>
         null;
      end case;
   end Proc;

end P;
