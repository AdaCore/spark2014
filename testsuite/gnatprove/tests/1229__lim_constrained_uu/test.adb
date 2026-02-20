procedure Test with SPARK_Mode is

   type My_Rec (Is_Int : Boolean := False) is record
      case Is_Int is
         when True =>
            F_Int : Integer;
         when False =>
            F_Float : Float;
      end case;
   end record with
     Unchecked_Union;

   procedure Write_F_Int_If_B (X : in out My_Rec; B : Boolean) with
     Pre => not X'Constrained;

   procedure Write_F_Int_If_B (X : in out My_Rec; B : Boolean) is
   begin
      if B then
         X := (True, 12);
      end if;
   end Write_F_Int_If_B;

   type My_Rec_2 is new My_Rec;

   procedure P_Inlined (X : in out My_Rec_2) is
   begin
     pragma Assert (X'Constrained);
   end P_Inlined;

   procedure P (X : in out My_Rec) is
   begin
     P_Inlined (My_Rec_2 (X));
   end P;

   X : My_Rec := (True, 13);
begin
   Write_F_Int_If_B (X, True);
end;
