procedure Ex with SPARK_Mode is

   type My_Rec (Is_Int : Boolean := False) is record
      case Is_Int is
         when True =>
            F_Int : Integer;
         when False =>
            F_Float : Float;
      end case;
   end record with
     Unchecked_Union;

   subtype My_Rec_Int is My_Rec (True);

   function Read_F_Int (X : My_Rec) return Integer with
     Pre => (Static => X in My_Rec_Int);

   function Read_F_Int (X : My_Rec) return Integer is (X.F_Int);

   procedure Write_F_Int_If_B (X : in out My_Rec; B : Boolean) with
     Post => (Static => (if B then X = (True, 12) else X = X'Old));

   procedure Write_F_Int_If_B (X : in out My_Rec; B : Boolean) is
   begin
      if B then
         X := (True, 12);
      end if;
   end Write_F_Int_If_B;

begin
   null;
end;
