procedure Test with SPARK_Mode is

   type My_Rec (Is_Int : Boolean := False) is record
      case Is_Int is
         when True =>
            F_Int : Integer;
         when False =>
            F_Float : Float;
      end case;
   end record;

   type My_Rec_2 is new My_Rec with
     Unchecked_Union;

   procedure Callee (X : in out My_Rec) is
   begin
      null;
   end Callee;

   procedure P (X : in out My_Rec_2) is
   begin
     Callee (My_Rec (X)); -- @UU_RESTRICTION:FAIL
   end P;

   X : My_Rec_2 := (True, 13);
begin
   P (X);
end;
