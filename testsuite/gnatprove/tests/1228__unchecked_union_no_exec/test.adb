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

   procedure P (B : Boolean) with Ghost => Static;

   procedure P (B : Boolean) is
      X : My_Rec := (True, 13);
      Y : My_Rec := (True, 13);
      C : Boolean := X = Y;  --  OK, P is ghost static
   begin
      null;
   end P;

   procedure P_2 (B : Boolean) with Ghost => Static, Post => True;

   procedure P_2 (B : Boolean) is
      X : My_Rec := (True, 13);
      Y : My_Rec := (True, 13);
      C : Boolean := X = Y;  --  OK, P_2 is ghost static
   begin
      null;
   end P_2;

   X : My_Rec := (True, 13);
   Y : My_Rec := (True, 13);
   C : Boolean := X = Y with Ghost => Static;  --  Ok, C is ghost static
begin
   C := X = Y;  --  Ok, C is ghost static
   P (X = Y);  --  OK, P is ghost static
   P_2 (X = Y);  --  OK, P_2 is ghost static
end;
