package body P is
   pragma SPARK_Mode (Off);  --  concatenation

   X : String := "some";
   B : Boolean := False;

   Y : String :=
     "yes" & (if B then X else X);

   function F (X : String; B : Boolean) return String is
      Y : String :=
        "yes" & (if B then X else X);
   begin
      return Y;
   end;

   subtype S is Integer range 1 .. 10;
   type D is new Integer range 1 .. 10;
   type T is range 1 .. 10;

   procedure Proc (X, Y : Integer) is
      Tmp_S : S := X;
      Tmp_D : D := D(X);
      Tmp_T : T := T(X);
   begin
      Tmp_S := Y;
      Tmp_D := D(Y);
      Tmp_T := T(Y);

      Tmp_S := X + Y;
      Tmp_D := D(X + Y);
      Tmp_T := T(X + Y);

      Tmp_S := X / Y;
      Tmp_D := D(X / Y);
      Tmp_T := T(X / Y);
   end;

end;
