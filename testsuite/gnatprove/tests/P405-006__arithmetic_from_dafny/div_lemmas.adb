with SPARK.Lemmas.Integer_Arithmetic; use SPARK.Lemmas.Integer_Arithmetic;

procedure Div_Lemmas with
  SPARK_Mode
is
   pragma Warnings (Off, "postcondition does not check the outcome of calling");

   subtype Small_Integer is Integer range -1_000 .. 1_000;
   subtype Small_Natural is Integer range 0 .. 1_000;
   subtype Small_Positive is Integer range 1 .. 1_000;

   type Sign_T is (Neg, Zero, Pos);
   function Sign (X : Integer) return Sign_T is
      (if X < 0 then Neg elsif X = 0 then Zero else Pos);

   procedure Div_Of_0 (D : Integer; Res : out Integer) with
     Pre  => D /= 0,
     Post => Res = 0
   is
   begin
      Res := 0 / D;
   end Div_Of_0;

   procedure Div_By_Self (D : Integer; Res : out Integer) with
     Pre  => D /= 0,
     Post => Res = 1
   is
   begin
      Res := D / D;
   end Div_By_Self;

   procedure Div_Small (X : Natural; D : Positive; Res : out Integer) with
     Pre  => X < D,
     Post => Res = 0
   is
   begin
      Res := X / D;
   end Div_Small;

   procedure Div_Float_Ge (X, Y : Float; Res : out Float) with
     Pre  => X > Y and then X >= 0.0 and then Y > 0.0,
     Post => Res >= 1.0
   is
   begin
      Res := X / Y;
   end Div_Float_Ge;

   X, Y, R : Integer;
   S : Float;

begin
   X := 4;
   Div_Of_0 (X, R);

   X := 4;
   Div_By_Self (X, R);

   X := 4;
   Y := 345;
   Div_Small (X, Y, R);

   Div_Float_Ge (123.09, 21.0334, S);

end Div_Lemmas;
