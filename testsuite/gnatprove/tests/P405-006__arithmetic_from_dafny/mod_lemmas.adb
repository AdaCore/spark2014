with SPARK.Lemmas.Integer_Arithmetic; use SPARK.Lemmas.Integer_Arithmetic;

procedure Mod_Lemmas with
  SPARK_Mode
is
   pragma Warnings (Off, "postcondition does not check the outcome of calling");

   subtype Small_Integer is Integer range -1_000 .. 1_000;
   subtype Small_Natural is Integer range 0 .. 1_000;
   subtype Small_Positive is Integer range 1 .. 1_000;

   type Sign_T is (Neg, Zero, Pos);
   function Sign (X : Integer) return Sign_T is
      (if X < 0 then Neg elsif X = 0 then Zero else Pos);

   procedure Mod_Of_Zero_Is_Zero (M : Positive; Res : out Integer) with
     Post => Res = 0
   is
   begin
      Res := 0 mod M;
   end Mod_Of_Zero_Is_Zero;

   procedure Fundamental_Div_Mod (X : Integer; D : Integer; Res : out Integer) with
     Pre  => D /= 0 and then
             (if D = -1 then X /= Integer'First),
     Post => X = Res  --  @POSTCONDITION:FAIL
   is
   begin
      Res := D * (X / D) + (X mod D);
   end Fundamental_Div_Mod;

   procedure Mod_Yourself (M : Positive; Res1, Res2 : out Integer) with
     Post => Res1 = 0 and then Res2 = 0
   is
   begin
      Res1 := M mod M;
      Res2 := (-M) mod M;
   end Mod_Yourself;

   procedure Mod_Small (X : Natural; M : Positive; Res : out Integer) with
     Pre  => X < M,
     Post => Res = X
   is
   begin
      Res := X mod M;
   end Mod_Small;

   procedure Mod_Range (X : Integer; M : Positive; Res : out Integer) with
     Post => Res in 0 .. M-1
   is
   begin
      Res := X mod M;
   end Mod_Range;

   procedure Mod_Twice (X : Integer; M : Positive; Res1, Res2 : out Integer) with
     Post => Res1 = Res2
   is
   begin
      Res1 := X mod M;
      Res2 := Res1 mod M;
   end Mod_Twice;

   procedure Mod_Add (X, Y : Small_Integer; M : Small_Positive; Res1, Res2 : out Integer) with
     Post => (if Res1 < M then Res2 = Res1 else Res2 = Res1 - M)
   is
   begin
      Res1 := (X mod M) + (Y mod M);
      Res2 := (X + Y) mod M;
   end Mod_Add;

   procedure Mod_Sub (X, Y : Small_Integer; M : Positive; Res1, Res2 : out Integer) with
     Post => (if Res1 >= 0 then Res2 = Res1 else Res2 = Res1 + M)
   is
   begin
      Res1 := (X mod M) - (Y mod M);
      Res2 := (X - Y) mod M;
   end Mod_Sub;

   X, Y, Z, R, S : Integer;

begin
   X := 4;
   Mod_Of_Zero_Is_Zero (X, R);

   X := 2356;
   Mod_Of_Zero_Is_Zero (X, R);

   X := 4;
   Mod_Yourself (X, R, S);

   X := 4;
   Y := 2356;
   Mod_Small (X, Y, R);

   X := 2356;
   Y := 4;
   Mod_Range (X, Y, R);

   X := 2356;
   Y := 4;
   Mod_Twice (X, Y, R, S);

   X := 356;
   Y := 43;
   Z := 4;
   Mod_Add (X, Y, Z, R, S);

   X := 356;
   Y := 43;
   Z := 4;
   Mod_Sub (X, Y, Z, R, S);

end Mod_Lemmas;
