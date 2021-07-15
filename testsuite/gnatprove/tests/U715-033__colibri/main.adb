with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main with SPARK_Mode is

   package Float_Convs is new Float_Conversions (Num => Long_Float);
   use Float_Convs;

   package Int_Convs is new Signed_Conversions (Int => Long_Integer);
   use Int_Convs;

   function BR (LF : Long_Float) return Big_Real
                renames Float_Convs.To_Big_Real;

   type Unit_Type is (Unit);

   subtype Exact is Long_Integer range - 2 ** 53 .. 2 ** 54;
   function Prove_Exact (X : Exact) return Unit_Type with
     Ghost,
     Post => To_Big_Real (To_Big_Integer (X)) = BR (Long_Float (X)); --@POSTCONDITION:FAIL
   function Prove_Exact (X : Exact) return Unit_Type is
   begin
      return Unit;
   end Prove_Exact;
   function Prove_Constr_Exact (X : Exact) return Unit_Type with
     Ghost
   is
      Y : constant Long_Float := Long_Float(X);
      F : constant Long_Float := Y * 2.0**(-17);
   begin
      pragma Assert (BR (Y) >= BR(- 2.0 ** 53));
      pragma Assert (BR (F) = BR (Y) * BR (2.0 **(-17))); --@ASSERT:FAIL
      return Unit;
   end Prove_Constr_Exact;
begin
   null;
end;
