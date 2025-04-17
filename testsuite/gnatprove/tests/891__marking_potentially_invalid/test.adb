with Ada.Unchecked_Conversion;

procedure Test with spark_mode is

   type R is record
      I : Positive;
   end record;

   function Conv is new Ada.Unchecked_Conversion (Integer, R) with Potentially_Invalid;

   --  On procedures that have a body in SPARK, we do not expect a warning,
   --  unless proof is disabled.

   procedure P_Body_SPARK (X : Integer; Res : out R) with
     Potentially_Invalid => Res,
     Post => Res.I = X;

   procedure P_Body_SPARK (X : Integer; Res : out R) is
   begin
      Res := Conv (X);
   end P_Body_SPARK;

   function F_Body_SPARK (X : Integer) return R is (Conv (X)) with
     Potentially_Invalid => F_Body_SPARK'Result,
     Post => F_Body_SPARK'Result.I = X;

   procedure P_Body_Off (X : Integer; Res : out R) with
     Potentially_Invalid => Res,
     Post => Res.I = X;

   procedure P_Body_Off (X : Integer; Res : out R) with SPARK_Mode => Off is
   begin
      Res := Conv (X);
   end P_Body_Off;

   function F_Body_Off (X : Integer) return R with
     Potentially_Invalid => F_Body_Off'Result,
     Post => F_Body_Off'Result.I = X;

   function F_Body_Off (X : Integer) return R is (Conv (X)) with SPARK_Mode => Off;


begin
   null;
end;
