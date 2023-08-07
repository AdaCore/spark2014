procedure Main with SPARK_Mode is

   TT : constant Boolean := True with Warnings => Off;
   FF : constant Boolean := False with Warnings => Off;
   V1 : Boolean := True;
   V2 : Boolean := True;
   V3 : Boolean := True;

   --  Check that warnings are suppressed on short circuits operators

   B1 : Boolean := FF and then V1;
   B2 : Boolean := FF and then (V1 or else V2);
   B3 : Boolean := TT or else V1;
   B4 : Boolean := TT or else (V1 and then V2);

   --  Check that warnings are suppressed on if expressions

   C1 : Boolean := (if FF then V1 else V2);
   C2 : Boolean := (if TT then V1 else V2);
   C3 : Boolean := (if TT then V1 elsif V3 then V2 else V1);
   C4 : Boolean := (if FF then (if V3 then V2 else V1) else V1);

   --  Check that warnings are suppressed on constract cases

   procedure P (Res : out Integer) with
     Contract_Cases =>
       (FF and then not V1 => Res = 4,
        TT or else V1      => Res = 3,
        not TT             => Res = 2,
        others             => Res = 1);

   procedure P (Res : out Integer) is
   begin
      if TT or else V1 then
         Res := 3;
      elsif FF then
         Res := 4;
      elsif not TT then
         Res := 2;
      else
         Res := 1;
      end if;
   end P;

   Res : Integer;
begin
   --  Check that warnings are suppressed on if statements. Add a case for
   --  'Valid which is considered to be 'statically disabled' for proof
   --  warnings.

   if FF then
      Res := 1;

      --  Checks for inconsistent assume are also removed in statically
      --  disabled branches.

      pragma Assume (not V1);
   elsif not V1'Valid then
      Res := 2;
   elsif TT or else V1 then
      Res := 3;
   elsif V2 then
      Res := 4;
   else
      Res := 5;
   end if;
end Main;
