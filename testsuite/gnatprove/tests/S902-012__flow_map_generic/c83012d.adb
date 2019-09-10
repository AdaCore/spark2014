with Report; use Report;

procedure C83012D is

   type REC is record
      PACK3 : Integer;
      PACK4 : Integer;
   end record;

   R : REC := (PACK3 => 3, PACK4 => 1);

   generic
      I : Integer;
   package GEN2 is
      J : Integer := Ident_Int (I);
   end GEN2;

   package PACK3 is new GEN2 (R.PACK3);

begin
   null;
end C83012D;
