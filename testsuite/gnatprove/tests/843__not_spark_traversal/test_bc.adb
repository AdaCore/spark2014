procedure Test_BC with SPARK_Mode is

   type Holder is record
      A : Integer;
      C : aliased Integer;
   end record;

   type Int_Acc is access Integer;

   type Holder_2 is record
      A : Integer;
      C : not null Int_Acc;
   end record;

   function F (X : aliased in out Holder) return not null access Integer;

   function F (X : aliased in out Holder) return not null access Integer is
   begin
      return X.C'Access;
   end F;

   function G (X : Holder_2) return not null access Integer;

   function G (X : Holder_2) return not null access Integer is
   begin
      return X.C;
   end G;

   X : aliased Holder := (1, 2);
   Y : Holder_2 := (1, new Integer'(2));
begin
   declare
      B : access Integer := F (X);
   begin
      pragma Assert (X.A = 1); --  Error, the object is borrowed
      B.all := 3;
   end;
   pragma Assert (X.A = 1); --  OK, ownership returned to X

   declare
      B : access Integer := G (Y);
   begin
      pragma Assert (Y.A = 1); --  Error, the object is borrowed
      B.all := 3;
   end;
   pragma Assert (Y.A = 1); --  OK, ownership returned to Y
end;
