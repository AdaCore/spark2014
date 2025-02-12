procedure Test_Legal with SPARK_Mode is

   --  Make sure that it is possible to use in out parameters in traversal functions

   type Holder is record
      C : aliased Integer;
   end record;

   function F (X : aliased in out Holder) return not null access Integer;

   function F (X : aliased in out Holder) return not null access Integer is
   begin
      return X.C'Access;
   end F;

   function F_2 (X : in out Holder) return not null access Integer;

   function F_2 (X : in out Holder) return not null access Integer is
      B : constant not null access Integer := X.C'Access;
   begin
      return B;  --@ACCESSIBILITY_CHECK:FAIL
   end F_2;

   H : aliased Holder := (C => 1);

   procedure Test is
      X_1 : not null access Integer := F (H);
   begin
      X_1.all := 12;
   end Test;

   procedure Test_2 is
      X_2 : not null access Integer := F_2 (H);
   begin
      X_2.all := 14;
   end Test_2;

   type Int_Acc is access Integer;

   type Holder_2 is record
      C : not null Int_Acc;
   end record;

   function F_3 (X : in out Holder_2) return not null access Integer;

   function F_3 (X : in out Holder_2) return not null access Integer is
   begin
      return X.C;
   end F_3;

   function F_4 (X : in out Holder_2) return not null access Integer;

   function F_4 (X : in out Holder_2) return not null access Integer is
      B : constant not null access Integer := X.C;
   begin
      return B;
   end F_4;

   G : aliased Holder_2 := (C => new Integer'(1));

   procedure Test_3 is
      X_1 : not null access Integer := F_3 (G);
   begin
      X_1.all := 12;
   end Test_3;

begin
   Test;
   pragma Assert (H.C = 12);
   Test_2;
   pragma Assert (H.C = 14); --  Fails at runtime because of the missing aliased
end;
