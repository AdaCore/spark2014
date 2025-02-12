procedure Test_Flow with SPARK_Mode is

   --  Test that modifications through borrowers are visible by flow analysis

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

   X : aliased Holder := (1, 2);
   procedure Modify_X with Global => X is
      B : access Integer := F (X);  --  Bad global mode for X
   begin
      B.all := 3;
   end;
   procedure Modify_X (I : Integer) with
     Depends => (X => X, null => I)  --  Bad dependency
   is
      B : access Integer := F (X);
   begin
      B.all := I;
   end;

   function G (X : Holder_2) return not null access Integer;

   function G (X : Holder_2) return not null access Integer is
   begin
      return X.C;
   end G;

   Y : Holder_2 := (1, new Integer'(2));
   procedure Modify_Y with Global => Y is
      B : access Integer := G (Y);  --  Bad global mode for Y
   begin
      B.all := 3;
   end;
   procedure Modify_Y (I : Integer) with
     Depends => (Y => Y, null => I)  --  Bad dependency
   is
      B : access Integer := G (Y);
   begin
      B.all := I;
   end;

begin
   null;
end;
