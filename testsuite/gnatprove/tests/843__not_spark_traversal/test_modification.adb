procedure Test_Modification with SPARK_Mode is

   --  Check that IN OUT parameters of traversal functions cannot be modified

   type Holder is record
      C : aliased Integer;
   end record;

   function F_1 (X : aliased in out Holder) return not null access Integer;

   function F_1 (X : aliased in out Holder) return not null access Integer is
      B : not null access Integer := X.C'Access;
   begin
      B.all := 15; --  Error, B is constant
      return B;
   end F_1;

   function F_2 (X : aliased in out Holder) return not null access Integer;

   function F_2 (X : aliased in out Holder) return not null access Integer is

      procedure Update (X : access Integer) with
        Always_Terminates,
        Global => null,
        Import;

      B : not null access Integer := X.C'Access;
   begin
      Update (B); --  Error, B is constant
      return B;
   end F_2;

   function F_3 (X : aliased in out Holder) return not null access Integer;

   function F_3 (X : aliased in out Holder) return not null access Integer is
      B : not null access Integer := X.C'Access;
   begin
      declare
         B2 : not null access Integer := B;
      begin
         B2.all := 15; --  Error, B is constant
      end;
      return B;
   end F_3;

   --  Check that traversal functions with IN parameters cannot be called on
   --  constant objects.

   type Int_Acc is access Integer;

   type Holder_2 is record
      A : Integer;
      C : not null Int_Acc;
   end record;

   function G (X : Holder_2) return not null access Integer;

   function G (X : Holder_2) return not null access Integer is
   begin
      return X.C;
   end G;

   W : constant Holder_2 := (1, new Integer'(2));
begin
   declare
      B : access Integer := G (W); --  Error, W is constant
   begin
      B.all := 4;
   end;
end;
