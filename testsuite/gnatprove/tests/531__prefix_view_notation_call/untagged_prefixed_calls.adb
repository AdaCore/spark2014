procedure Untagged_Prefixed_Calls is

   package Pkg is

      type Rec (D : Integer) is record
         Comp : Integer := 0;
         Op_3 : Boolean := True;
      end record;

      procedure Op_1 (Obj : Rec; I : Integer);
      procedure Op_2 (Obj : access Rec; B : Boolean);
      function Op_3 (Obj : Rec) return Boolean;


      type Priv is private;

      procedure Prim_Op_1 (Obj : Priv; I : Integer);


      type Other_Priv is private;

      procedure Prim_Op_1 (Obj : Other_Priv; I : Integer);
      function "=" (L, R : Other_Priv) return Boolean;


      type Int_1 is range 1 .. 1000;

      function "+" (L, R : Int_1) return Int_1;

      procedure Proc_Op (Obj : Int_1; I : Integer);

      type Int_2 is new Int_1;

      procedure Proc_Op (Obj : Int_2; I : Integer);

      type Int_3 is new Int_2 range 1 .. 500;

      procedure Proc_Op (Obj : Int_3; I : Integer);


      type Acc_Rec is access all Rec;

      type Acc_Acc_Rec is access all Acc_Rec;

      procedure Op_1 (Obj : Acc_Rec; I : Integer);
      procedure Op_2 (Obj : access Acc_Rec; B : Boolean);

   private

      type Priv is (A, B, C, D);

      procedure Prim_Op_2 (Obj : Priv; I : Integer);
      procedure Prim_Op_3 (Obj : Priv; I : Integer);


      procedure Prim_Op_2 (Obj : Other_Priv; I : Integer);

      type Other_Priv is tagged record
         Comp : Integer;
      end record;

      procedure Prim_Op_3 (Obj : Other_Priv; I : Integer);

   end Pkg;

   package body Pkg is

      procedure Op_1 (Obj : Rec; I : Integer) is
      begin
         null;
      end Op_1;

      procedure Op_2 (Obj : access Rec; B : Boolean) is
      begin
         null;
      end Op_2;

      function Op_3 (Obj : Rec) return Boolean is
      begin
         return Obj.Op_3;
      end Op_3;

      procedure Prim_Op_1 (Obj : Priv; I : Integer) is
      begin
         null;
      end Prim_Op_1;

      procedure Prim_Op_2 (Obj : Priv; I : Integer) is
      begin
         null;
      end Prim_Op_2;

      procedure Prim_Op_3 (Obj : Priv; I : Integer) is
      begin
         null;
      end Prim_Op_3;

      procedure Proc_Op (Obj : Int_1; I : Integer) is
      begin
         null;
      end Proc_Op;

      function "+" (L, R : Int_1) return Int_1 is
      begin
         return Int_1 (Integer (L) + Integer (R));
      end "+";

      procedure Proc_Op (Obj : Int_2; I : Integer) is
      begin
         null;
      end Proc_Op;

      procedure Proc_Op (Obj : Int_3; I : Integer) is
      begin
         null;
      end Proc_Op;

      procedure Op_1 (Obj : Acc_Rec; I : Integer) is
      begin
         null;
      end Op_1;

      procedure Op_2 (Obj : access Acc_Rec; B : Boolean) is
      begin
         null;
      end Op_2;

      procedure Prim_Op_1 (Obj : Other_Priv; I : Integer) is
      begin
         null;
      end Prim_Op_1;

      procedure Prim_Op_2 (Obj : Other_Priv; I : Integer) is
      begin
         null;
      end Prim_Op_2;

      procedure Prim_Op_3 (Obj : Other_Priv; I : Integer) is
      begin
         null;
      end Prim_Op_3;

      function "=" (L, R : Other_Priv) return Boolean is
      begin
         return False;
      end "=";

      Rec_Object : aliased Pkg.Rec (222);
      Acc_Rec_Object : Pkg.Acc_Rec := new Pkg.Rec (456);

      Full_View_Priv_Obj : Priv;
      Full_View_Other_Priv_Obj : Other_Priv;

   begin
      Rec_Object.Op_1 (123);
      Acc_Rec_Object.Op_1 (777);
      Acc_Rec_Object.Op_2 (True);

      Full_View_Priv_Obj.Prim_Op_1 (456);
      Full_View_Priv_Obj.Prim_Op_2 (456);
      Full_View_Priv_Obj.Prim_Op_3 (456);

      Full_View_Other_Priv_Obj.Prim_Op_1 (456);
      Full_View_Other_Priv_Obj.Prim_Op_2 (456);
      Full_View_Other_Priv_Obj.Prim_Op_3 (456);
   end Pkg;

   -------------------------------------------------------------

   package Derived_Pkg is

      type D_Priv is private;

      procedure Prim_Op_1 (Obj : D_Priv; I : Integer);

   private

      procedure Prim_Op_2 (Obj : D_Priv; I : Integer);

      procedure Misc_Op (Obj : D_Priv; I : Integer);

      type D_Priv is new Pkg.Priv;

      procedure Prim_Op_3 (Obj : D_Priv; I : Integer);

   end Derived_Pkg;

   package body Derived_Pkg is

      procedure Prim_Op_1 (Obj : D_Priv; I : Integer) is
      begin
         null;
      end Prim_Op_1;

      procedure Prim_Op_2 (Obj : D_Priv; I : Integer) is
      begin
         null;
      end Prim_Op_2;

      procedure Misc_Op (Obj : D_Priv; I : Integer) is
      begin
         null;
      end Misc_Op;

      procedure Prim_Op_3 (Obj : D_Priv; I : Integer) is
      begin
         null;
      end Prim_Op_3;

      Full_View_Obj : D_Priv;

   begin
      Full_View_Obj.Prim_Op_1 (456);
      Full_View_Obj.Prim_Op_2 (456);
      Full_View_Obj.Misc_Op (456);
      Full_View_Obj.Prim_Op_3 (456);
   end Derived_Pkg;

   -------------------------------------------------------------

   generic
      type Formal_Derived_Rec is new Pkg.Rec;
   package Gen_Pkg is
      type Acc_FDR is access all Formal_Derived_Rec;
   end Gen_Pkg;

   package body Gen_Pkg is

      FDR_Object : Formal_Derived_Rec (555);

      Acc_FDR_Object : Acc_FDR := new Formal_Derived_Rec (777);

   begin
      FDR_Object.Op_1 (123);
      Acc_FDR_Object.Op_2 (True);
   end Gen_Pkg;

   -------------------------------------------------------------

   Rec_Object : aliased Pkg.Rec (222);
   B : Boolean := Rec_Object.Op_3;  -- OK, resolves to component Op_3

   subtype Sub_Rec is Pkg.Rec (333);

   Sub_Rec_Object : Sub_Rec;

   type New_Rec is new Pkg.Rec (777);

   New_Rec_Object : New_Rec;

   -------------------------------------------------------------

   Priv_Object : Pkg.Priv;

   type New_Priv is new Pkg.Priv;

   New_Priv_Object : New_Priv;
   D_Priv_Object : Derived_Pkg.D_Priv;

   type New_D_Priv is new Derived_Pkg.D_Priv;

   New_D_Priv_Object : New_D_Priv;
   Other_Priv_Object : Pkg.Other_Priv;

   -------------------------------------------------------------

   Int_1_Object : Pkg.Int_1;
   Int_2_Object : Pkg.Int_2;
   Int_3_Object : Pkg.Int_3;

   subtype Sub_Int_1_A is Pkg.Int_1;
   subtype Sub_Int_1_B is Sub_Int_1_A range 1 .. 10;

   Sub_Int_1_A_Object : Sub_Int_1_A;
   Sub_Int_1_B_Object : Sub_Int_1_B;

   Acc_Rec_Object : aliased Pkg.Acc_Rec := new Pkg.Rec (456);
   Acc_Acc_Rec_Object : Pkg.Acc_Acc_Rec := new Pkg.Acc_Rec;

   type New_Acc_Rec is new Pkg.Acc_Rec;

   New_Acc_Rec_Object : New_Acc_Rec;

begin
   Rec_Object.Op_1 (123);
   Acc_Rec_Object.Op_1 (777);
   Acc_Rec_Object.Op_2 (True);
   --  Rec_Object'Access.Op_2 (True);
   Sub_Rec_Object.Op_1 (123);
   New_Rec_Object.Op_1 (123);

   Priv_Object.Prim_Op_1 (123);
   New_Priv_Object.Prim_Op_1 (123);
   D_Priv_Object.Prim_Op_1 (123);
   New_D_Priv_Object.Prim_Op_1 (123);

   Other_Priv_Object.Prim_Op_1 (123);
   if Other_Priv_Object."="(Other_Priv_Object) then
      null;
   end if;

   Int_1_Object.Proc_Op (123);
   Int_1_Object := Int_1_Object."+" (Int_1_Object);
   Int_2_Object.Proc_Op (123);
   Int_3_Object.Proc_Op (123);
   Sub_Int_1_A_Object.Proc_Op (123);
   Sub_Int_1_B_Object.Proc_Op (123);

   Acc_Rec_Object.Op_1 (123);
   Acc_Acc_Rec_Object.Op_2 (True);
   Acc_Rec_Object.Op_2 (True);
   New_Acc_Rec_Object.Op_1 (123);
end Untagged_Prefixed_Calls;
