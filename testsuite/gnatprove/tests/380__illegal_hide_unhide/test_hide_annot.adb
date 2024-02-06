procedure Test_Hide_Annot with SPARK_Mode is

   function T return Boolean is (True);

   function Id (X : Integer) return Integer is (X);

   function Hidden_Id (X : Integer) return Integer is (X) with
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  Wrong number of parameters

   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body");

   --  Third parameter shall be a string

   pragma Annotate (GNATprove, Hide_Info, 11, Id);

   --  Invalid third parameter

   pragma Annotate (GNATprove, Hide_Info, "foo", Id);

   --  Fourth parameter shall be an entity

   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", 11);

   --  Entity shall be an expression function

   function Not_Expr_Fun return Boolean with Import, Global => null;

   procedure Use_Not_Expr_Fun with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Not_Expr_Fun);
      B : Boolean := Not_Expr_Fun;
   begin
      null;
   end Use_Not_Expr_Fun;

   --  Entity shall be in SPARK

   function Not_SPARK return Boolean is (True) with SPARK_Mode => Off;

   procedure Use_Not_SPARK with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Not_SPARK);
   begin
      null;
   end Use_Not_SPARK;

   --  Entity body shall be in SPARK

   function Not_Body_SPARK return Boolean;

   function Not_Body_SPARK return Boolean is (True) with SPARK_Mode => Off;

   procedure Use_Not_Body_SPARK with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Not_Body_SPARK);
      B : Boolean := Not_Body_SPARK;
   begin
      null;
   end Use_Not_Body_SPARK;

   --  Entity shall not have a Refined_Post

   package Nested is
      function Refined (X : Integer) return Integer;
   end Nested;

   package body Nested is
      function Refined (X : Integer) return Integer is (X) with
        Refined_Post => Refined'Result <= X;

      procedure Use_Refined with Global => null is
         pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Refined);
         I : Integer := Refined (1);
      begin
        null;
      end Use_Refined;
   end Nested;

   --  Entity shall not be inlined

   function Inlined return Boolean is (True) with
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Use_Inlined with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Inlined);
      B : Boolean := Inlined;
   begin
      null;
   end Use_Inlined;

   function Inlined_2 return Boolean is (True) with
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
     Annotate => (GNATprove, Inline_For_Proof);

   --  Entity shall not be a logical equality

   function Eq (X, Y : Integer) return Boolean is (X = Y) with
     Annotate => (GNATprove, Logical_Equal);

   procedure Use_Eq with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Eq);
      B : Boolean := Eq (1, 2);
   begin
      null;
   end Use_Eq;

   function Eq_2 (X, Y : Integer) return Boolean is (X = Y) with
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
     Annotate => (GNATprove, Logical_Equal);

   --  Entity shall not be an at end borrow function

   function At_End_Borrow (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   procedure Use_At_End_Borrow with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", At_End_Borrow);
      X : aliased Integer := 12;
      B : access Integer := X'Access;
      C : constant access constant Integer := At_End_Borrow (B) with Ghost;
   begin
      null;
   end Use_At_End_Borrow;

   function At_End_Borrow_2 (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
     Annotate => (GNATprove, At_End_Borrow);

   --  Entity shall not have HO specialization

   function Call (F : not null access function return Boolean) return Boolean is (F.all) with
     Annotate => (GNATprove, Higher_Order_Specialization);

   procedure Use_Call with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Call);
      B : Boolean := Call (T'Access);
   begin
      null;
   end Use_Call;

   function Call_2 (F : not null access function return Boolean) return Boolean is (F.all) with
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
     Annotate => (GNATprove, Higher_Order_Specialization);

   --  There should not be several Hide/Unhide annotation for the same entity in the same scope

   procedure Duplicated_Annot with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Id);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Id);
   begin
      null;
   end Duplicated_Annot;

   --  Hide/unhide annotations should be at the beginning of the body

   procedure Misplaced_Annot with Global => null is
      X : Integer := Id (1);
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Id);
   begin
      null;
   end Misplaced_Annot;

   --  Accepted placements

   procedure OK_Top_Body with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Id);
   begin
      null;
   end OK_Top_Body;

   procedure OK_After_Spec with Global => null;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Id);

   procedure OK_After_Spec is
   begin
      null;
   end OK_After_Spec;

   procedure OK_After_Body with Global => null;

   procedure OK_After_Body is
   begin
      null;
   end OK_After_Body;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Id);

   function OK_After_Expr_Fun return Boolean is (True);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Id);

   --  Incompatible annotations with default

   procedure Incompatible with Global => null is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Id);
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Hidden_Id);
   begin
      null;
   end Incompatible;

   --  Expression function whose body is hidden in a package body. It can
   --  only be hidden/unhidden where it is visible.

   package Deferred_Expr_Fun is
      function Deferred_Id (X : Integer) return Integer;
      procedure OK_Deferred with Global => null;
   end Deferred_Expr_Fun;

   package body Deferred_Expr_Fun is
      function Deferred_Id (X : Integer) return Integer is (X);

      procedure OK_Deferred is
         pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Deferred_Id);
      begin
         null;
      end OK_Deferred;
   end Deferred_Expr_Fun;

   procedure Bad_Deferred with Global => null is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Deferred_Expr_Fun.Deferred_Id);
   begin
      null;
   end Bad_Deferred;

begin
   null;
end Test_Hide_Annot;
