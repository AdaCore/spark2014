procedure Test_Access_Violation with SPARK_Mode is
   type Rec is record
      F1, F2 : aliased Integer;
   end record;

   type C_Int_Acc is access constant Integer;

   type Holder is record
      G : C_Int_Acc;
   end record;

   function F (I : Integer) return Rec with Import;

   function F (I : Integer) return Holder with Import,
     Post => F'Result.G /= null;

   function B return Boolean with Import;

   function Id (I : access constant Integer) return access constant Integer with Import;

   function Id2 (I : aliased Integer) return access constant Integer is
     (I'Access); -- Bad: 'Access not supported in expression functions

   V : aliased Integer := 15;
   C : aliased constant Integer := 15;
   R : aliased Rec := (12, 13);
   T : aliased Rec := (13, 12);
   S : C_Int_Acc := Rec'(if B then R else T).F1'Access; -- Bad: Prefix must be a path
   X : C_Int_Acc := F (15).F1'Access; -- Bad: Prefix must be rooted in an object
   Y : C_Int_Acc := Id (C'Access); -- Bad: 'Access only supported at top-level
   Z : C_Int_Acc := V'Access; -- Bad: path rooted at a variable
   H : Holder := F (15);
   U : C_Int_Acc := H.G.all'Access; -- OK: G is a constant part of H
begin
   declare
      type C_Int_Acc is access constant Integer;
      Obs : access constant Rec := R'Access; -- OK: Obs is an observer, not a named access-to-constant
      Z : C_Int_Acc := Obs.F1'Access; -- Bad: path rooted at an observer
   begin
      null;
   end;
end Test_Access_Violation;
