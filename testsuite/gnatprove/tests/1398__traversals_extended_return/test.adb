procedure Test with SPARK_Mode is

   --  Test extended return statement on traversal functions

   function At_End (X : Integer) return Integer is (X) with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   function At_End (X : access constant Integer) return access constant Integer
   is (X)
     with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   --  Examples with borrows

   function F (X : aliased in out Integer) return not null access Integer with
     Post => At_End (F'Result).all = At_End (X);

   function F (X : aliased in out Integer) return not null access Integer is
   begin
      return B : not null access Integer := X'Access do
         pragma Assert (At_End (B).all = At_End (X));
      end return;
   end F;

   function F2 (X : aliased in out Integer) return not null access Integer is
   begin
      return B : constant not null access Integer := X'Access do
         pragma Assert (At_End (B).all = At_End (X));
      end return;
   end F2;

   --  Examples with observes

   function F3 (X : aliased Integer) return not null access constant Integer is
   begin
      return B : not null access constant Integer := X'Access do
         null;
      end return;
   end F3;

   function F4 (X : aliased Integer) return not null access constant Integer is
   begin
      return B : constant not null access constant Integer := X'Access do
         null;
      end return;
   end F4;

   --  With an intermediate borrower

   type Int_Access is not null access Integer;
   type R is record
      C : Int_Access;
   end record;

   function At_End (X : R) return R is (X) with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function F5 (X : aliased in out R) return not null access Integer with
     Post => At_End (F5'Result).all = At_End (X).C.all;
   function F5 (X : aliased in out R) return not null access Integer is
      L_B : not null access R := X'Access;
   begin
      return B : not null access Integer := L_B.C do
         null;
      end return;
   end F5;

   --  Example with a reborrow

   type List;
   type List_Acc is access List;
   type List is record
      N : List_Acc;
   end record;

   function F6 (X : not null List_Acc) return not null access List is
   begin
      return B : not null access List := X do
         while B.N /= null loop
            B := B.N;
         end loop;
      end return;
   end F6;

   --  Example that should fail a dynamic accessibility check

   function F7 (X : aliased in out Integer) return not null access Integer is
      L_B : not null access Integer := X'Access;
   begin
      return B : not null access Integer := L_B do -- @ACCESSIBILITY_CHECK:FAIL
         null;
      end return;
   end F7;
begin
   null;
end;
