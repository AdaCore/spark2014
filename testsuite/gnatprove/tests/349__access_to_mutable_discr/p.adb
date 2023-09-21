procedure P with SPARK_Mode is

   --  Test that we are handling access types designating types with mutable
   --  discriminants properly.

   --  Test_1: In general, the object designated by an access type is considered
   --  to be constrained. Check that 'Constrained works as expected and that we
   --  have the expected discriminant checks.

   procedure Test_1 is
      type Option (Present : Boolean := False) is record
         case Present is
         when True =>
            The_Value : Integer;
         when False =>
            null;
         end case;
      end record;

      type Option_Access is access all Option;

      procedure P (X : in out not null Option_Access) is
      begin
         pragma Assert (X.all'Constrained);
         X.all := (Present => False); --@DISCRIMINANT_CHECK:FAIL
      end P;

      type Holder is record
         H : not null Option_Access;
      end record;

      V : aliased Option (True) := (True, 12);
      W : aliased Option := (True, 12);
      I : Option_Access := V'Access;
      J : Option_Access := W'Access;
      A : Holder := (H => I);
      B : Holder := (H => J);

      procedure P (X, Y : in out Holder; B : Boolean) with Global => null;
      procedure P (X, Y : in out Holder; B : Boolean) is
      begin
         pragma Assert (X.H'Constrained and Y.H'Constrained);
         pragma Assert (if B then X.H.Present = Y.H.Present); -- @ASSERT:FAIL
         X.H.all := (Present => False); --@DISCRIMINANT_CHECK:FAIL
      end P;

   begin
      P (A, B, False);
   end Test_1;

   --  Test_2: As an exception to the rule above, the object designated by an
   --  access type is considered to be unconstrained if the designated type has
   --  an unconstrained private view. Check that we can assign the designated
   --  object arbitrarily in that case.

   procedure Test_2 is
      package Nested is
         type Option is private;
         None : constant Option;
      private
         type Option (Present : Boolean := False) is record
            case Present is
            when True =>
               The_Value : Integer;
            when False =>
               null;
            end case;
         end record;
         None : constant Option := (Present => False);
      end Nested;
      use Nested;

      type Option_Access is access all Option;

      procedure P (X : in out not null Option_Access) is
      begin
         X.all := None; --@DISCRIMINANT_CHECK:PASS
      end P;

      type Holder is record
         H : not null Option_Access;
      end record;

      procedure P (X : in out Holder) with Global => null;
      procedure P (X : in out Holder) is
      begin
         X.H.all := None; --@DISCRIMINANT_CHECK:PASS
      end P;

   begin
      null;
   end Test_2;

begin
   Test_1;
end P;
