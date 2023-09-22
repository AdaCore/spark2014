--  Test that we are handling access types designating types with mutable
--  discriminants properly.
--  Those are supposed to test an exception to the general rule that
--  the value designated by an access type is always considered to be
--  constrained. It occurs when the designated type has an ancestor with a
--  constrained private view.

--  Simplest test, Option itself has a contrained partial view, things seem
--  to work fine.

procedure Test_1 with SPARK_Mode is
   package Nested is
      type Option is private;
      procedure Test;
   private
      type Option (Present : Boolean := False) is record
         case Present is
            when True =>
               The_Value : Integer;
            when False =>
               null;
         end case;
      end record;
   end Nested;
   use Nested;

   package body Nested is
      procedure Test is
         None : constant Option := (Present => False);

         type Option_Access is access all Option;

         procedure P (X : in out not null Option_Access) is
         begin
            X.all := None; -- The object is unconstrained
         end P;

         V : aliased Option := (True, 12);
         A : Option_Access := V'Access;

      begin
         P (A);
      end Test;
   end Nested;

begin
   Nested.Test;
end Test_1;
