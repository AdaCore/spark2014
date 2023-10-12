--  Attempt to create a more complex case with a type derivation. This
--  is rejected by marking due to "discriminants on derived types" but
--  executing it does not seem to exhibit the corner case.

procedure Test_3 with SPARK_Mode is
   package Nested is
      type Option_Priv is private;
      procedure Test;
   private
      type Option_Priv (Present : Boolean := False) is record
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
         type Option is new Option_Priv;
         None : constant Option := (Present => False);

         type Option_Access is access all Option;

         procedure P (X : in out not null Option_Access) is
         begin
            X.all := None; -- The object seems to be constrained for the compiler, is it expected?
         end P;

         V : aliased Option := (True, 12);
         A : Option_Access := V'Access;

      begin
         P (A);
      end Test;
   end Nested;

begin
   Nested.Test;
end Test_3;
