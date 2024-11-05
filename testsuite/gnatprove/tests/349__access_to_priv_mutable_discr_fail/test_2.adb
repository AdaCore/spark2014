--  Make sure that it is not acutally possible to create a constrained object
--  in this case.

procedure Test_2 with SPARK_Mode is
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

         V : aliased Option (True) := (True, 12); --  This is rejected by the frontend
         A : Option_Access := V'Access;

      begin
         P (A);
      end Test;
   end Nested;

begin
   Nested.Test;
end Test_2;
