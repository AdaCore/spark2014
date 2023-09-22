--  Same as before, but with visibility on the full view to check whether is is
--  allowed to create a constrained object.

procedure Test_5 with SPARK_Mode is
   package Nested is
      type Option_Priv is private;
      None_Priv : constant Option_Priv;
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
      None_Priv : constant Option_Priv := (Present => False);
   end Nested;
   use Nested;

   type Option_2 is new Option_Priv;

   package body Nested is
      procedure Test is
         type Option is new Option_2;
         None : constant Option := Option (None_Priv);

         type Option_Access is access all Option;
         V : aliased Option (True) := (True, 12); --  This is rejected by the frontend
         A : Option_Access := V'Access;

         procedure P (X : in out not null Option_Access) is
         begin
            X.all := None; -- The compiler emits a spurious error here
         end P;

      begin
         P (A);
      end Test;
   end Nested;

begin
   Nested.Test;
end Test_5;
