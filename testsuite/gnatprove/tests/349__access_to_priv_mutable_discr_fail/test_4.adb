--  Seccond attempt, with a derivation at a location where the full view of
--  Option_Priv is not visible. This is rejected by the compiler with an
--  error.

procedure Test_4 with SPARK_Mode is
   package Nested is
      type Option_Priv is private;
      None_Priv : constant Option_Priv;
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
   procedure Test;

   procedure Test is
      type Option is new Option_2;
      None : constant Option := Option (None_Priv);

      type Option_Access is access all Option;

      procedure P (X : in out not null Option_Access) is
      begin
         X.all := None; -- The compiler emits a spurious error here
      end P;

   begin
      null;
   end Test;

begin
   Test;
end Test_4;
