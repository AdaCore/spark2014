procedure Test with SPARK_Mode is

   --  Test that we emit appropriate explanations on discriminant checks on
   --  formal parameters with mutable discriminants.

   type T (B : Boolean := True) is record
      case B is
         when True =>
            Content : Integer;
         when False => null;
      end case;
   end record;

   procedure Update (X : in out T) is
   begin
      X := (B => False); -- @DISCRIMINANT_CHECK:FAIL
   end Update;

   package Nested is
      type T is private;
      procedure Update (X : in out T);
   private
      type T (B : Boolean := True) is record
         case B is
            when True =>
               Content : Integer;
            when False => null;
         end case;
      end record;
   end Nested;

   package body Nested is
      procedure Update (X : in out T) is
      begin
         X := (B => False); -- @DISCRIMINANT_CHECK:FAIL
      end Update;
   end Nested;
begin
   null;
end;
