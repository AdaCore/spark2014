procedure Main with SPARK_Mode is

   --  Check that we do not emit an invariant check on exceptional exit for
   --  results of functions.

   package Nested is
      E : exception;
      type T is private;
      function Create (X, Y : Integer) return T with
        Side_Effects,
        Exit_Cases =>
          (X > Y => (Exception_Raised => E),
           others => Normal_Return);
   private
      type T is record
         F, G : Integer := 0;
      end record with
        Type_Invariant => F <= G;
   end Nested;

   package body Nested is
      function Create (X, Y : Integer) return T is
      begin
         if X > Y then
            raise E;
         end if;

         return (X, Y);
      end Create;
   end Nested;
begin
   null;
end Main;
