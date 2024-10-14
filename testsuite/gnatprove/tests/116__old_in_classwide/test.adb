procedure Test with SPARK_Mode is

   package Nested is
      type Root is tagged record
         X : Integer;
      end record;

      function F (X : Root) return Boolean is (True);

      procedure P (X : in out Root) with
        Post'Class => F (X'Old); -- @POSTCONDITION:FAIL

      procedure P (X : in out Root) is null;

      type Child is new Root with record
         Y : Integer;
      end record;

      function F (X : Child) return Boolean is (False);

      procedure P (X : in out Child) is null;
   end Nested;
   use Nested;

   X : Child := (1, 2);

begin
   P (X);
end Test;
