procedure Test_Declare with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   procedure Bad_1 with Global => null is
      X : Integer := 1;
   begin
      X := (declare
            Y : constant Integer := Id (Integer'Last) - 3;
            Z : constant Integer := Y + 4; --@OVERFLOW_CHECK:FAIL
            begin Z + Y);
   end Bad_1;

   procedure Bad_2 with Global => null is
      X : Integer := 1;
   begin
      X := (declare
            Y : constant Integer := Id (Integer'Last) - 3;
            Z : constant Integer := Y + 1;
            begin Z + Y); --@OVERFLOW_CHECK:FAIL
   end Bad_2;

   X : Integer := 1;
begin
   X := (declare
           Y : constant Integer := Id (3);
         begin Y + X);
   X := (declare
           Y renames X;
         begin Y + X);
   pragma Assert (X = 8);
   pragma Assert
       ((declare
           Y : constant Integer := Id (3);
           Z : constant Integer := Y + 1;
         begin Z + Y) = 7);
end Test_Declare;
