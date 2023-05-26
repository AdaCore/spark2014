procedure Assert_Assume_In_Declare with SPARK_Mode is
   function Shift (X : Integer) return Integer is
     (declare
        pragma Assert (X <= Integer'Last - 3);
      begin
        X + 3)
   with Pre => X <= Integer'Last - 3;
   procedure Sub (X : Integer) with Global => null;
   procedure Sub2 (X : Integer) with Global => null;
   procedure Sub (X : Integer)
   is
      Y : Integer :=
        (declare
            pragma Assume (X < 0);
            Z : constant Integer := X + 1;
            pragma Assert (Z <= 0);
         begin
            Shift (Z)
         );
   begin
      pragma Assert (Y <= 3);
   end Sub;
   procedure Sub2 (X : Integer) is
      Y : Integer :=
        (declare
            pragma Assert (X < 0); --@ASSERT:FAIL
            Z : constant Integer := X + 1;
         begin
            Shift (Z)
        );
   begin
      pragma Assert (Y <= 3);
   end Sub2;
begin
   Sub (-36);
   Sub2 (-42);
end Assert_Assume_In_Declare;
