package body Test_05 is

   procedure P_01 (X : Integer;
                   Y : out Integer)
   is

      package Nested is

         type T is private;

      private

         type T is new Integer with
            Type_Invariant => Integer (T) >= X;  -- I guess this is OK

      end Nested;

   begin
      Y := X;
   end P_01;

   procedure P_02 (X : in out Integer) is

      package Nested is

         type T is private;

      private

         type T is new Integer with
            Type_Invariant => Integer (T) >= X;  -- Not OK

      end Nested;

   begin
      X := X * 1;
   end P_02;

end Test_05;
