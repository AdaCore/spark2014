package Private_Types with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   package P1 is
      type T (D : Boolean := False) is private;
   private
      type T (D : Boolean := False) is record
         case D is
            when True =>
               F : Positive := Id (0); --@RANGE_CHECK:FAIL
            when False => null;
         end case;
      end record;
   end P1;

   package P2 is
      type T (<>) is tagged private;

      type T2 is private;
   private
      type T (D : Boolean) is tagged record
         case D is
            when True =>
               F : Positive := Id (0); --@RANGE_CHECK:FAIL
            when False => null;
         end case;
      end record;

      X : T (True);

      type T2 is new T (True) with null record;
   end P2;

   package P3 is
      type T is private;
   private
      type T (D : Boolean := False) is record
         case D is
            when True =>
               F : Positive := Id (0); --@RANGE_CHECK:FAIL
            when False => null;
         end case;
      end record;

      X : T (True);
   end P3;

   package P4 is
      type T (<>) is tagged private;

      type T2 is new T with private;
   private
      type T (D : Boolean) is tagged record
         case D is
            when True =>
               F : Positive := Id (0); --@RANGE_CHECK:FAIL
            when False => null;
         end case;
      end record;

      type T2 is new T (True) with null record;
      X : T2;
   end P4;

end Private_Types;
