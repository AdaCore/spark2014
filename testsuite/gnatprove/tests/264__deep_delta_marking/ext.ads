package Ext is
   package P1 is
      type R is private;

      function F (X : R) return R;
   private
      package Bad with SPARK_Mode => Off is
         type T is record
            F, G : Integer := 0;
         end record;
      end Bad;

      type R is record
         C : Bad.T;
      end record;

      function F (X : R) return R is ((X with delta C.F => 2));
   end P1;

   package P2 is
      type R is private;

      type My_Arr is private;

      function F (X : R) return R;
   private
      package Bad with SPARK_Mode => Off is
         type T is new Integer;
      end Bad;

      type My_Arr is array (Positive range 1 .. 10) of Bad.T;

      type R is record
         C : My_Arr;
      end record;

      function F (X : R) return R is ((X with delta C (1) => 2));
   end P2;

   package P3 is
      type R is private;

      type RR is private;

      function F (X : R) return R;
   private
      package Bad with SPARK_Mode => Off is
         type T is new Integer;
      end Bad;

      type RR is record
         D : Bad.T;
      end record;

      type R is record
         C : RR;
      end record;

      function F (X : R) return R is ((X with delta C.D => 2));
   end P3;
end Ext;
