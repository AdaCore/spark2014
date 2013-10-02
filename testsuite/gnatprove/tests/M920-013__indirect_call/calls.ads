pragma SPARK_Mode;

package Calls is

   package Inner is
      procedure C1;
      PC1 : access procedure := C1'Access;

      task T is
         entry C2;
      end;

      protected P is
         procedure C3;
      end;

      type R is tagged null record;
      procedure C4 (X : R'Class);
      X : R;
      Y : R'Class := X;
   end Inner;

   procedure C;

end Calls;
