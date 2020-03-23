package Caller with
   SPARK_Mode
is
   package Dic with
      SPARK_Mode
   is

      type Pr_T is private;

      function Evaluate (R : Pr_T) return Integer;
   private
      type Pr_T is record
         X : Integer;
         Y : Integer := 0;
      end record;

      function Evaluate (R : Pr_T) return Integer is (R.X);
   end Dic;

   type Pr_TT_2 is private;

private
   use Dic;
   type Pr_TT_2 is new Pr_T with
      Type_Invariant => Evaluate (Pr_T (Pr_TT_2)) = 10;
end Caller;
