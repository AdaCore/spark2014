package Q is

   procedure Proc with SPARK_Mode => On;

   protected type PT2 is
      procedure Proc2 (X : out Integer) with SPARK_Mode => On, Post => X = 0;
   end PT2;

   protected type PT with SPARK_Mode => Off is
      procedure P (A : access Integer)
        with SPARK_Mode => Off;
   private
      pragma SPARK_Mode (Off);
      A : access Integer;
   end PT;

   task type TT with SPARK_Mode => Off;

end Q;
