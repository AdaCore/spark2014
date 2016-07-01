package body Q is

   procedure Proc is
   begin
      null;
   end Proc;

   protected body PT2 is
      procedure Proc2 (X : out Integer) with SPARK_Mode => On is
      begin
         X := 2;
      end;
   end PT2;

   protected body PT with SPARK_Mode => Off is
      procedure P (A : access Integer)
        with SPARK_Mode => Off Is
         B : access Integer;
      begin
         B := A;
         Proc;
      end P;
   end PT;

   task body TT with SPARK_Mode => Off is
   begin
      null;
   end TT;

end Q;
