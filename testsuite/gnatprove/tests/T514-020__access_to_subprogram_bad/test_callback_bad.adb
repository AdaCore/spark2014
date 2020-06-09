package body Test_Callback_Bad with SPARK_Mode is

   protected body P is
      function Get return Integer is
         type Incr_Fun is not null access function
           (X : Integer) return Integer;
         function F (Y : Integer) return Integer is
           (Y);
         C : Incr_Fun := F'Access;
      begin
         return 1;
      end Get;
   end P;

   procedure Prim (X : Root) is null;

   function F_Vol (X : Integer) return Integer is (X) with Volatile_Function;

   function F_Relaxed (X : Integer) return Integer is (X) with Relaxed_Initialization => X;

   procedure Test is
      type Proc is access procedure (X : Root);
      Y : Proc := Prim'Access;
      X : Incr_Fun := F_Vol'Access;
      Z : Incr_Fun := F_Relaxed'Access;
      W : Incr_Fun := Z.all'Access;
   begin
      null;
   end Test;

end Test_Callback_Bad;
