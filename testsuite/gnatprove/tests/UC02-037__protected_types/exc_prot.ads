pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package Exc_Prot with SPARK_Mode is

   Overflow : exception;

   protected Counter is
      function Get return Natural;
      procedure Init with
        Post => Get = 0;
      procedure Incr with
        Exceptional_Cases => (Overflow => Get = Integer'Last);
      procedure Incr_Twice with
        Exceptional_Cases => (Overflow => Get = Integer'Last);
   private
      X : Natural := 0;
   end Counter;

end;
