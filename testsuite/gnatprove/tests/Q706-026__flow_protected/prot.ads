package Prot with SPARK_Mode is

   protected P is
      procedure Read;
      procedure Read_With_Global with Global => null;
   private
      Count : Integer := 0;
   end P;

end Prot;
