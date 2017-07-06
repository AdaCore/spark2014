package body Prot with SPARK_Mode is

   protected body P is
      procedure Read is
      begin
         P.Count := P.Count + 1;
      end Read;

      procedure Read_With_Global is
      begin
         P.Count := P.Count + 1;
      end Read_With_Global;
   end P;

end Prot;
