package Empty is
   pragma SPARK_Mode;

   procedure P;
   --  this procedure is empty and will be proved

   procedure Q;
   --  this procedure contains a check, but will not be proved
end Empty;
