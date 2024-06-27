package body P.Child with SPARK_Mode is

   protected body Prot is
      function Get_Body return T is (-1); --@INVARIANT_CHECK:NONE
      function Get_Priv return T is (-1); --@INVARIANT_CHECK:NONE
      function Get return T is (-1);
   end Prot;

end P.Child;
