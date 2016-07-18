package Ex is

   function Get_Int (I : Integer) return Integer with SPARK_Mode;

   procedure Bug (X : in out Integer) with SPARK_Mode;


end Ex;
