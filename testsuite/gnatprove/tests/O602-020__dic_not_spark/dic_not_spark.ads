package Dic_Not_Spark is

   type Bad1 is private with
     Default_Initial_Condition => Add (Bad1, Total);

   Total : Natural := 0;

   function Add (X : Bad1; Y : in out Natural) return Boolean;

   package With_SPARK_Mode with SPARK_Mode is

      type Bad2 is private with
        Default_Initial_Condition => Add (Bad2, Total);

      function Add (X : Bad2; Y : in out Natural) return Boolean;
   private
      type Bad2 is new Natural;
   end With_SPARK_Mode;

private
   type Bad1 is new Natural;
end Dic_Not_Spark;
