package Exclude_Selected_Parts is

   procedure Critical_Action;

   procedure Non_Critical_Action;

   package Non_Critical_Data with
     SPARK_Mode => Off
   is
      type T is access Integer;
      X : T;
      function Get_X return Integer;
   end Non_Critical_Data;

end Exclude_Selected_Parts;
