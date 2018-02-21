package Ext with SPARK_Mode is
   subtype My_Pos is Positive range 1 .. 100;

   X : My_Pos := 4;

   type M is array (Positive range <>, Positive range <>) of Natural;

   subtype MM is M (1 .. 3, 1 .. 3);

   function New_M return MM;
end Ext;
