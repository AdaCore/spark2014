package Repro
--  with SPARK_Mode
is
--     function Contrainte1 (sortie1 : in boolean;
--                           sortie2 : in boolean)
--       return Boolean
--     with SPARK_Mode;

   function Contrainte1 (sortie1 : in boolean;
                         sortie2 : in boolean)
     return boolean is (sortie1=sortie2)
   with SPARK_Mode;

   procedure  exigence(sortie1:  in out boolean;
                       sortie2 : in out boolean)
     with SPARK_Mode,
   post =>  (Contrainte1(sortie1,sortie2));
end Repro;
