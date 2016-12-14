package P with SPARK_Mode is

   task type TT;

   V : Integer := 0;
   -- unsynchronized variable accessed by task type TT
   
end;
