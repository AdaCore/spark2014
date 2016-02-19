package P with SPARK_Mode is

   type T is limited private;

private
   pragma SPARK_Mode (Off);
   task type T;
end;
