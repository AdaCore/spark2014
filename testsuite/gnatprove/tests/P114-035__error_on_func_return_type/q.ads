package Q with SPARK_Mode is

   type Callback is access procedure;

   function F return Callback;

   procedure P (Arg : Callback);

end;
