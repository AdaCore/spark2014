package P with SPARK_Mode is

   type Callback is access procedure;

   procedure P (Arg : Callback);

   function F1 (Arg : Callback) return Integer;

   function F2 return Callback;

end;
