package Update_Legal
  with SPARK_Mode
is
   type Array_T is array (Integer range 1 .. 5) of Boolean;

   procedure P1 (Arr : in out Array_T);
end Update_Legal;
