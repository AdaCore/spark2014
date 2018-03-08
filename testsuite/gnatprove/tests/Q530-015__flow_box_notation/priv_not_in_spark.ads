package Priv is
   type T is private;


private
   pragma SPARK_Mode (Off);
   type T is record
      A : Integer;
   end record;

   Ob : T := (others => <>);
end Priv;
