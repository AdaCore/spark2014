package P is

   type T1 is delta 0.000001 range 0.0 .. 1.0;
   type T2 is new T1'Base;
   MDCY : T2;

end P;
