package P
  with SPARK_Mode => Off
is
   subtype T1 is Integer range 0 .. 10;
   subtype T1bis is Integer range 0 .. 10;
   subtype T1ter is T1;
   subtype T2 is Integer range 0 .. 20;

   type AT1 is array (T1) of T1;
   type AT1bis is array (T1bis) of T1bis;
   type AT1ter is array (T1ter) of T1ter;

   function Conv_T1_T2 (I : T1) return T2 is
      (T2 (I));

   function Conv_AT1_AT1bis (A : AT1) return AT1bis;
   function Conv_AT1_AT1bis (A : AT1) return AT1bis is
      (AT1bis (A));

   function Conv_AT1_AT1ter (A : AT1) return AT1ter;
   function Conv_AT1_AT1ter (A : AT1) return AT1ter is
      (AT1ter (A));

   function Conv_AT1_AT1 (A : AT1) return AT1 is
      (AT1 (A));
end P;
