package For_Access_Subtype with SPARK_Mode is

   type tab is array (Positive range <>) of Integer;

   type L (N : integer) is record
      T : tab (1..N);
   end record;

   type L_Ptr is access L;
   L3 : L_Ptr(14);
end;
