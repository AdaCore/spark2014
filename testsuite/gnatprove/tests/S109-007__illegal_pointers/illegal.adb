procedure Illegal with SPARK_Mode is
   type Ptr is access Integer;
   X : Ptr := new Integer'(1);

   function F (X : Ptr) return Integer is (X.all);

   type Ptr_V is new Ptr with Volatile;

   function F_2 (X : Ptr_V) return Integer is (1) with Volatile_Function;

   function F_3 (X : Integer) return Ptr is (new Integer'(X));  -- illegal

   function F_4 (X : Integer) return Ptr is (new Integer'(X)) with Volatile_Function; --  legal

   Y : Integer := F (X);
begin
   Y := F (new Integer'(1));  -- illegal
   Y := F_2 (new Integer'(1)); --  legal
end Illegal;
