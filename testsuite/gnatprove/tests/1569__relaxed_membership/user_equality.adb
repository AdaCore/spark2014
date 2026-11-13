procedure User_Equality (Result : out Boolean) with SPARK_Mode is
   type I is new Integer with Relaxed_Initialization;
   type Rec is record
      F : I;
   end record;
   function "=" (Left, Right : Rec) return Boolean is (False);
   type Arr is array (1 .. 1) of Rec;
   A : Rec := (F => 0);
   C : Rec := (F => 1);
   B : Rec;
   AA : Arr := (others => A);
   CC : Arr := (others => C);
   BB : Arr;
begin
   Result := A in C | B; -- @INIT_BY_PROOF:PASS
   pragma Assert (not Result); -- @ASSERT:PASS
   Result := AA in CC | BB; -- @INIT_BY_PROOF:PASS
   pragma Assert (not Result); -- @ASSERT:PASS
end User_Equality;
