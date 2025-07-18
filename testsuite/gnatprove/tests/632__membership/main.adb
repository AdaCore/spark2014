procedure Main with SPARK_Mode is
   function Random return Integer with Import, Global => null;
   package A is
      type Root is tagged record X : Integer; end record;
      function Sentinel_A return Root is (X => 0);
      function Sentinel_B return Root is (X => -1);
      function "=" (A, B : Root) return Boolean
        with Import, Global => null;
      procedure Check_Is_Sentinel (X, S_A, S_B : Root; Y : out Boolean)
        with Import, Global => null,
          Post'Class => Y = (X in S_A | S_B);
      procedure Make_Sentinel (X : in out Root; S_A, S_B : Root)
        with Import, Global => null,
          Post'Class => X in S_A | S_B;
      procedure Make_Sentinel_Access (X : access Root; S_A, S_B : Root)
        with Import, Global => null,
          Pre'Class => (if X = null then X.all not in S_A),
          Post'Class => (if X not in null then X.all in S_B);
   end A;
   use A;
   package B is
      type Child is new Root with null record;
      overriding function Sentinel_B return Child is (X => 1);
      overriding procedure Check_Is_Sentinel (X, S_A, S_B : Child; Y : out Boolean)
        with Import, Global => null;
      overriding procedure Make_Sentinel (X : in out Child; S_A, S_B : Child)
        with Import, Global => null;
      overriding procedure Make_Sentinel_Access (X : access Child; S_A, S_B : Child)
        with Import, Global => null;
      overriding function "=" (A, B : Child) return Boolean is (A.X = B.X);
   end B;
   use B;
   Out_Bool : Boolean;
   RA : Root'Class := Child'(X => 0);
   RB : Root'Class := Child'(X => -1);
   RC : Root'Class := Child'(X => 1);
   X : aliased Root'Class := Child'(X => 42);
begin
   case Random is
      when 0 =>
         Check_Is_Sentinel (RA, Sentinel_A, Sentinel_B, Out_Bool);
         pragma Assert (Out_Bool); --@ASSERT:PASS
      when 1 =>
         Check_Is_Sentinel (RB, Sentinel_A, Sentinel_B, Out_Bool);
         pragma Assert (Out_Bool); --@ASSERT:FAIL
      when 2 =>
         Check_Is_Sentinel (RC, Sentinel_A, Sentinel_B, Out_Bool);
         pragma Assert (Out_Bool); --@ASSERT:PASS
      when 3 =>
         Make_Sentinel (X, Sentinel_A, Sentinel_B);
         Check_Is_Sentinel (X, Sentinel_A, Sentinel_B, Out_bool);
         pragma Assert (Out_Bool); --@ASSERT:PASS
      when 4 =>
         Make_Sentinel (X, Sentinel_A, Sentinel_B);
         pragma Assert (X.X in -1 .. 0); --@ASSERT:FAIL;
      when others =>
         null;
   end case;
end Main;
