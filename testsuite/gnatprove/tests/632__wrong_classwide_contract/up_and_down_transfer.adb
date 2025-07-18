procedure Up_And_Down_Transfer with SPARK_Mode is
   function Random return Integer with Import, Global => null;
   package A is
      type Root is tagged record
         Label : Integer;
      end record;
      function Sentinel return Root is (Label => 0);
      function Equivalent (X, Y : Root) return Boolean is
        (X.Label mod 2 = Y.Label mod 2);
      function Is_Sentinel (X : Root) return Boolean
        with Import, Global => null, Post'Class =>
          Is_Sentinel'Result = Equivalent (X, Sentinel)
          and then Is_Sentinel'Result = Equivalent (Sentinel, X);
   end A;
   use A;
   package B is
      type Child is new Root with null record;
      overriding function Sentinel return Child is (Label => 1);
      function Equivalent (X, Y : Child) return Boolean is
         (X.Label mod 3 = Y.Label mod 3);
      overriding function Is_Sentinel (X : Child) return Boolean
        with Import, Global => null;
   end B;
   use B;
   R : Root'Class := Root'(Label => 0);
   S : Root'Class := Root'(Label => 1);
   T : Root'Class := Child'(Label => 1);
   U : Root'Class := Child'(Label => 0);
   V : Root'Class := Child'(Label => 4);
   W : Root'Class := Child'(Label => 2);
   Direct : Child := Child'(Label => 4);
begin
   case Random is
      when 0 =>
         pragma Assert (Is_Sentinel (R)); --@ASSERT:PASS
      when 1 =>
         pragma Assert (Is_Sentinel (S)); --@ASSERT:FAIL
      when 2 =>
         pragma Assert (Is_Sentinel (T)); --@ASSERT:PASS
      when 3 =>
         pragma Assert (Is_Sentinel (U)); --@ASSERT:FAIL
      when 4 =>
         pragma Assert (Is_Sentinel (V));
      when 5 =>
         pragma Assert (Is_Sentinel (W)); --@ASSERT:FAIL
      when 6 =>
         pragma Assert (Is_Sentinel (Direct));
      when others =>
         null;
   end case;
end Up_And_Down_Transfer;
