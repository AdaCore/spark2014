pragma Assertion_Level (Silver);
pragma Assertion_Level (Gold, Depends => [Silver, Static]);

procedure Main with spark_mode is
   type Int_Acc is access Integer;

   function Create return Int_Acc is (new Integer'(12));

   function Read (X : Int_Acc) return Boolean is (X /= null);

   X : Int_Acc := new Integer'(12) with Ghost => Silver; -- @RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
   Y : Int_Acc := new Integer'(12) with Ghost => Gold; -- @RESOURCE_LEAK_AT_END_OF_SCOPE:NONE

   procedure Test_Silver with Ghost => Silver is
      X : Int_Acc := new Integer'(12) with Ghost; -- @RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
      Y : Int_Acc := new Integer'(12) with Ghost => Gold; -- @RESOURCE_LEAK_AT_END_OF_SCOPE:NONE

   begin
      pragma Assert (Create /= null); -- @RESOURCE_LEAK:FAIL
      pragma Assert (Gold => Create /= null); -- @RESOURCE_LEAK:NONE
      pragma Assert (Read (new Integer'(12))); -- @RESOURCE_LEAK:FAIL
      pragma Assert (Gold => Read (new Integer'(12))); -- @RESOURCE_LEAK:NONE
   end;

   procedure Test_Gold with Ghost => Gold is
      X : Int_Acc := new Integer'(12) with Ghost; -- @RESOURCE_LEAK_AT_END_OF_SCOPE:NONE

   begin
      pragma Assert (Create /= null); -- @RESOURCE_LEAK:NONE
      pragma Assert (Read (new Integer'(12))); -- @RESOURCE_LEAK:NONE
   end;

begin
   pragma Assert (Silver => Create /= null); -- @RESOURCE_LEAK:FAIL
   pragma Assert (Gold => Create /= null); -- @RESOURCE_LEAK:NONE
   pragma Assert (Silver => Read (new Integer'(12))); -- @RESOURCE_LEAK:FAIL
   pragma Assert (Gold => Read (new Integer'(12))); -- @RESOURCE_LEAK:NONE
end Main;
