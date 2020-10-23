package Foo_relaxed with SPARK_Mode is

   type Int_Wrap is record
      X : Integer;
   end record;

   type Relaxed_Int64_Arr is array (Positive range 1 .. 4) of Int_Wrap with
     Relaxed_Initialization;

   type Message_Root is abstract tagged null record;

   type Dummy is new Message_Root with record
      Dummy : Int_Wrap := (X => 0);
      F     : Integer;
   end record;

   function F return Relaxed_Int64_Arr with Import;

   type Int_Wrapp_Acc is access Int_Wrap;

   Y : Relaxed_Int64_Arr := F;
   Z : Integer := Dummy'(Dummy => Y (1), F => 3).F; -- No init check needed
   X : Dummy := (Dummy => Y (2), F => 3); -- @INIT_BY_PROOF:FAIL
   V : Int_Wrapp_Acc := new Int_Wrap'(Y (3)); -- @INIT_BY_PROOF:FAIL

end Foo_relaxed;
