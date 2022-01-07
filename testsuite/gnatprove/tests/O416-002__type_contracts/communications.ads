with Messages; use Messages;

package Communications
  with SPARK_Mode
is
   type Communication (Num : Positive) is private;

   type Message_Arr is array (Integer range <>) of Message;

   function Create (A : Message_Arr) return Communication;

   procedure Mark_Duplicates (Com : in out Communication);

private

   type Communication (Num : Positive) is record
      Msgs : Message_Arr (1 .. Num);
   end record
     with Type_Invariant =>
       (for all Idx in 1 .. Communication.Num-1 =>
          Communication.Msgs(Idx).Received <= Communication.Msgs(Idx+1).Received);

end Communications;
