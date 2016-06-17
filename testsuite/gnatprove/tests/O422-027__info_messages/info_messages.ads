package Info_Messages with SPARK_mode is
   type Nat_Array is array (Positive range <>) of Natural;

   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Found  : out Boolean;
                     Result : out Positive);
end Info_Messages;
