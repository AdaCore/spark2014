-- The volatile input abstract state represented by V_S is refined onto a
-- volatile input variable, External_Input.
-- External_Input has aspects to show that it is volatile and has a specific
-- address.
-- The body of Is_Valid may be implemented as a simple expression function.
-- The procedure Read has a refined global aspect and has only been given
-- a refined postcondition to extend the abstract postcondition with the
-- constraint that Value - External_Input'History (1).
-- The volatile variable External_Input can only be referenced on the RHS of a
-- simple assignment statement or as a parameter to an instance of
-- Unchecked_Conversion.
-- It cannot be used in a contract but <Volatile_Variable>'History may be used in
-- a postcondition or a refined postcondition of a procedure reading
-- (or updating) a volatile variable, and only in such placed.
-- This means we can use the name External_Input'History (1) to represent
-- the value just read from External_Input.
-- The extension of the postcondition is necessary otherwise an implmentation
-- such as Value := 5 would satisfy the postcondition Value > 0.
with System.Storage_Elements;
package body Volatile_1
with
  Refined_State => (V_S => (Volatile => (Extenal_Input => Input)))
is
   External_Input : T
   with
     Volatile => True,
     Address  => for External_Input'Address use
       System.Storage_Elements.To_Address (16#FFFF_FFFF#);


   function Is_Valid (V : T) return Boolean is ( V > 0);

   procedure Read (Value : out T)
   with
     Refined_Global => (Input => External_Input),
     Refined_Post   => Is_Valid (Value) and
                       Value = External_Input'History (1)
     -- <Volatile_Variable>'History can only appear in a
     -- postcondition or refined postcondition.
   is
   begin
      loop
         -- External_input can only appear in a simple assignment statement
         -- or as a parameter to an unchecked conversion.
         Value := External_Input;
         exit when Is_Valid (Value);
      end loop;
   end Read;
end Volatile_1;
