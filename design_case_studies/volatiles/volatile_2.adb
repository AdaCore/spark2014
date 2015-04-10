-- The volatile input abstract state represented by V_S is refined onto a
-- volatile input variable, External_Input.
-- External_Input has aspects to show that it is volatile and has a specific
-- address.
-- The procedure Input_Is_Rising has a refined global aspect in terms of
-- External_Input'History.
-- The volatile variable External_Input can only be referenced on the RHS of a
-- simple assignment statement or as a parameter to an instance of
-- Unchecked_Conversion.
-- It cannot be used in a contract but <Volatile_Variable>'History may be used in
-- a postcondition or a refined postcondition of a procedure reading
-- (or updating) a volatile variable, and only in such placed.
-- This means we can use the name External_Input'History (1) to represent the
-- last value read from External_Input and External_Input'History (2) to
-- represent preceding value.
with System.Storage_Elements;
package body Volatile_2
with
  Refined_State => (V_S => (External_Input => (Volatile => Input)))
is
   External_Input : Integer;

   with
     Volatile => True,
     Address  => for External_Input'Address use
       System.Storage_Elements.To_Address (16#FFFF_FFFF#);


   procedure Input_Is_Rising (Rising : out Boolean)
   with
     Refined_Global => (Input => External_Input),
     Refined_Post   => Rising = External_Input'History (1) >
                                External_Input'History (2)
     -- <Volatile_Variable>'History can only appear in a
     -- postcondition or refined postcondition.
   is
      First_Value  : Integer;
      Second_Value : Integer;
   begin
      -- External_input can only appear in a simple assignment statement
      -- or as a parameter to an unchecked conversion.
      First_Value := External_Input;
      Second_Value := External_Input;
      Rising := Second_Value > First_Value;
   end Input_Is_Rising;

end Volatile_2;
