with System.Storage_Elements;
with Interfaces;
with Ada.Unchecked_Conversion;
package body U2
  with SPARK_Mode => On,
       Refined_State => (Port => (Raw_Port1, Raw_Port2))
is
   type A is array (Boolean) of Character;

   C : constant A := ('F', 'T');

   Raw_Port1 : Boolean
     with Import,
          Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEADBEEF#);

   Raw_Port2 : Interfaces.Unsigned_8
     with Import,
          Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEEDBEEF#);

   function Conv is new Ada.Unchecked_Conversion (Interfaces.Unsigned_8, Boolean);

   procedure Read1 (X : out Character)
   is
      T : Boolean;
   begin
      --  No warning here because the user has forgotten to use
      --  or doesn't know about 'Valid!
      T := Raw_Port1;
      X := C (T);
   end Read1;

   procedure Read2 (X : out Character)
   is
      T : Boolean;
   begin
      T := Raw_Port1;
      if T'Valid then
         X := C (T); --  This should be OK since (T'Valid -> T in Boolean)
      else
         T := Boolean'Succ (T); --  Potential Constraint_Error here,
                                --  but GNATProve says "range check proved"
         X := C (T);
      end if;
   end Read2;

   procedure Read3 (X : out Character)
   is
      T : Boolean;
   begin
      --  No 'Valid AND unsafe use of U_C
      --  Warning on line 24 is the ONLY clue that this is wrong.
      T := Conv (Raw_Port2);
      X := C (T);
   end Read3;

   procedure Read4 (X : out Character)
   is
      T : Boolean;
   begin
      -- Unsafe use of U_C followed by 'Valid
      T := Conv (Raw_Port2);
      if T'Valid then
         X := C (T); --  This should be OK since (T'Valid -> T in Boolean)
      else
         T := Boolean'Succ (T); --  Potential Constraint_Error here,
                                --  but GNATProve says "range check proved"
         X := C (T);
      end if;
   end Read4;


end U2;
