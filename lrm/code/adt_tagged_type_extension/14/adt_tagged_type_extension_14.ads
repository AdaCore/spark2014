-- Confirm that no inherit clause in SPARK 2014.

package adt_tagged_type_extension_14.adt_tagged_type_extension_14 is

   type Monitored_Stack is new adt_tagged_type_extension_14.Stack with private;

   overriding
   procedure Clear(S : out Monitored_Stack);
   with
      Depends => (S => null);

   overriding
   procedure Push(S : in out Monitored_Stack; X : in Integer);
   with
      Depends => (S =>+ X)

   function Top_Identity(S : Monitored_Stack) return Integer;
   function Next_Identity(S : Monitored_Stack) return Integer;

private

   type Monitored_Stack is new adt_tagged_type_extension_14.Stack with
      record
         Monitor_Vector : adt_tagged_type_extension_14.Vector;
         Next_Identity_Value : Integer;
      end record;

end adt_tagged_type_extension_14.adt_tagged_type_extension_14;
