-- Confirm that no inherit clause in SPARK 2012.

package Stacks.Monitoring is

   type Monitored_Stack is new Stacks.Stack with private;

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

   type Monitored_Stack is new Stacks.Stack with
      record
         Monitor_Vector : Stacks.Vector;
         Next_Identity_Value : Integer;
      end record;

end Stacks.Monitoring;
