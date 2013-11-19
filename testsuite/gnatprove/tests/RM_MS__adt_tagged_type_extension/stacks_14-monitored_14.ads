package Stacks_14.Monitored_14
  with SPARK_Mode
is
   type Monitored_Stack is new Stacks_14.Stack with private;

   overriding
   procedure Clear(S : out Monitored_Stack)
     with Depends => (S    => null,
                      null => S);

   overriding
   procedure Push(S : in out Monitored_Stack; X : in Integer)
     with Depends => (S =>+ X);

   function Top_Identity(S : Monitored_Stack) return Integer;
   function Next_Identity(S : Monitored_Stack) return Integer;

private
   type Monitored_Stack is new Stacks_14.Stack with record
      Monitor_Vector : Stacks_14.Vector;
      Next_Identity_Value : Integer;
   end record;
end Stacks_14.Monitored_14;
