pragma Ada_2022;

procedure Main with SPARK_Mode is

   package My_Stack is

      type Stack (C : Natural) is private
      with
        Aggregate =>
          (Empty => Empty, Add_Unnamed => Push, Count_Discriminant => C);

      function Empty (C : Natural) return Stack;

      procedure Push (S : in out Stack; E : Integer);

   private

      type Int_Array is array (Positive range <>) of Integer;

      type Stack (C : Natural) is record
         Content : Int_Array (1 .. C);
         Top : Natural := 0;
      end record;

      function Empty (C : Natural) return Stack
      is (C, (1 .. C => 0), 0);

   end My_Stack;

   package body My_Stack is

      procedure Push (S : in out Stack; E : Integer) is
      begin
         S.Top := S.Top + 1;
         S.Content (S.Top) := E;
      end Push;

   end My_Stack;

begin
   null;
end Main;
