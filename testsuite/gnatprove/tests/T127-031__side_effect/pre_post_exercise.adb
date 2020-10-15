package body Pre_Post_Exercise with SPARK_Mode is

    --  Useful types

    Stack_Size : constant := 100;
    subtype Pointer_Range is Integer range 0 .. Stack_Size;
    subtype Stack_Range is Pointer_Range range 1 .. Stack_Size;

    --  Global data representing the stack

    Stack : Int_Arr (Stack_Range) := (others => 0);
    Stack_Pointer : Pointer_Range := 0;

    function Is_Full return Boolean is
      (Stack_Pointer = Stack_Size);
    function Is_Empty return Boolean is
       (Stack_Pointer = 0);
    procedure Push (X : Integer) is
    begin
       Stack_Pointer := Stack_Pointer + 1;
       Stack (Stack_Pointer) := X;
    end Push;
    procedure Pop (X : out Integer) is
    begin
       X := Stack (Stack_Pointer);
       Stack_Pointer := Stack_Pointer - 1;
    end Pop;

    function Model return Int_Arr is
      (Stack (1 .. Stack_Pointer));

end Pre_Post_Exercise;
