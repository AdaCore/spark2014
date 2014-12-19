package body Pre_Post_Exercise is

   function Is_Full return Boolean is
   begin
      return Stack_Pointer = Stack_Size;
   end Is_Full;

   procedure Initialize is
   begin
      Stack_Pointer := 0;
      Stack := (others => 0);
   end Initialize;

   procedure Push (X : in Integer) is
   begin
      Stack_Pointer := Stack_Pointer + 1;
      Stack (Stack_Pointer) := X;
   end Push;

   procedure Pop (X : out Integer) is
   begin
      X := Stack (Stack_Pointer);
      Stack_Pointer := Stack_Pointer - 1;
   end Pop;

end Pre_Post_Exercise;
