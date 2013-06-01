--  Implementation of the subprograms

package body ASM_Stack
is

   Stack_Size : constant := 100;
   type Stack_Range is range 0 .. Stack_Size;
   type Vector is array(Stack_Range range <>) of Integer;

   Stack_Vector : Vector (1 .. Stack_Size); --  anonymous type in unconstrained array
   Stack_Top : Stack_Range;

   function Is_Empty return Boolean
   is
   begin
      return Stack_Top = 0;
   end Is_Empty;

   function Is_Full return Boolean
   is
   begin
      return Stack_Top = Stack_Size;
   end;  -- the name will be generated

   procedure Clear
   is
   begin
      Stack_Top :=0;
      Stack_Vector := (others => 0); -- The aggregat must be qualified
   end Clear;

   procedure Push(X : in Integer)
   is
   begin
      if Is_Full  then
         raise Overflow;  -- raise exception
      end if;
      Stack_Top :=Stack_Top + 1;
      Stack_Vector(Stack_Top) := X;
   end Push;

   function Pop return Integer
   is
   begin
      if Is_Empty then
         raise Underflow;
      end if;
      Stack_Top := Stack_Top - 1;
      return Stack_Vector(Stack_Top + 1);
   end Pop;


--  In contrast to the ADT_Stack package the state is initialized
begin
   Stack_Top := 0;
   Stack_Vector := (others => 0); -- The aggregat must be qualified

end ASM_Stack;
